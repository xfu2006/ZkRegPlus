/// log related functions.
/*
	Created: 07/23/2024. Factored from os.rs of old zkreg project (01/04/2024)
*/

use crate::timer::Timer;
use crate::os::proj_root;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::Path;
use std::sync::{Arc, Mutex, OnceLock, RwLock};
use std::sync::mpsc::{channel, sync_channel, Sender, SyncSender};
use std::collections::HashMap;

use crate::consts::read_global_config;

pub const ERR:usize = 0;
pub const WARN:usize = 1;
pub const LOG1:usize = 2;
pub const LOG2:usize = 3;
pub const LOG3:usize = 4;
pub const LOG4:usize = 5;
pub const LOG5:usize = 6;
pub const LOG6:usize = 7;
pub const LOG7:usize = 8;

/// Messages on the stdout drainer's channel. `Line` is a normal log
/// line; `Flush` is a fence — the drainer writes everything queued
/// before it, flushes the stdout buffer, then acks. `flush_logger()`
/// uses this to ensure prior log lines are durably on stdout before
/// it returns.
enum LogMsg {
	Line(String),
	Flush(SyncSender<()>),
}

/// Background stdout drainer. One thread owns the only `Stdout` lock
/// for the process lifetime; prover threads enqueue formatted lines
/// into this MPSC and return immediately. A stuck stdout (full disk,
/// NFS hang, slow tty) parks only the drainer — never the prover
/// threads. Unbounded on purpose: under a healthy drainer the queue
/// stays near-empty; under a stuck drainer we'd be in trouble anyway
/// (memory pressure surfaces long before queued strings matter).
fn stdout_tx() -> &'static Sender<LogMsg> {
	static TX: OnceLock<Sender<LogMsg>> = OnceLock::new();
	TX.get_or_init(|| {
		let (tx, rx) = channel::<LogMsg>();
		std::thread::Builder::new()
			.name("logger-stdout".into())
			.spawn(move || {
				// IMPORTANT: take the stdout lock ONLY while writing,
				// then drop it before going back to recv(). Holding
				// it across recv() would block every direct println!
				// / print! / DEBUG-USE call elsewhere in the codebase
				// (Stdout uses a process-wide ReentrantMutex).
				while let Ok(msg) = rx.recv() {
					match msg {
						LogMsg::Line(line) => {
							let stdout = std::io::stdout();
							let mut out = stdout.lock();
							let _ = out.write_all(line.as_bytes());
							let _ = out.write_all(b"\n");
						}
						LogMsg::Flush(ack) => {
							{
								let stdout = std::io::stdout();
								let mut out = stdout.lock();
								let _ = out.flush();
							}
							let _ = ack.send(());
						}
					}
				}
			})
			.expect("spawn logger-stdout thread");
		tx
	})
}

/// Hand a line to the background drainer. Move-by-value, no clone.
/// If the drainer thread is gone the line is dropped silently.
/// Public so callers across the workspace can replace raw `println!`
/// in prover-path code without taking the global `Stdout` mutex.
pub fn emit_stdout(line: String) {
	let _ = stdout_tx().send(LogMsg::Line(line));
}

/// Block until the drainer has written every line enqueued so far
/// and flushed stdout. Safe to call from any thread; re-entrant
/// across multiple call sites. A best-effort fence — if the drainer
/// is gone the call returns immediately without error.
pub fn flush_logger() {
	let (ack_tx, ack_rx) = sync_channel::<()>(1);
	if stdout_tx().send(LogMsg::Flush(ack_tx)).is_ok() {
		let _ = ack_rx.recv();
	}
}

/// Per-job log file cache. Each entry is an `Arc<Mutex<File>>` opened
/// once in append mode and reused for the rest of the process. The
/// outer `RwLock` serializes only HashMap reads/inserts — it is NEVER
/// held across any filesystem syscall (open, create_dir_all,
/// remove_file, write). This kills the convoy that the old
/// `initialized_jobs` mutex created across slow I/O.
type JobLog = Arc<Mutex<File>>;

fn job_log_cache() -> &'static RwLock<HashMap<usize, JobLog>> {
	static C: OnceLock<RwLock<HashMap<usize, JobLog>>> = OnceLock::new();
	C.get_or_init(|| RwLock::new(HashMap::new()))
}

/// Return a cloned `Arc` to the job's append-mode `File`, opening it
/// on first touch. Returns `None` if the file cannot be opened — the
/// caller treats that as "drop this line" rather than panicking, so
/// a stuck/failed FS can never propagate up into the prover.
fn get_job_log(job_id: usize) -> Option<JobLog> {
	// Fast path: shared read lock, no syscall.
	if let Ok(map) = job_log_cache().read() {
		if let Some(w) = map.get(&job_id) {
			return Some(Arc::clone(w));
		}
	}
	// Slow path: build the path and open the file with NO cache lock
	// held. Snapshot `b_resume` into a local so the config guard is
	// dropped before any I/O.
	let fpath = format!("{}/data/cache/logs/log_job_{}.txt",
		proj_root(), job_id);
	if let Some(parent) = Path::new(&fpath).parent() {
		let _ = fs::create_dir_all(parent);
	}
	let b_resume = read_global_config().b_resume;
	if !b_resume {
		let _ = fs::remove_file(&fpath); // ignore ENOENT
	}
	let file = OpenOptions::new()
		.create(true).append(true).open(&fpath).ok()?;
	let new_writer: JobLog = Arc::new(Mutex::new(file));

	// Cache it. If a racing thread inserted first, keep theirs.
	let mut w = job_log_cache().write().ok()?;
	Some(Arc::clone(w.entry(job_id).or_insert(new_writer)))
}

/// convert from log level to its name
pub fn name_log_level(i: usize)->String{
	match i{
		ERR => String::from("ERR"),
		WARN => String::from("WARN"),
		LOG1=> String::from("LOG1"),
		LOG2=> String::from("LOG2"),
		LOG3=> String::from("LOG3"),
		LOG4=> String::from("LOG4"),
		LOG5=> String::from("LOG5"),
		LOG6=> String::from("LOG6"),
		LOG7=> String::from("LOG7"),
		_ => String::from("UNKNOWN")
	}
}

/// log function worker only if log_level is greater than or equal to
/// LOG_LEVEL. `job_id` is the id of the current job for parallel
/// execution. Both stdout and the per-job file write are best-effort:
/// I/O errors are swallowed so a stuck/failed write can never block
/// or panic the prover.
pub fn log(job_id: usize, log_level: usize, msg: &String){
	// Snapshot config into a local so the read guard dies before I/O.
	let global_lvl = read_global_config().log_level;
	if log_level > global_lvl { return; }

	let indent_level = if log_level<2 {0} else {log_level-2};
	let indent_str = "-- ".repeat(indent_level);
	let line = format!("[job {}] {}: {} {}",
		job_id, name_log_level(log_level), indent_str, msg);

	// Per-job file FIRST so a crash still has the freshest line on
	// disk. The per-job mutex only serializes lines for the same job.
	if let Some(arc) = get_job_log(job_id) {
		if let Ok(mut f) = arc.lock() {
			let _ = writeln!(f, "{}", line);
		}
	}
	// Stdout via background drainer — moves the String, no clone,
	// never blocks on I/O.
	emit_stdout(line);
}

/// write all messages into an accumulator (acc).
/// `job_id` is the id of the current job for parallel execution.
pub fn flog(job_id: usize, log_level: usize, msg: &String, acc: &mut Vec<String>){
	let global_lvl = read_global_config().log_level;
	if log_level > global_lvl { return; }
	let indent_level = if log_level<2 {0} else {log_level-2};
	let indent_str = "-- ".repeat(indent_level);
	let line = format!("[job {}] {}: {} {}",
		job_id, name_log_level(log_level), indent_str, msg);
	acc.push(line.clone());      // acc keeps a copy
	emit_stdout(line);            // drainer takes ownership
}

/// log the performance.
/// `job_id` is the id of the current job for parallel execution.
pub fn log_perf(job_id: usize, log_level: usize, log_title: &str, timer: &mut Timer){
	timer.stop();
	if timer.time_ns()<1000{
		log(job_id, log_level, &format!("{} {} ns", log_title, timer.time_ns()));
	}else if timer.time_us()<1000{
		log(job_id, log_level, &format!("{} {} us", log_title, timer.time_us()));
	}else{
		log(job_id, log_level, &format!("{} {} ms", log_title, timer.time_us()/1000));
	}
	timer.clear_start();
}

/// log the performance into acc (vector of strings).
/// `job_id` is the id of the current job for parallel execution.
pub fn flog_perf(job_id: usize, log_level: usize, log_title: &str, timer: &mut Timer, acc: &mut Vec<String>){
	timer.stop();
	if timer.time_us()<1000{
		flog(job_id, log_level, &format!("{} {} us", log_title, timer.time_us()), acc);
	}else{
		flog(job_id, log_level, &format!("{} {} ms", log_title, timer.time_us()/1000), acc);
	}
	timer.clear_start();
}

