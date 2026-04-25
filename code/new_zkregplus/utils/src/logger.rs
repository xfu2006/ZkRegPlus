/// log related functions.
/*
	Created: 07/23/2024. Factored from os.rs of old zkreg project (01/04/2024)
*/

use crate::timer::Timer;
use crate::os::{append_to_file, file_exists, proj_root};
use std::fs::{self, File};
use std::path::Path;
use std::sync::{OnceLock, Mutex};
use std::collections::HashSet;

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

pub fn initialized_jobs() -> &'static Mutex<HashSet<usize>> {
    static INITIALIZED_JOBS: OnceLock<Mutex<HashSet<usize>>> = OnceLock::new();
    INITIALIZED_JOBS.get_or_init(|| Mutex::new(HashSet::new()))
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

/// ensure the log file exists. First-touch behavior depends on b_resume:
/// - b_resume == false: overwrite (remove + recreate blank) on first touch.
/// - b_resume == true : preserve existing contents; only create if missing.
/// Also ensures the parent directory exists.
pub fn ensure_log_file(job_id: usize, fpath: &str){
    if let Some(parent) = Path::new(fpath).parent() {
        fs::create_dir_all(parent).expect(&format!(
            "Unable to create log dir: {}", parent.display()));
    }
    let b_resume = read_global_config().b_resume;
    let mut init_jobs = initialized_jobs().lock().unwrap();
    if !init_jobs.contains(&job_id) {
        if !b_resume && file_exists(fpath) {
            std::fs::remove_file(fpath).unwrap_or_else(|_| ());
        }
        if !file_exists(fpath) {
            File::create(fpath).expect(&format!(
                "Unable to create log file: {}", fpath));
        }
        init_jobs.insert(job_id);
    } else if !file_exists(fpath) {
        File::create(fpath).expect(&format!(
            "Unable to create log file: {}", fpath));
    }
}

/// log function worker only if log_level is greater than or equal to LOG_LEVEL.
/// `job_id` is the id of the current job for parallel execution.
pub fn log(job_id: usize, log_level: usize, msg: &String){
	let b_write = true;
	let fpath = format!("{}/data/cache/logs/log_job_{}.txt",
		proj_root(), job_id);
	if log_level<=read_global_config().log_level{ 
		let indent_level = if log_level<2 {0} else {log_level-2};
		let indent_str = "-- ".repeat(indent_level);
		println!("[job {}] {}: {} {}", job_id, name_log_level(log_level), indent_str, msg); 
		if b_write{
			ensure_log_file(job_id, &fpath);
			append_to_file(&fpath, &format!("[job {}] {}: {} {}\n", 
				job_id, name_log_level(log_level), indent_str, msg));
		}
	}
}

/// write all messages into an accumulator (acc).
/// `job_id` is the id of the current job for parallel execution.
pub fn flog(job_id: usize, log_level: usize, msg: &String, acc: &mut Vec<String>){
	if log_level<=read_global_config().log_level{ 
		let indent_level = if log_level<2 {0} else {log_level-2};
		let indent_str = "-- ".repeat(indent_level);
		println!("[job {}] {}: {} {}", job_id, name_log_level(log_level), indent_str, msg); 
		acc.push(format!("[job {}] {}: {} {}", job_id, name_log_level(log_level), indent_str, msg));
	}
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

