/// System related utilities such as read files etc.
/* Created 01/04/2024
*/
extern crate regex;

use regex::Regex;
use std::{
	process::{Stdio,Command},
	fs::{read_to_string,OpenOptions,remove_file,File,metadata},
	path::{Path},
	io::{Write,Read}
};
use project_root::{get_project_root};
use std::fs;

/// write sigs to dir where dir is relatively to the 
/// project root/data.
/// We assume contents are not large (and use in-efficient text write funcs)
pub fn write_sigs_to_dir(
	sigs: &Vec<String>, 
	dir: &str, 
	sigs_need_dfa: &Vec<String>,
	sigs_need_ised: &Vec<String>,
	sigs_need_ised_igc: &Vec<String>
){
	let rt = proj_root();
	let fnames = vec!["sigs.db", "needs_dfa.txt", 
		"needs_ised.txt", "needs_ised_igc.txt"];
	let v2d = vec![sigs, sigs_need_dfa, sigs_need_ised, sigs_need_ised_igc];
	for i in 0..fnames.len(){
		let filename= format!("{}/data/{}/{}", rt, dir, fnames[i]);
		write_to_file(&filename, &format!("# {}\n", fnames[i])); 
		for line in v2d[i]{
			append_to_file(&filename, &format!("{}\n",line));
		}
	}
}
/// return the absolute path of the project
pub fn proj_root()->String{
	match get_project_root(){
		Ok(p) => {
			let abspath = fs::canonicalize(&p);
			let res = abspath.expect("unable to extract proj path");
			res.into_os_string().into_string().expect("error in abspath")
		},
		Err(e) => panic!("ERROR: unable to retrieve project root: {}", e)
	}
}

/// create as new dir, the dir should ONLY be a file name.
/// the directory will be created under project_root/data/cache
pub fn create_new_cache_dir(dir: &str){
	//1. validate data
	let r1 = Regex::new(r"[0-9a-f_]+").unwrap();
	assert!(r1.is_match(dir), "INVALID dir: {}. Only alphanum allowed", dir);

	//2. create dir
	let abspath = format!("{}/data/cache/{}", &proj_root(), dir); 
	if file_exists(&abspath){
		fs::remove_dir_all(&abspath).
			expect(&format!("remove dir fails: {}", dir));
	}
	fs::create_dir_all(&abspath).expect(&format!("create dir fails: {}", abspath));
}

/// true if file exists
pub fn file_exists(fname: &str) -> bool{
	Path::new(fname).exists()
}

/// append a line to a file
pub fn append_to_file(fname: &str, line: &str){
    let mut fh = OpenOptions::new().append(true).open(fname)
		.expect(&format!("open {} failed", fname));
   	fh.write(line.as_bytes()).expect("write failed");
}

/// write a line to a file (erase contents if it exists)
pub fn write_to_file(fname: &str, line: &str){
	if Path::new(fname).exists(){
		remove_file(fname).unwrap();
	}
    let mut fh = OpenOptions::new().create_new(true).write(true).open(fname)
		.expect(&format!("open {} failed", fname));
	//write_all (not write): a single write() caps at ~2GiB on Linux
	//(0x7ffff000) and silently truncates large buffers (e.g. the
	//multi-GB DB cache vec_sigs/bundle_subsig), which .expect() does
	//not catch. write_all loops until every byte lands.
   	fh.write_all(line.as_bytes()).expect("write failed");
}

/// write a vector of lines to file
pub fn write_lines(fname: &str, lines: &Vec<String>, b_create_new: bool){
   let fpath = format!("{}/{}", &proj_root(), fname);
   let mut fh = if b_create_new{
   		if Path::new(&fpath).exists(){ remove_file(&fpath).unwrap(); }
        OpenOptions::new().create_new(true).write(true).open(&fpath)
        .expect(&format!("open {} failed", &fpath))
    }else{
        OpenOptions::new().write(true).append(true).open(&fpath)
        .expect(&format!("open {} failed", &fpath))
    };

	for line in lines{
   		fh.write((line.to_owned() + "\n").as_bytes()).expect("write failed");
	}
}

/// read all lines out 
pub fn read_lines(fpath: &str)->Vec<String>{
	let mut res = vec![];
	for line in  read_to_string(fpath).expect(&format!("ERROR in read: {}", fpath)).lines(){
        res.push(line.to_string())
    }
   	res 
}

/// read file in one string 
pub fn read(fpath: &str) -> String{
	read_to_string(fpath).expect(&format!("error in read file: {}", fpath))
}

/// read all binary contents and return as a hex string
pub fn read_nibbles(fpath: &str) -> Vec<u8>{
	//1. read the file
	let mut file = File::open(fpath).expect(
		&format!("can't open file: {}", fpath));
    let metadata = metadata(fpath).expect("unable to read");
	let size = metadata.len() as usize;
    let mut buffer = vec![0; size];
    file.read(&mut buffer).expect("buffer overflow");

	//2. collet string
	let mut vres = vec![];
	for num in buffer{
		vres.push(num/16);
		vres.push(num%16);
	}

	vres	
}



/// Print a one-shot machine + task banner to stdout. `s_task_desc`
/// names the computing task; when None, the launching command line
/// (/proc/self/cmdline) is used. Reports datetime, logical CPUs,
/// total/available RAM, CPU model + speed, and OS version. Linux
/// oriented (reads /proc, /etc/os-release); unreadable fields
/// degrade to "unknown".
pub fn print_computer_config(s_task_desc: Option<&str>){
	//1. task desc (fall back to the launching command line)
	let task = match s_task_desc{
		Some(s) => s.to_string(),
		None => {
			let raw = read_to_string("/proc/self/cmdline")
				.unwrap_or_default();
			let cmd = raw.split('\0')
				.filter(|s| !s.is_empty())
				.collect::<Vec<_>>().join(" ");
			if cmd.is_empty(){"unknown".to_string()} else {cmd}
		}
	};

	//2. date-time (shell `date`; epoch fallback)
	let now = Command::new("date")
		.arg("+%Y-%m-%d %H:%M:%S %Z")
		.output().ok()
		.and_then(|o| String::from_utf8(o.stdout).ok())
		.map(|s| s.trim().to_string())
		.filter(|s| !s.is_empty())
		.unwrap_or_else(|| {
			let secs = std::time::SystemTime::now()
				.duration_since(std::time::UNIX_EPOCH)
				.map(|d| d.as_secs()).unwrap_or(0);
			format!("epoch+{}s", secs)
		});

	//3. logical CPUs
	let cpus = std::thread::available_parallelism()
		.map(|n| n.get().to_string())
		.unwrap_or_else(|_| "unknown".to_string());

	//4. RAM from /proc/meminfo (kB -> GiB)
	let mi = read_to_string("/proc/meminfo").unwrap_or_default();
	let pick_kb = |key: &str| -> Option<f64> {
		mi.lines().find(|l| l.starts_with(key))
			.and_then(|l| l.split_whitespace().nth(1))
			.and_then(|v| v.parse::<f64>().ok())
	};
	let gib = |kb: Option<f64>| match kb{
		Some(v) => format!("{:.1} GiB", v/1024.0/1024.0),
		None => "unknown".to_string(),
	};
	let ram_total = gib(pick_kb("MemTotal:"));
	let ram_avail = gib(pick_kb("MemAvailable:"));

	//5. CPU model + speed from /proc/cpuinfo
	let ci = read_to_string("/proc/cpuinfo").unwrap_or_default();
	let pick_ci = |key: &str| -> String {
		ci.lines().find(|l| l.starts_with(key))
			.and_then(|l| l.split(':').nth(1))
			.map(|s| s.trim().to_string())
			.unwrap_or_else(|| "unknown".to_string())
	};
	let cpu_model = pick_ci("model name");
	let cpu_mhz = pick_ci("cpu MHz");

	//6. OS version: /etc/os-release + kernel release
	let osr = read_to_string("/etc/os-release").unwrap_or_default();
	let os_name = osr.lines()
		.find(|l| l.starts_with("PRETTY_NAME="))
		.and_then(|l| l.split('=').nth(1))
		.map(|s| s.trim_matches('"').to_string())
		.unwrap_or_else(|| "unknown".to_string());
	let kernel = read_to_string("/proc/sys/kernel/osrelease")
		.map(|s| s.trim().to_string())
		.unwrap_or_else(|_| "unknown".to_string());

	//7. emit one block (always printed, like rss_probe)
	let block = format!(
"========== computer config ==========\n\
task     : {}\n\
datetime : {}\n\
cpus     : {} logical\n\
ram      : {} total, {} available\n\
cpu      : {} @ {} MHz\n\
os       : {} (kernel {})\n\
=====================================",
		task, now, cpus, ram_total, ram_avail,
		cpu_model, cpu_mhz, os_name, kernel);
	crate::logger::emit_stdout(block);
}

/// check if s is a match of r by running perl.
/// NOTE: requires PERL installed
pub fn perl_is_match(r: &str, s: &str) -> bool{
	//1. write th efile
	let fname = "data/cache/to_remove.pl";
	let real_fname = format!("{}/{}", &proj_root(), fname);
	let prefix_s = if r.chars().next()==Some('^') 
		{"".to_string()} else {"^".to_string()};
	let suffix_s = if r.ends_with("$") {"".to_string()} else {"$".to_string()};
	let r = prefix_s + &r + &suffix_s;
	let lines = vec![
		format!("$s1 = \"{}\";", s),
		format!("print 'ok' if $s1 =~ /{}/;", r)
	];
	write_lines(fname, &lines, true);

	//2. run the perl and get the result
	let output = Command::new("perl")
		.arg(&real_fname)
		.stdout(Stdio::piped()).output().unwrap();
	let sout = String::from_utf8(output.stdout).unwrap();

	sout.contains("ok")
}

#[cfg(test)]
mod tests{
	use crate::os::{proj_root, create_new_cache_dir};

	#[test]
	fn test_proj_root(){
		let path = proj_root();
		assert!(path.contains("new_zkregplus"), "ERROR proj path: {}", path);
		create_new_cache_dir("dir1");
	}
}

