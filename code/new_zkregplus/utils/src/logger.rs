/// log related functions.
/*
	Created: 07/23/2024. Factored from os.rs of old zkreg project (01/04/2024)
*/

use crate::timer::Timer;
use crate::os::{append_to_file};



pub const ERR:usize = 0;
pub const WARN:usize = 1;
pub const LOG1:usize = 2;
pub const LOG2:usize = 3;
pub const LOG3:usize = 4;
pub const LOG4:usize = 5;
pub const LOG5:usize = 6;
pub const LOG6:usize = 7;
pub const LOG7:usize = 8;
/// current default log level for entire system
pub const LOG_LEVEL:usize = LOG6;

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
/// log function worker only if log_level is greater than or equal to LOG_LEVEL.
/// `job_id` is the id of the current job for parallel execution.
pub fn log(job_id: usize, log_level: usize, msg: &String){
	let b_write = false;
	let fpath = format!("./log_job_{}.txt", job_id);
	if log_level<=LOG_LEVEL{ 
		let indent_level = if log_level<2 {0} else {log_level-2};
		let indent_str = "-- ".repeat(indent_level);
		println!("[job {}] {}: {} {}", job_id, name_log_level(log_level), indent_str, msg); 
		if b_write{
			append_to_file(&fpath, &format!("{}: {}\n", 
				name_log_level(log_level), msg));
		}
	}
}

/// write all messages into an accumulator (acc).
/// `job_id` is the id of the current job for parallel execution.
pub fn flog(job_id: usize, log_level: usize, msg: &String, acc: &mut Vec<String>){
	if log_level<=LOG_LEVEL{ 
		let indent_level = if log_level<2 {0} else {log_level-2};
		let indent_str = "-- ".repeat(indent_level);
		println!("[job {}] {}: {} {}", job_id, name_log_level(log_level), indent_str, msg); 
		acc.push(msg.clone());
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

