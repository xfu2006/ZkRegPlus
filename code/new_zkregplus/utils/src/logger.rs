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
/// current default log level for entire system
pub const LOG_LEVEL:usize = LOG1;

/// convert from log level to its name
pub fn name_log_level(i: usize)->String{
	match i{
		ERR => String::from("ERR"),
		WARN => String::from("WARN"),
		LOG1=> String::from("LOG1"),
		LOG2=> String::from("LOG2"),
		LOG3=> String::from("LOG3"),
		_ => String::from("UNKNOWN")
	}
}
/// log function worker only if log_level is greater than or equal to LOG_LEVEL
pub fn log(log_level: usize, msg: &String){
	let b_write = false;
	let fpath = "./log.txt";
	if log_level<=LOG_LEVEL{ 
		println!("{}: {}", name_log_level(log_level), msg); 
		if b_write{
			append_to_file(fpath, &format!("{}: {}\n", 
				name_log_level(log_level), msg));
		}
	}
}

/// write all messages into an accumulator (acc)
pub fn flog(log_level: usize, msg: &String, acc: &mut Vec<String>){
	if log_level<=LOG_LEVEL{ 
		println!("{}", msg); 
		acc.push(msg.clone());
	}
}

/// log the performance.
pub fn log_perf(log_level: usize, log_title: &str, timer: &mut Timer){
	timer.stop();
	if timer.time_us()<1000{
		log(log_level, &format!("{} {} us", log_title, timer.time_us()));
	}else{
		log(log_level, &format!("{} {} ms", log_title, timer.time_us()/1000));
	}
	timer.clear_start();
}

/// log the performance into acc (vector of strings)
pub fn flog_perf(log_level: usize, log_title: &str, timer: &mut Timer, acc: &mut Vec<String>){
	timer.stop();
	if timer.time_us()<1000{
		flog(log_level, &format!("{} {} us", log_title, timer.time_us()), acc);
	}else{
		flog(log_level, &format!("{} {} ms", log_title, timer.time_us()/1000), acc);
	}
	timer.clear_start();
}

