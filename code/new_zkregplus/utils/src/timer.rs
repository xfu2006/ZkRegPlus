/// Timer object: for measure elapsed time
/*
	Created: 07/23/2024. Factored from os.rs of old zkreg project (01/04/2024)
*/

use std::time::Instant;

/// timer class for recording time in microseconds
pub struct Timer{
	///running time in micro-second (accumulated)
	time_us: usize,

	/// the time timer starts
	start_time: Instant,
}

/// timer class for recording time in microseconds
impl Timer{
	/// return the elapsed time in micro-seconds.
	pub fn time_us(&self) -> usize{
		self.time_us
	}

	/// constructor
	pub fn new() -> Timer{
		return Timer{time_us: 0, start_time: Instant::now()};
	}

	/// start recording
	pub fn start(&mut self){
		self.start_time = Instant::now();
	}

	/// clear start time and also elapsed time
	pub fn clear_start(&mut self){
		self.time_us = 0;
		self.start_time = Instant::now();
	}

	/// stop the timer and accumulates the time
	pub fn stop(&mut self){
		self.time_us += self.start_time.elapsed().as_micros() as usize;
	}

	/// clear elapsed time.
	pub fn clear(&mut self){
		self.time_us = 0;
	}

	/// get the elapsed time in milli-seconds.
	pub fn ms(&self) -> usize{
		self.time_us/1000
	}
}
