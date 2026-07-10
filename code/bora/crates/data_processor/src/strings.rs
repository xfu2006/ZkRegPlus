/// Common utility functions related to strings

/*
 Created 01/04/2024
 Refactored 01/17/2024
 Revised: 06/11/2024: removed b_ignore logic to ACDFA
 Ported: 07/24/2024
*/

extern crate regex;
use regex::Regex;
use utils::logger::emit_stdout;

/// count how many times need appears in haystack
pub fn count_occ(needle: &str, haystack: &str)->usize{
	haystack.matches(needle).count()
}

/// validate if the given string follows rustomaton regex syntax
/// for the PM-reg
pub  fn validate_pm_regex(s: &str, pattern_name: &str){
	let r1 = Regex::new(r"^[abcdef0123456789().*?{},]+$").unwrap();
	let bres = r1.is_match(s);
	if !bres {emit_stdout(format!(
		"ERROR: not matching rustomaton for pm-regex: {}, signame: {}",
		s, pattern_name));}
	assert!(bres);
}

/// validate counter constraint
pub  fn validate_counter_constraint(s: &str, pattern_name: &str){
	let r1 = Regex::new(r"^\d+(>|=|<|==)\d+$").unwrap();
	let bres = r1.is_match(s);
	if !bres {emit_stdout(format!(
		"ERROR: not matching counter constraint: {}, signame: {}",
		s, pattern_name));}
	assert!(bres);
}

/// validate if the given string follows rustomaton regex syntax
pub  fn validate_ra_regex(s: &str, pattern_name: &str){
	let r1 = Regex::new(r"^[abcdef0123456789().|*?{},]+$").unwrap();
	let bres = r1.is_match(s);
	if !bres {emit_stdout(format!(
		"ERROR: not matching rustomaton regex: {}, signame: {}",
		s, pattern_name));}
	//assert!(bres);
}

/// validate if the given string follows rustomaton regex syntax
/// allow ! symbol it will be processed when generating automataon
pub  fn validate_ra_regex_relaxed(s: &str, pattern_name: &str){
	let r1 = Regex::new(r"^[abcdef0123456789().|*!?{},]+$").unwrap();
	let bres = r1.is_match(s);
	if !bres {emit_stdout(format!(
		"ERROR: not matching rustomaton regex: {}, signame: {}",
		s, pattern_name));}
	//assert!(bres);
}

/// tell if that the given string is good for quick processing 
pub fn is_sequential_regex(s: &str) -> bool{
	let r1 = Regex::new(r"^[abcdef0123456789.*?]+$").unwrap();
	r1.is_match(s)
}

/// find the first match of the sreg in haystack.
/// if not found, return 0
pub fn find_first_match(sreg: &str, haystack: &str) -> Option< (String, usize) >{
	let arr_str = find_all(sreg, haystack);
	if arr_str.len() == 0{
		None 
	}else{
		let subs = &arr_str[0];
		let pos = haystack.find( subs ).unwrap();
		Some( (arr_str[0].clone(), pos) )
	}
}

/// validate if it is a valid ClamavSig expr
pub  fn validate_expr(s: &str, pattern_name: &str){
	let r1 = Regex::new(r"^[0123456789()&|]+$").unwrap();
	let bres = r1.is_match(s);
	assert!(bres, "ERROR in expr: {}, signame: {}", s, pattern_name);
}

/// drop the last .*
pub fn drop_last_dotstar(s:&str)->String{
	if s.ends_with(".*"){s[0..s.len()-2].to_string()} else {String::from(s)}
}

/// return all matches
pub fn find_all(sreg: &str, haystack: &str)->Vec<String>{
	let r1 = Regex::new(sreg).unwrap();
	r1.find_iter(haystack).map(|m| m.as_str().to_string())
		.collect::<Vec<String>>()
}

/// find the first (if no match return ""), if there 
/// are MULTIPLE matches, abort
pub fn find_only(sreg: &str, haystack: &str)->String{
	let res = find_all(sreg, haystack);
	assert!(res.len()==1, "find_only failed on sreg: {}, haystack: {}, matches: {:?}", sreg, haystack, &res);
	res[0].clone()
}

/// check if haystack is a match of sreg
pub fn is_match(sreg: &str, haystack: &str)->bool{
	let re = Regex::new(sreg).expect("incorrect reg");
	re.is_match(haystack)
}

/// given a string extract all numbers
pub fn extract_nums(s: &str) -> Vec<usize>{
	let mut res = Vec::<usize>::new();
	for snum in find_all(r"\d+", s){res.push(snum.parse::<usize>().unwrap());}

	res
}

/// given a string extract all numbers in 2 hex format
pub fn extract_hex2(s: &str) -> Vec<usize>{
	let mut res = Vec::<usize>::new();
	for snum in find_all(r"[a-f0-9][a-f0-9]", s){res.push(usize::from_str_radix(&snum,16).unwrap());}

	res
}

/// Generate a wild match string between min and max.
/// Example, for min=3, max=5, the regex string is:
/// ....?.?
pub  fn dot_str(min:usize, max:usize)->String{
	if max<=usize::MAX-4000{
	 String::from(".".repeat(min)) + &String::from(".?".repeat(max-min))
	}else{
	 String::from(".".repeat(min)) + ".*"
	}
}

/// general the standard form of a range string of e.g. `{1,5}`
pub fn rng_str(min: usize, max: usize, b_add_dot: bool)->String{
	let res = if max>=(usize::MAX-1000)/2{//this implies it's infinite
		format!("{{{},}}", min)
	}else{
		format!("{{{},{}}}", min, max)
	};
	let res =if  b_add_dot {".".to_string() + &res} else {res};

	res
}


/// split by seprator
pub fn split(s: &str, sep: &str)->Vec<String>{
	s.split(&sep).map(str::to_string).collect::<Vec<String>>()
}

/// split a string into vector of 2-hex digits
pub fn chunks2(s: &str)->Vec<String>{
	let n:usize = s.len();
	let mut res:Vec<String> = vec![];
	for i in 0..n/2 {
		let (ch1, ch2) = (s.chars().nth(i*2).unwrap(), s.chars().nth(i*2+1).unwrap());
		let s = String::from(ch1) + &String::from(ch2);
		res.push(s);
	}

	res
}

///return the wide version of char,
///e.g., 41 --> 4100 (simply append 00).
///assumming len of s is 2
pub fn wide(s: &str)->String{
	assert!(s.len()==2, "s.len should be 2, s: {}", s);
	String::from(s) + &String::from("00")
}
	

/// if s (e.g., 41) falls in [a-zA-Z]
pub fn is_english(s: &str) -> bool{
	let hval_opt= usize::from_str_radix(s, 16);
	match hval_opt{
		Ok(hval) => 
			(hval>=0x41 && hval<=0x5a) || (hval>=0x61 && hval<=0x7a),
		Err(_) => false
	}
}

/// return regex which is non-alpha numeric
pub fn regex_non_alphanum()->String{
	let mut s = String::from("(00");

	for i in 1..127{
		if !((i>=0x41 && i<=0x51) || (i>=0x61 && i<=0x71) 
			|| (i>=0x30 && i<=0x39)){
			s = s + "|" + &format!("{:#04x}", i)[2..];
		}
	}
	s.push(')');

	s
}


