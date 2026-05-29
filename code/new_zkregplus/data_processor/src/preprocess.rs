/// Collections of preprocessing functions for handling decorators
/// and modifiers of Clamav Signatures.

/* Created: 06/14/2024
	Ported: 07/24/2024
*/

extern crate regex;

use std::cmp::Ordering::{Less,Equal,Greater};
use std::collections::{HashMap};
use regex::Regex;
use crate::{
	strings::{dot_str,rng_str,chunks2,is_english,find_all,regex_non_alphanum,wide},
	fsa_utils::{build_dfa},
};
use utils::{
	data::{hex_to_u8,u8_to_hex},
};
use rustomaton::{regex::{ToRegex}};

/// handle {num-num} related forms, normalize to the accepted forms
pub fn handle_range(s:&str)->String{
	//1. collect (min,max) tuples (note: each number means bytes, should
	// multiple with 2)
	let s = &s.replace("{0-}",".*");
	let mut vt = vec![];
	let r1 = Regex::new(r"\{(\d+)-(\d+)\}").unwrap();
	for (_,[min, max]) in r1.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}
	let r2 = Regex::new(r"\{-(\d+)\}").unwrap();
	for (_,[max]) in r2.captures_iter(s).map(|c| c.extract()){
		vt.push((0, max.parse::<usize>().unwrap()));
	}
	let r3 = Regex::new(r"\{(\d+)\}").unwrap();
	for (_,[max]) in r3.captures_iter(s).map(|c| c.extract()){
		vt.push((max.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}
	let r4 = Regex::new(r"\{(\d+)-\}").unwrap();
	for (_,[min]) in r4.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), (usize::MAX-1000)/2));
	}
	//NOTE: bugzilla 776 disappeared and there is NO explaination
	//of the bracket (we treat it like wild match of min to max chars)
	let r5 = Regex::new(r"\[(\d+)-(\d+)\]").unwrap();
	for (_,[min,max]) in r5.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}

	//2. handle the replacement
	let mut s2 = String::from(s);
	for (min,max) in vt.clone(){
		let (min2, max2) = (min * 2, max*2);
		if min==max{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "}"), &dot_str(min2, max2));
			s2 = s2.replace(&("[".to_string() + &max.to_string() + "-" + &max.to_string() + "]"), &dot_str(min2, max2));
		}else if min==0{
			s2 = s2.replace(&("{-".to_string() + &max.to_string() + "}"), &dot_str(min2, max2));
			s2 = s2.replace(&("{0-".to_string() + &max.to_string() + "}"), &dot_str(min2, max2));
			s2 = s2.replace(&("[0-".to_string() + &max.to_string() + "]"), &dot_str(min2, max2));
		}else if max2>=usize::MAX-4000{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "-}"), &dot_str(min2, max2));
		}else{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "-" + &max.to_string() + "}"), &dot_str(min2, max2));
			s2 = s2.replace(&("[".to_string() + &min.to_string() + "-" + &max.to_string() + "]"), &dot_str(min2, max2));
		}
	}

	s2
}

/// handle {num-num} related forms,
/// but without approximation with dotstring (this function
/// is used to feed to string to parser
/// e.g., `{2-4}` is tranted to `{4,8}` 
/// (because to bytes to hex nibbles multiply 2)
/// `{2-}` is tranted to `{4,}`, i.e., 4 to infinite
/// if b_add_dot is set to true, the "." is appended to 
/// BEFORE the `{num1, num2}`
pub fn handle_range_without_approx(s:&str, b_add_dot: bool)->String{
	//1. collect (min,max) tuples (note: each number means bytes, should
	// multiple with 2)
	let s = &s.replace("{0-}",".*");
	let mut vt = vec![];
	let r1 = Regex::new(r"\{(\d+)-(\d+)\}").unwrap();
	for (_,[min, max]) in r1.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}
	let r2 = Regex::new(r"\{-(\d+)\}").unwrap();
	for (_,[max]) in r2.captures_iter(s).map(|c| c.extract()){
		vt.push((0, max.parse::<usize>().unwrap()));
	}
	let r3 = Regex::new(r"\{(\d+)\}").unwrap();
	for (_,[max]) in r3.captures_iter(s).map(|c| c.extract()){
		vt.push((max.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}
	let r4 = Regex::new(r"\{(\d+)-\}").unwrap();
	for (_,[min]) in r4.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), (usize::MAX-1000)/2));
	}
	//NOTE: bugzilla 776 disappeared and there is NO explaination
	//of the bracket (we treat it like wild match of min to max chars)
	let r5 = Regex::new(r"\[(\d+)-(\d+)\]").unwrap();
	for (_,[min,max]) in r5.captures_iter(s).map(|c| c.extract()){
		vt.push((min.parse::<usize>().unwrap(), max.parse::<usize>().unwrap()));
	}

	//2. handle the replacement
	let mut s2 = String::from(s);
	for (min,max) in vt.clone(){
		let (min2, max2) = (min * 2, max*2);
		if min==max{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "}"), &rng_str(min2, max2, b_add_dot));
			s2 = s2.replace(&("[".to_string() + &max.to_string() + "-" + &max.to_string() + "]"), &rng_str(min2, max2, b_add_dot));
		}else if min==0{
			s2 = s2.replace(&("{-".to_string() + &max.to_string() + "}"), &rng_str(min2, max2, b_add_dot));
			s2 = s2.replace(&("{0-".to_string() + &max.to_string() + "}"), &rng_str(min2, max2, b_add_dot));
			s2 = s2.replace(&("[0-".to_string() + &max.to_string() + "]"), &rng_str(min2, max2, b_add_dot));
		}else if max2>=usize::MAX-4000{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "-}"), &rng_str(min2, max2, b_add_dot));
		}else{
			s2 = s2.replace(&("{".to_string() + &min.to_string() + "-" + &max.to_string() + "}"), &rng_str(min2, max2, b_add_dot));
			s2 = s2.replace(&("[".to_string() + &min.to_string() + "-" + &max.to_string() + "]"), &rng_str(min2, max2, b_add_dot));
		}
	}

	s2
}

/// assuming length even, convert to ignore case form
/// e.g.,  "61" to "(61|41)" 
pub fn to_ignore_case(s: &str)->String{
	assert!(s.len()%2==0, "s length has to be even! s: {}", s);
	let chunks = chunks2(s);
	let mut res = "".to_string();
	for x in chunks{
		let nextx = if is_english(&x){ "(".to_string() + &x + "|" + &other_case(&x) +")" } else {x};
		res = res + &nextx;
	}
	res
}

/// return the other case of s
/// if s not English alphabet, return itself 
pub fn other_case(s: &str) -> String{
	assert!(s.len()==2, "s.len should be 2");
	let hval= usize::from_str_radix(s, 16).unwrap();
	if hval>=0x41 && hval<=0x5a{
		format!("{:#04x}", 0x61+ hval-0x41)[2..].to_string()
	}else if hval>=0x61 && hval<=0x7a{
		format!("{:#04x}", 0x41+ hval-0x61)[2..].to_string() 
	}else{
		String::from(s)	
	}
}

/// find the triggers for PCRE, recursively. Because trigger themselves 
/// might have dependency on triggers
pub fn recursive_triggers(i: usize, triggers: &Vec<String>) -> String{
	if i>=triggers.len() {return format!("{}",i);}

	let mut tri = triggers[i].clone();
	//if it has relation like (1>0)&2&3
	//for engineering convenience, we do not handle it recursively.
	//just return as it is
	if find_all(r"<|>|=", &tri).len()>0{
		let re = Regex::new(r"[><=]\d+").unwrap();
		let tri_no_rel = re.replace_all(&tri, ""); 
		let arr_trigs = find_all(r"[0-9]+", &tri_no_rel);
		for x in arr_trigs{	
			let j = x.parse::<usize>().unwrap();
			assert!(triggers.len()<=j || triggers[j].len()==0, "we cannot handle the trigger recursively for j: {}", j);
		}
		return tri;
	}

	//now handle it recursively
	let mut arr_trigs = find_all(r"[0-9]+", &tri);
	if arr_trigs.len()==0{ 
		tri = format!("{}", i);
		return tri;
	}

	//handle recursively LONGER first so longer gets processed first
	arr_trigs.sort_by(|a,b| if b.len()>a.len() {Greater} else if b.len()==a.len() {Equal} else {Less});
	for x in arr_trigs{
		let j = x.parse::<usize>()
			.expect(&format!("ERROR parsing x as int: {}",x));
		let s = recursive_triggers(j, triggers);
		let news = if s==format!("{}", j) {s.clone()} 
			else {format!("({})&{}", s, j)};
		tri = tri.replace(&x, &news);
	}
	tri
}

/// replace in "s" the appearance of i by the intersection
/// of its trigger and itself
pub fn plug_in_trigger(i: usize, s: &str, trigger: &str)->String{
	if trigger.len()==0 || trigger==format!("{}",i) {return s.to_string();}
	let mut s = s.to_string();

	//1. protect all relations (right end)
	let mut hs = HashMap::<String,String>::new();
	let reps = vec!["a", "b", "c", "d", "e", "f", "g", "h", "i"];
	let reps2 = vec!["A", "B", "C", "D", "E", "F", "G", "H", "I"];
	let rels = find_all(r"(>|=|<)[0-9]+", &s);
	for i in 0..rels.len(){ 
		s = s.replace(&rels[i], reps[i]);
		hs.insert(reps[i].to_string(), rels[i].to_string());
	}

	//2. protect all numbers which has i as substring e.g., 25 vs 2
	//there might be cases like 2>5
	let longs = find_all(&format!("({}[0-9]+|[0-9]+{})", i, i), &s);
	assert!(longs.len()<reps2.len(), "INCREASE reps2 len!");
	for i in 0..longs.len(){
		s = s.replace(&longs[i], reps2[i]);
		hs.insert(reps2[i].to_string(), longs[i].to_string());
	}

	//3. now do the replacement
	//let pat_occ = find_all(
	//	&format!("{}((>|=|<)[0-9a-zA-Z]+)?", i), &s);
	let self_s = format!("{}",i);
	s = if self_s==trigger {s}
		else{s.replace(&format!("{}", i), &format!("({})&{}", trigger, i))};

	//4. recover everything
	if hs.len()>0{
		for (k,v) in &hs{
			s = s.replace(k, v);
		}
	}

	s
}

/// apply modifiers (no need to apply b_ignore - 
/// it will be handled by automaton)
pub fn gen_modified_str(arr: &Vec<String>, b_wide: bool, _b_ignore: bool, 
	b_full: bool)->String{
	let mut s = String::from("");
	//1. apply b_ignore
	for x in arr{
		let s1 = if b_wide {wide(&x)} else {x.clone()};
		s = s + &s1;
		/* NO NEED to handle b_ignore any more. We'll handle it in ACDFA
		if b_ignore && is_english(x){
			let s2 = if b_wide {wide(&other_case(&x))} else {other_case(&x)};
			s = s + "(" + &s1 + "|" + &s2 +")";
		}else{
		}
		*/
	}
	//2. apply b_full
	if b_full{
		s = s + &regex_non_alphanum();
	}

	s
}

/// handle signature modifiers [i - ignore case, w - wide char, f - full word,
/// a - ascii]; NOTE PM-supports limited modifiers: 
/// it does not support "f" - fullword, and it does not more than 2 
/// modifiers combined.
/// boolean indicate if it's case sensitive (this can be handled by ac-dfa).
pub fn handle_modifier_for_pm(s:&str)->(String,bool){
	if !s.contains("::") {return (String::from(s), true);}
	let arr = s.split("::").map(str::to_string).collect::<Vec<String>>();
	let mods = &arr[1];
	if mods.len()>2{panic!("handle_modifier_for_pm does not support more than 2 modifiers: {}", &mods);}

	let b_w = mods.contains("w"); //wide char mode
	let b_i = mods.contains("i"); //ignore case
	let b_a = mods.contains("a"); //ascii mode
	let b_f = mods.contains("f"); //full word mode
	if b_f {panic!("PM-reg does not support full mode");}
	if b_a && b_w{panic!("PM-reg does not support both a and w mode. Make two sigs instead");}

	let chunks = chunks2(&arr[0]);
	let mut final_str = String::from(&arr[0]);
	if b_w{
		final_str = String::from("");
		for x in chunks{
			final_str = final_str + &wide(&x);
		}
	}
	(final_str, !b_i)
}

/// re-write but do not rewrite ignore case (will be handled later
/// in hir in DFA construction
pub fn handle_modifier_but_no_igc(s:&str)->(String, bool){
	handle_modifier_worker(s, false)
}

/// handle signature modifiers [i - ignore case, w - wide char, f - full word,
/// a - ascii], return (string, b_case_sensitive)
pub fn handle_modifier(s:&str)->(String, bool){
	handle_modifier_worker(s, true)
}

/// worker function called by hanlde_modifier
pub fn handle_modifier_worker(s:&str, handle_igc: bool)->(String, bool){
	if !s.contains("::") {return (String::from(s), true);}
	let arr = s.split("::").map(str::to_string).collect::<Vec<String>>();
	let mods = &arr[1];
	let chunks = chunks2(&arr[0]);
	let b_w = mods.contains("w"); //wide char mode
	let b_i = mods.contains("i"); //ignore case
	let b_a = mods.contains("a"); //ascii mode
	let b_f = mods.contains("f"); //full word mode

	let final_str;
	if b_a && b_w{//both
		let s1 = gen_modified_str(&chunks, true, b_i && handle_igc, b_f);
		let s2 = gen_modified_str(&chunks, false, b_i && handle_igc, b_f);

		final_str = "(".to_owned() + &s1 + "|"  + &s2 + ")"
	}else{//otherwise, only one string (depending on if wide)
		final_str= gen_modified_str(&chunks, b_w, b_i && handle_igc, b_f)	
	};
	(final_str, !b_i)
}

/// This function handles the location specifiers as defined in
/// extended signature format: <https://docs.clamav.net/manual/Signatures/ExtendedSignatures.html>.
/// E.g., 5:aabb (starting at index 5).
/// Some specifications are approximated (e.g., EP+5) to .*.....
/// As there are no way to search for entry point (by parsing executable)
/// using regex.
/// Note that this function now appends .* around the word pattern
/// e.g., "abc" is converted to `".*abc.*"`
pub fn handle_location(s:&str)->String{
	let parts:Vec<String> = s.split(":").map(str::to_string).collect();
	//1. no loc string
	if parts.len()==1{ return String::from(".*") + s + ".*"; }

	//2. format "5:abc"
	let res;
	assert!(parts.len()==2, "parts.len!=2. Details: {:?}", &parts);
	let pattern = &parts[1];
	let loc = &parts[0].to_lowercase();
	if Regex::new(r"^[0-9]+$").unwrap().is_match(loc){
		let num = loc.parse::<usize>().unwrap();
		//offset is in nibble units -> emit symbolic `.{num,num}`
		//(NOT num*2) so it stays a single Repetition node. Avoids
		//materializing `num` literal dots (O(num) host cost).
		res = rng_str(num, num, true) + pattern + ".*";
	}
	//2.5 format "num1,num2"
	else if Regex::new(r"^[0-9]+,[0-9]+$").unwrap().is_match(loc){
		let arr = loc.split(",").map(str::to_string).collect::<Vec<String>>();
		let min = arr[0].parse::<usize>().unwrap();
		let max = arr[1].parse::<usize>().unwrap();
		let (min,max) = if min<max {(min,max)} else {(max,min)};
		//nibble units -> symbolic `.{min,max}` (NOT *2), see above.
		res = rng_str(min, max, true) + pattern + ".*";
	}
	//3. "*"
	else if loc.contains("*"){
		res = ".*".to_string() + pattern + ".*";
	}
	//4. "ep+n" case (APPROXIMATED) and "exp+min,max" case
	else if loc.contains("ep+"){
		let mut dotstr = String::from("");
		let num_str = &loc[3..];
		if num_str.contains(","){
			let arr = num_str.split(",").map(str::to_string).collect::<Vec<String>>();
			let min = arr[0].parse::<usize>().unwrap();
			let max = arr[1].parse::<usize>().unwrap();
			dotstr = dotstr + &dot_str(min,max);
		}else{
			let n = num_str.parse::<usize>().unwrap();
			dotstr = dotstr + &dot_str(n,n);
		}
		res = ".*".to_owned() + &dotstr + pattern + ".*";
	//5. ep-n, SL+x, SL-x, SE+x, SE-x, vi cases (APPROXIMATED)
	//as no way to identify section offsetset using regex only
	//NOTE: not sure about "vi", not found in documentation there is no offset.
	}else if loc.contains("ep") || loc.contains("s") || loc.contains("vi"){
		res = ".*".to_owned() + pattern + ".*";
	//6. eof-n case
	}else if loc.contains("eof-"){
		let n = loc[4..].parse::<usize>().unwrap();
		if 2*n<pattern.len(){
			//log(WARN, &format!("parsing eof error n<pattern.len(): n: {}, len: {}, s: {}. Most likely caused by ! operators", n, pattern.len(), s));
		}
		let ndiff = if 2*n > pattern.len() {2*n-pattern.len()} else {0};
		res = ".*".to_owned() + pattern + &".".repeat(ndiff);
	}else{
		panic!("Unhandled case: s: {}", s);
		//res = String::from("ERROR");
	}	

	res
}

/// only allow \d+ or *
pub fn handle_location_for_pm(s:&str)->String{
	let parts:Vec<String> = s.split(":").map(str::to_string).collect();
	//1. no loc string
	if parts.len()==1{ return String::from(".*") + s + ".*"; }

	//2. format "5:abc"
	let res;
	assert!(parts.len()==2, "parts.len!=2. Details: parts: {:?}, s: {}", &parts, &s);
	let pattern = &parts[1];
	let loc = &parts[0].to_lowercase();
	if Regex::new(r"^[0-9]+$").unwrap().is_match(loc){
		let num = loc.parse::<usize>().unwrap();
		//nibble units -> symbolic `.{num,num}` (NOT num*2), see
		//handle_location: avoids materializing `num` literal dots.
		res = rng_str(num, num, true) + pattern + ".*";
	}
	//2.5 format "num1,num2"
	else if Regex::new(r"^[0-9]+,[0-9]+$").unwrap().is_match(loc){
		let arr = loc.split(",").map(str::to_string).collect::<Vec<String>>();
		let min = arr[0].parse::<usize>().unwrap();
		let max = arr[1].parse::<usize>().unwrap();
		let (min,max) = if min<max {(min,max)} else {(max,min)};
		//nibble units -> symbolic `.{min,max}` (NOT *2), see above.
		res = rng_str(min, max, true) + pattern + ".*";
	}
	//3. "*"
	else if loc.contains("*"){
		res = ".*".to_string() + pattern + ".*";
	}else{
		panic!("Unhandled case: s: {}", s);
		//res = String::from("ERROR");
	}

	res
}

/// e.g., enum_all_except(vec![0, 1]) returns
/// "(02|03|...|ff)"
pub fn enum_all_except(vbytes: &Vec<usize>) -> String{
	//1. convert
	let mut res = vec![];
	for x in 0..256{
		if ! vbytes.contains(&x){
			res.push(x);
		}
	}

	//2. generate the string
	let mut id = 0;
	let mut s = String::from("(");
	for x in res{
		let sx = format!("{:#04x}", x)[2..].to_string(); 
		if id==0{
			s  = s + &sx;	
		}else{
			s = s + "|" + &sx;
		}
		id += 1;
	}
	s = s + ")";
	return s;
}

/// for !(112233) like string, too long to enumerate all combinations.
/// Convert 112233 to DFA, minimize it, negagate it and intersect
/// handle long str to disjunct
fn neg_str_to_disjunc_new(s: &str)->String{
	//1. preprocessing string
	let s = &s[1..].to_owned();
	let nums = find_all(r"[0-9a-f]+", &s);
	assert!(nums.len()>0, "no numbers!: {}", &s);
	let unit_len = nums[0].len();
	for x in nums {assert!(x.len()==unit_len, "UNEQUAL unit number len!");}

	//2. build the DFAs
	let ws = String::from(".").repeat(unit_len);
	let dfa_n = build_dfa(&ws, false);
	let dfa_n = dfa_n.minimize();
	let dfa_2 = build_dfa(&s, true);
	let dfa_2 = dfa_2.minimize();
	let dfa_3 = dfa_n.intersect(dfa_2);
	let dfa_3 = dfa_3.minimize();
	let dfa3_regex = dfa_3.to_regex().simplify().to_string();
	let res = format!("({})", dfa3_regex);

	res
}


/// we handle `!(\d{2}) or !(\d{2}|....)` or even longer length
pub fn handle_negation(s: &str) -> String{
	let mut pairs = vec![];
	//1. handle !(\d{2})
	for subexpr in find_all(r"\!\([a-f0-9]+(\|[a-f0-9]+)*\)", s){
		//pairs.push( (subexpr.clone(), neg_str_to_disjunc(&subexpr)) );
		pairs.push( (subexpr.clone(), neg_str_to_disjunc_new(&subexpr)) );
	}
	//2. handle all pairs
	let mut s2 = String::from(s);
	for (olds, news) in pairs{
		s2 = s2.replace(&olds, &news);	
	}

	assert!(!s2.contains("!"), "after negation ! still exists: {}", &s2);
	return s2;
}


/// convert very 0x41 to 0x5a to 0x61 to 0x7a
/// assumption these letters stored at even idx
pub fn to_lower(s: &str)->String{
	let s = hex_to_u8(s);
	let mut vec:Vec<u8> = vec![];
	for i in (0..s.len()).step_by(2){
		let ch1 = s[i];
		if i+1>=s.len() {
			vec.push(ch1);
			continue;
		}
		let ch2 = s[i+1];
		let val = 16 * ch1 + ch2;
		let (newch1, newch2) = if val>=0x41 && val<=0x5a{
			let newval = val - 0x41 + 0x61;	
			(newval/16, newval%16)
		}else {(ch1, ch2)};
		vec.push(newch1);
		vec.push(newch2);
	}

	u8_to_hex(&vec)
}

/// tell if s is PCRE subsignature, mainly check existence of
/// non-escaped /
pub fn is_pcre_subsig(s:&str)->bool{
	let chs = s.chars().collect::<Vec<char>>();
	for i in 0..chs.len(){ 
		if chs[i]=='/' && i>0 && chs[i-1]!='\\'{ return true; } 
	}

	false	
}

/// extract the three parts from e.g. `0&1\/abc.*\/smi`
pub fn extract_clamav_reg(s: &str) -> (String,String,String){
	let s = s.to_string();
	let arr_s = s.split("/").map(str::to_string).collect::<Vec<String>>();	
	assert!(arr_s.len()>=3, "s: {} not pcre! Expect: trigger/str/flags", s);
	let idx1 = s.find("/").unwrap();
	let idx2 = s.rfind("/").unwrap();

	let trigger = s[0..idx1].to_string();
	let reg_s = s[idx1+1..idx2].to_string();
	let flags = s[idx2+1..].to_string();

	(trigger, reg_s, flags)
}

/// mainly the preprocess_regex for GeneralRegex but 
/// without approxiting range
/// return (String, b_ignore_case)
pub fn preprocess_general_regex_without_rep(s: &str)->(String,bool){
	let mut s = s.to_lowercase();
	s = s.replace("*", ".*");
	s = s.replace("?", ".");
	// REPLACE the old: s = handle_range(&s); with the following
	s = handle_range_without_approx(&s, true);
	let (s2, b_igc) = handle_modifier_but_no_igc(&s); //will be handled later
							//in hir handling
	s = handle_location(&s2);
	s = handle_negation(&s);

	(s, b_igc)
}

