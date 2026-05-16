/// Regex preprocessing (parser related) functions for clamav ldb format,
/// It contains "quick" discharging estimate functions such as
/// `discharge_file_by_crit_bag_pm()`, for real discharge proof
/// functions look at proof_gen.rs.
 /// For ClamAV ldb spec check: <https://docs.clamav.net/manual/Signatures/LogicalSignatures.html>

/* Created 01/04/2024 -> preprocessing of regex patterns
 Modified: 01/17/2024 -> added PM-Reg related preprocessing
 Modified: 06/13/2024 -> add PCRE preprocessing
 Modified: 06/26/2024 -> add DFA running in report
 Modified: 07/15/2024 -> Add TotalSubsigCount type
 Refactored: 07/25/2024
 Modified: 03/18/2025 -> Added quick_discharge_adv
 */

extern crate rayon;
extern crate rustomaton;
extern crate regex;
extern crate serde;
extern crate ark_serialize;
extern crate utils;

use rayon::prelude::*;
use self::serde::{ser::Error,Serialize,Deserialize,Serializer,Deserializer};
use std::{
	collections::{VecDeque,HashSet,HashMap,BTreeSet},
	collections::hash_map::{Entry},
	fmt, ops::{Not,BitAnd,BitOr},
	sync::{mpsc,Arc}, thread,
	time::Duration,
};

use regex::Regex;
use self::rustomaton::{
	automaton::{Buildable,Automata},
	nfa::{NFA},
	dfa::{DFA},
};

//use utils::consts::{WARN,LOG1,LOG2,LOG3, B_SINGLE_JOB_MODE,COMBINATION_LIMIT,RANGE_MAX,MAX_PM_SECTIONS, REPEAT_LEN_LIMIT, MIN_BAG_WORD_LEN, TEST_MODE};
use utils::{
	logger::{log, log_perf,LOG1,LOG2,LOG4,LOG6},
	consts::{read_global_config, B_DEBUG},
	os::{read_lines},
	timer::{Timer},
	data::{u8_to_hex}
};
use crate::{
	strings::{find_all,extract_nums,validate_counter_constraint,validate_ra_regex,validate_ra_regex_relaxed,validate_pm_regex,is_match,find_only,count_occ,drop_last_dotstar,split,validate_expr},
	type_def::{PcreInfo,ClamSigType,SubSigType,SubSigObj,ClamavApproxConfig,TriVal,ClamavSig,EvalDNF,CompOp},
	hex_acdfa::{HexACDFA},
	pcre::{collect_bag_words_from_rustomaton_regex, collect_pm_reg_from_rustomaton_regex, rustomaton_to_hir, collect_pm_reg_from_rustomaton_regex_worker, vec_pmreg_to_res, pcre_to_dfa, clamav_genregex_to_dfa, filter_bag_of_words,parse_pcre_subsig},
	fsa_utils::{size_nfa,build_dfa,size_dfa,empty_nfa,build_nfa,get_total_size},
	preprocess::{is_pcre_subsig,handle_range,handle_modifier,handle_location,handle_negation,handle_modifier_for_pm,handle_location_for_pm,recursive_triggers,plug_in_trigger},
	discharge_proof::{FailDischargeRecord},
};
use folding_schemes::{
	folding::foldpot::sigma_ir1cs::{WordInfo,DischargeSigInfo}
};



pub const RANGE_MAX:usize = 1<<31;
pub const B_SINGLE_JOB_MODE:bool = false; //set to true for debug
pub const TEST_MODE:bool = false; //set for debugging/test

impl SubSigType{
	pub fn from(v: u8)->Self{
		match v{
			0 => SubSigType::GeneralRegex,
			1 => SubSigType::CounterConstraint,
			2 => SubSigType::SubsigCountConstraint,
			_ => panic!("invalid value for SubsigType")
		}
	}
}

impl CompOp{
	pub fn from(v: u8)->Self{
		match v{
			0 => CompOp::NONE,
			1 => CompOp::GT,
			2 => CompOp::LT,
			3 => CompOp::EQ,
			_ => panic!("invalid value for CompOp")
		}
	}
}

impl TriVal{
	pub fn from(v: u8)->Self{
		match v{
			1 => TriVal::False,
			2 => TriVal::True,
			3 => TriVal::Maybe,
			_ => panic!("invalid value for TriVal")
		}
	}
}



/// boolean value to ternary value
pub fn bool_to_tri(b: bool)->TriVal{
	match b{
		true => TriVal::True,
		false => TriVal::False
	}
}

impl Not for TriVal{
	type Output = Self;
	fn not(self)->Self{
		match self{
			Self::False => Self::True,
			Self::True => Self::False,
			Self::Maybe => Self::Maybe
		}
	}
}

impl BitAnd for TriVal{
	type Output = Self;
	fn bitand(self, other: Self)->Self{
		match self{
			Self::False => 
				match other{
					Self::False => Self::False,
					Self::Maybe => Self::False,
					Self::True => Self::False,
				},
			Self::True => 
				match other{
					Self::False => Self::False,
					Self::Maybe => Self::Maybe,
					Self::True => Self::True,
				},
			Self::Maybe => 
				match other{
					Self::False => Self::False,
					Self::Maybe => Self::Maybe,
					Self::True => Self::Maybe,
				},
		}
	}
}

impl BitOr for TriVal{
	type Output = Self;
	fn bitor(self, other: Self)->Self{
		match self{
			Self::False => 
				match other{
					Self::False => Self::False,
					Self::Maybe => Self::Maybe,
					Self::True => Self::True,
				},
			Self::True => 
				match other{
					Self::False => Self::True,
					Self::Maybe => Self::True,
					Self::True => Self::True,
				},
			Self::Maybe => 
				match other{
					Self::False => Self::Maybe,
					Self::Maybe => Self::Maybe,
					Self::True => Self::True,
				},
		}
	}
}

impl SubSigObj{

	/// split fixed words and reg ops, assuming reg ops 
	/// only has . * ? and assuming fixed words in [0-9a-f]
	pub fn get_tokens(s: &str) -> Vec<String>{
		let chars = s.chars().collect::<Vec<char>>();
		let is_fixed = |c| -> bool {(c>='0' && c<='9') || (c>='a' && c<='f')};
		let mut res = vec![];
		let mut last_fixed = is_fixed(chars[0]);

		let mut cur_word = vec![];
		for i in 0..chars.len(){
			let c = chars[i];
			let cur_fixed = is_fixed(c);
			if cur_fixed!=last_fixed{
				let sword = cur_word.into_iter().collect::<String>();
				res.push(sword);
				cur_word = vec![];
				last_fixed = cur_fixed;
			}
			cur_word.push(c);
		}
		let sword = cur_word.into_iter().collect::<String>();
		res.push(sword);

		res
	}

	/// regex (dot star or question mark strings)
	/// to minmax bound not implemented yet
	pub fn reg_to_bound(s: &str) -> (usize, usize){
		let r1 = Regex::new(r"[\.\*\?]*").unwrap();
		let r2 = Regex::new(r"[\.]*").unwrap();
		assert!(r1.is_match(s), "s: {} not well-formed for reg_to_bound", s);
		let mut min = 0;
		let mut max = 0;
		// first identify all .* and remove them
		let arr_dot_star = find_all(r"\.\*", s);
		if arr_dot_star.len()>0{
			max = RANGE_MAX;
		}
		let s2 = s.to_string().replace(r".*", "");

		// then identify all .?
		let arr_dot_ques = find_all(r"\.\?", &s2);
		let s3 = s2.replace(".?", "");
		max += arr_dot_ques.len();

		// count the rest of dots
		assert!(r2.is_match(&s3), "s3: {} should consists of dots only", &s3);
		min += s3.len();
		max += s3.len();
		if max>RANGE_MAX {max = RANGE_MAX;}
		if min>RANGE_MAX {min = RANGE_MAX;}

		(min, max)
	}

	/// approximate itself to PM-Reg subsig
	pub fn approx_to_pm(&self, _cfg: &ClamavApproxConfig) -> SubSigObj{
		//1. if containing nested structure simply approx to .*
		let r_nested = Regex::new(r"\([^\)]*\(").unwrap();
		if r_nested.is_match(&self.real_value){
			//println!("WARN: nested structure usually cased by ai decorator: {}, directly approx to .*", self.real_value);
			let mut sig = self.clone();
			sig.real_value = ".*".to_string();
			return sig;
		}

		//1. check no nested groups
		let mut sig = self.clone();
		let mut val = self.real_value.clone();
		let old_val = val.clone();
		let r1 = Regex::new(r"^\([a-f0-9]*\($").unwrap();
		let r2 = Regex::new(r"^[a-f0-9\(\)\|\.\*\?]*$").unwrap();
		let r3 = Regex::new(r"^[abcdef0123456789().*?]+$").unwrap();
		assert!(!r1.is_match(&val), "nested ( structure. s: {}", val);
		assert!(r2.is_match(&val), "ERROR matching r2. s: {}", val);

		//2. convert all groups to appropriate lengths
		let groups = find_all(r"\(.*?\)", &val);
		for gp in groups{
			//1. verify all items are of the same length
			let items = find_all("[a-f0-9]+", &gp);
			assert!(items.len()>0, "no items in group: {}", &gp);
			let mut min_len = RANGE_MAX;
			let mut max_len = 0;
			for item in &items{
				if min_len>item.len() {min_len = item.len();}
				if max_len<item.len() {max_len = item.len();}
			}
			val = val.replace(&gp, &(".".repeat(min_len) + &".?".repeat(max_len-min_len)));
		}
		assert!(r3.is_match(&val), "ERROR: {} not pm-reg, original_val: {}", 
			&val, &old_val);
		sig.real_value = val;

		sig
	}

	/// only callable for PM-Reg, generate a section of
	/// patterns and the corresponding position ranges
	/// pattern bounds specifies that for each fixed pattern string
	/// the (min,max) allowed distance from the END of its previous 
	/// fixed word. 
	pub fn gen_pm_bounds(&self, cfg:&ClamavApproxConfig) 
		-> Vec<(String, (usize, usize))>{
		//1. assuming it is already approximated before the call
		let val = self.real_value.clone();
		let r1 = Regex::new(r"^[0-9a-f.*?]*$").unwrap();
		assert!(r1.is_match(&val), "call approx_to_pm first. val: {}", val);

		//2. retrieve tokens and parse all bounds
		let tokens = Self::get_tokens(&val); 
		if tokens.len()==0 {return vec![];} 		

		//3. set the pm_bounds
		let mut res = vec![];
		let r1 = Regex::new(r"^[0-9a-f]+").unwrap();
		let b_starts_fixed = r1.is_match(&tokens[0]); 
		let start_i = if b_starts_fixed {0} else {1};

		for i in (start_i..tokens.len()).step_by(2){
			let bound = if i>=1 {Self::reg_to_bound(&tokens[i-1])} else {(0,0)};
			res.push( (tokens[i].to_string(), bound) ) ;
		}

		let maxlen= if res.len()>cfg.max_pm_sections{cfg.max_pm_sections} 
			else {res.len()};
		res[0..maxlen].to_vec()
	}

	/// whenver possible, extract the LONGEST which is not contained
	/// in the given map yet.
	/// Return a HashSet of strings as critical pattern.
	/// Most likely returns a single element set, but for union patterns like
	/// ".*(abc|123).*" will return {abc, 123}.
	/// For patterns that CANNOT be discharged such as counter constraint subsig=0, subsig<2
	/// the pattern contains a SINGLE element "".
	pub fn get_critical_pattern(&self, myid: usize, map: &HashMap::<String, Vec<String>>, vec_sub_sigobj: &Vec<SubSigObj>, vec_subsig_bagwords: &Vec<HashSet<Vec<String>>>)->HashSet<String>{
		//0. utility functions
		let avg_len = |pats: &HashSet<String>| -> usize{
			let total_len:usize = pats.iter().map(|s| s.len()).sum();
			if total_len == 0 {0} else  {total_len/pats.len()}
		};
		let any_in_map= |pats: &HashSet<String>, map:&HashMap::<String,Vec<String>>| -> bool{
			for x in pats{ if map.contains_key(x) {return true;} }
			false
		};
		let vec_to_set = |v: &Vec<String> | -> HashSet<String>{
			v.iter().map(|s| s.clone()).collect::<HashSet<String>>()
		};
		let empty_set = || ->HashSet<String>{
			let mut hs = HashSet::<String>::new();
			hs.insert("".to_string());
			hs
		};
			

		//1. pats is essentially a bag of words (consider other factors such as counter constraints)
		//NOTE: for SubsigCountConstraint will be handled later
		let pats = self.get_patterns(myid, vec_sub_sigobj, vec_subsig_bagwords);
		let pats = pats.iter().map(|v| v.clone()).collect::<BTreeSet<Vec<String>>>();

		//2. select the max len out of patterns
		let mut max_pat = empty_set();
		for x in &pats{ 
			let x = vec_to_set(&x);	
			if avg_len(&x)>avg_len(&max_pat) {max_pat = x.clone();} 
		}

		//2. select the max pattern who is not in map
		let mut max_pat2 = empty_set();
		for x in &pats{
			let x = vec_to_set(&x);
			if x.len()>max_pat2.len() && !any_in_map(&x, map) {max_pat2=x.clone();} 
		}

		//3. weights between two options
		let weight = 3;
		let res = if avg_len(&max_pat2)*weight>avg_len(&max_pat) {max_pat2} else {max_pat};
		res
	}

	/// return all the patterns inside
	/// if this is an arithmetic pattern (e.g., 0>5)
	/// will extract the patterns from 0.
	/// if the constraint is like "id=0", then return an default {""} (can't discharge)
	pub fn get_patterns(&self, myid: usize, vec_sub_sigs: &Vec<SubSigObj>, vec_subsig_bagwords: &Vec<HashSet<Vec<String>>>)->HashSet<Vec<String>>{
		self.get_patterns_new(myid, vec_sub_sigs, vec_subsig_bagwords)
	}

	pub fn get_patterns_old(&self, vec_sub_sigs: &Vec<SubSigObj>) ->Vec<String>{
		let b_debug = B_DEBUG;
		match self.subsig_type{
			SubSigType::GeneralRegex => {
				if b_debug{ validate_ra_regex(&self.value, "unknown"); }
				find_all(r"[0-9a-f]+", &self.value)	
			},
			SubSigType::CounterConstraint => {
				if b_debug{validate_counter_constraint(&self.value, "unknown");}
				let nums = extract_nums(&self.value);
				let id = nums[0];
				if self.value.contains("=0"){
					vec![]
				}else{
					vec_sub_sigs[id].get_patterns_old(vec_sub_sigs)	
				}
					
			},
			SubSigType::SubsigCountConstraint => {
				unimplemented!("SubsigCounterConstraint not handled yet")
			}
		}
	}

	/// use the vec_subsig_bagwords instead, basically returns bag of words (except with
	/// some additional inspection of counter constraints
	pub fn get_patterns_new(&self, myid: usize, vec_sub_sigs: &Vec<SubSigObj>, vec_subsig_bagwords: &Vec<HashSet<Vec<String>>>)->HashSet<Vec<String>>{
		assert!(vec_subsig_bagwords.len()>0, "call collect_bagwords first!");
		match self.subsig_type{
			SubSigType::GeneralRegex => {vec_subsig_bagwords[myid].clone()}
			SubSigType::CounterConstraint => {
				//1. assert it's id(<|>|=)num constraint (no multiple ID, no multiple number
				validate_counter_constraint(&self.value, "unknown");

				//2. extract info
				let nums = extract_nums(&self.value);
				let id = nums[0];
				if self.value.contains("=0") || self.value.contains("<"){
					let mut hs = HashSet::<Vec<String>>::new();
					hs.insert(vec!["".to_string()]); //cannot be discharged
					hs
				}else{//for ">xx" cases, aparently needs subsig to true
					vec_sub_sigs[id].get_patterns(id, vec_sub_sigs, vec_subsig_bagwords)	
				}
					
			},
			SubSigType::SubsigCountConstraint => {
				//no need to collec thte patterns because its subsigs
				//will be evaluated
				HashSet::<Vec<String>>::new()
			}
		}
	}

}

/// dummy wrapper for NFA for serialization
#[derive(Clone)]
pub struct MyNFA(NFA<char>);
impl Serialize for MyNFA{
	fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
	 where S: Serializer { //do nothing, dummy 
	 	Err(Error::custom("dummy function should not call"))
	}
}

impl fmt::Debug for MyNFA{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result{
		write!(f, "nfa size: {:?}", size_nfa(&self.0))
	}
}

impl<'de> Deserialize<'de> for MyNFA{
 fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
   where D: Deserializer<'de>
 {
 	unimplemented!("dummy function should not call");
 }
}


/// from string record generate a clamav sig
pub fn gen_clamav_sig(s: &str, sigtype: ClamSigType, cfg: &ClamavApproxConfig) 
	-> ClamavSig{
	let parts:Vec<String> = s.split(";").map(str::to_string).collect();
	let mut sig = ClamavSig{ 
		name: parts[0].clone(),
		desc: parts[1].clone(),
		expr: parts[2].clone(),
		line: String::from(s),
		vec_subsigs: parts[3..].to_vec(),
		vec_subsig_obj: vec![],
		vec_bneg: vec![false; parts.len()-3],
		vec_bcase_sensitive: vec![true; parts.len()-3],
		eval_dnf: EvalDNF{vec_disjunc:vec![]},
		sigtype: sigtype, 
		vec_subsig_automaton: vec![],
		vec_subsig_bagwords: vec![],
		vec_subsig_pm_bounds: vec![],
		vec_pcre_info: vec![],
		b_no_crit_pat: false,
	};
	sig.preprocess(cfg);

	sig
}

/// preprocess clamav regex so that it follows format of rustomaton regex
/// return the (trigger string (applicable to pcre only), 
///   the preprocessed string that conforms to rustomaton syntax (with
///          class, macros preprocssed, and lookaround and backref approximated)
///   and whether case insensitive)
pub fn preprocess_regex(s:&str, name: &str, sigtype: ClamSigType, cfg: &ClamavApproxConfig)
->(String, String, bool, PcreInfo){
	let old_s = s.to_string();
	let mut s = s.to_lowercase();
	let b_case_sensitive;
	let mut trigger = String::new();
	let b_pcre = is_pcre_subsig(&old_s);
	let mut pi = PcreInfo::new_false();
	if b_pcre{
		(trigger, s, b_case_sensitive, pi)  = parse_pcre_subsig(&old_s, cfg.combination_limit, cfg.repeat_limit);
		if s.len()>1024*1024{
			println!("WARN: preproces_regex len: {}, name: {}", s.len(), name);
		}
	}else if sigtype==ClamSigType::General{
		s = s.replace("*", ".*");
		s = s.replace("?", "."); 
		s = handle_range(&s);
		(s, b_case_sensitive) = handle_modifier(&s);
		s = handle_location(&s);
		s = handle_negation(&s);
		validate_ra_regex_relaxed(&s, &name);
	}else if sigtype==ClamSigType::PM{
		s = s.replace("*", ".*");
		s = s.replace("?", ".");
		s = handle_range(&s);
		(s, b_case_sensitive) = handle_modifier_for_pm(&s);
		s = handle_location_for_pm(&s);
		s = handle_negation(&s);
		validate_pm_regex(&s, &name);
	}else{
		panic!("unhandled type: {:?}", sigtype);
	}

	(trigger, s, b_case_sensitive, pi)
}

impl ClamavSig{

	pub fn to_str(&self)->String{
		format!("{}: {}", self.name, self.line)
	}

	pub fn get_automaton(&self,id: usize) -> Arc<DFA<char>>{
		self.vec_subsig_automaton[id].clone()
	}

	/// Preprocess to conform to rustomaton regex format
	pub fn preprocess(&mut self, cfg: &ClamavApproxConfig){
		//1. preprocess all substrings
		let copy_subsigs = self.vec_subsigs.clone();
		let vec_tripples: Vec<(String,String,bool, PcreInfo)> = 
		if B_SINGLE_JOB_MODE{
			self.vec_subsigs.iter()
			.map(|s| preprocess_regex(s, &self.name, self.sigtype, cfg)).collect()
		}else{
			self.vec_subsigs.par_iter()
			.map(|s| preprocess_regex(s, &self.name, self.sigtype, cfg)).collect()
		};

		let (triggers, new_subsigs, new_bc, vec_pi): 
			(Vec<String>,Vec<String>,Vec<bool>, Vec<PcreInfo>) = 
			(
				vec_tripples.par_iter().map(|t| t.0.clone()).collect(),
				vec_tripples.par_iter().map(|t| t.1.clone()).collect(),
				vec_tripples.par_iter().map(|t| t.2.clone()).collect(),
				vec_tripples.par_iter().map(|t| t.3.clone()).collect(),
			);


		//2. handle expr
		self.vec_pcre_info = vec_pi;
		for i in 0..copy_subsigs.len(){
			//copy back the old string (for DFA constr)
			self.vec_pcre_info[i].original_str= copy_subsigs[i].clone();
		}
		self.vec_subsigs = new_subsigs.clone();
		self.vec_bcase_sensitive = new_bc.clone();
		self.expr = self.expr.replace("==", "=");
		for i in 0..triggers.len(){
			let rec_trig = recursive_triggers(i, &triggers);
			self.expr = plug_in_trigger(i, &self.expr, &rec_trig);
		}
		if self.sigtype==ClamSigType::PM{
			self.preprocess_expr_new(true);
		}else if self.sigtype==ClamSigType::General{
			//self.preprocess_expr();
			self.preprocess_expr_new(false);
		}else{
			panic!("cannot handle self.sigtype: {:?}", self.sigtype);
		}
		//3. generate the evaluation DNF formula 
		self.gen_eval_dnf();

	}

	/// can be expensive when we have a lot of patterns, make it optional
	pub fn gen_vec_automaton(&self, cfg: &ClamavApproxConfig) -> Vec<Arc<DFA<char>>>{
		let log_level = LOG4;
		let mut vec_subsig_automaton = vec![];
		for (id, subsig) in self.vec_subsig_obj.iter().enumerate(){
			let mut timer = Timer::new();
			let mut dfa = if self.vec_subsig_obj[id].subsig_type==SubSigType::SubsigCountConstraint{
				//just build a dummy one
				build_dfa("", false)
			} else if self.vec_subsig_obj[id].subsig_type==SubSigType::CounterConstraint{
				let sig = &subsig.value;
				if !is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", &sig){
					panic!("INVALID counter sig: {}", &sig);
				}
				let id = extract_nums(&sig)[0]; 
				let num = extract_nums(&sig)[1]; 
				let sop = find_only(r">|<|=", &sig);
				let (op, num) = Self::strop_to_comp_op(&sop, num);
				let s = self.vec_pcre_info[id].original_str.clone();
				if is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", &s){
					//s cannot be counter string itself.
					panic!("INVALID sub str {} used in counter sig: {}", &s, &sig);
				}

				let dfa = if !is_pcre_subsig(&s){ clamav_genregex_to_dfa(&s) }
					else{ pcre_to_dfa(&s, cfg.combination_limit, cfg.repeat_limit) };

				let dfa = if dfa.transitions.len()<256 {dfa.minimize()}
					else {dfa};
				let repeat = if op==CompOp::LT{
					//e.g., 0 < 3, repeat pm-reg 3 times
					// if NOT match can justify as True! otherwise Maybe
					num
				}else if op==CompOp::EQ{
					if num>0{
						//e.g. 0 = 2 (2 times), if NOT match 
						// can justify as False!, otherwise Maybe
						num 
					}else{
						// if return False -> True (because no match)
						// otherwise maybe is maybe
						1
					}
				}else{//GT
					//e.g. 0>2, repeat pm-reg patterns for 3 times
					//if NOT match can justify as False! otherwise Maybe
					num + 1
				};
				let repeat = if repeat >cfg.repeat_limit
						{cfg.repeat_limit} else {repeat};
				let dfa_res = dfa.repeat(repeat..=repeat);
				dfa_res
			}else if !self.vec_pcre_info[id].b_pcre{
				let s = self.vec_pcre_info[id].original_str.clone();
				let dfa = clamav_genregex_to_dfa(&s);
				dfa
			}else{//for pcre (because we can leverage structure info)
				let s = self.vec_pcre_info[id].original_str.clone();
				let dfa = pcre_to_dfa(&s, cfg.combination_limit, cfg.repeat_limit);
				dfa
			};
			log(0, log_level, &format!(" gen_vec_automaton build dfa size: {:?}", size_dfa(&dfa)));
			log_perf(0, log_level, " gen_vec_automaton build dfa: ", &mut timer);
			dfa.raw_str = subsig.value.clone();
			vec_subsig_automaton.push( Arc::new(dfa) );
		}
		vec_subsig_automaton
	}

	pub fn set_vec_automaton(&mut self, cfg: &ClamavApproxConfig){
		//println!("DEBUG USE 300: set_automaton ... {}", self.to_str());
		self.vec_subsig_automaton = self.gen_vec_automaton(cfg);
		let _vlen = self.vec_subsig_automaton.iter().map(|v| v.transitions.len()).collect::<Vec<usize>>();
		//println!("DEBUG USE 301: {} set vec automaton: {}, SIZES: {:?}", 
		//	self.to_str(), self.vec_subsig_automaton.len(), &vlen);
	}


	/// evaluate subsignature by automaton (only for general regex
	/// or counter constraint).
	pub fn subsig_accepts_by_automaton(&self, id: usize, s2: &Vec<char>)->bool{
		let res = match self.vec_subsig_obj[id].subsig_type{
			SubSigType::GeneralRegex => {
				let hs = self.vec_subsig_automaton[id].run(&s2);
				hs
			},
			SubSigType::CounterConstraint => {
				let sig = &self.vec_subsig_obj[id].value;
				if !is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", &sig){
					panic!("INVALID counter sig: {}", &sig);
				}
				let _id = extract_nums(&sig)[0]; 
				let num = extract_nums(&sig)[1]; 
				let sop = find_only(r">|<|=", &sig);
				let (op, num) = Self::strop_to_comp_op(&sop, num);
				let ps = self.vec_subsig_automaton[id].run(&s2);
				match op{
					CompOp::NONE => {panic!("comp op is None!")}
					CompOp::LT => { 
						//note repeats have been encoded
						//e.g., 0<2 is encoded as pat_0{2}
						//then not match means TRUE 
						!ps
					},
					CompOp::EQ => if num>0 {
						//e.g., 0=1, no match means false
						ps
					} else {
						// e.g. 0 = 0 (encoded as pat_0)
						// no match means true
						!ps
					},
					CompOp::GT => {
						// match means so many instances
						ps
					}
				}
			},
			SubSigType::SubsigCountConstraint=> {
				panic!("subsig_accepts_by_automaton do not handle SubsigCountConstraint");
			}
		};

		res
	}

	/// returns true if the string is accepted by the signature (match)
	/// i.e., it is a virus. Returh the discharge info with the minimum
	/// cost that returns false.
	pub fn accepts_by_automaton(&self, sig_id: usize, str_src: &Vec<u8>) 
	-> (bool,Option<DischargeSigInfo>){
		let b_debug = B_DEBUG;
		if self.vec_subsig_obj.len() != self.vec_subsig_automaton.len(){
			//println!("NEEDS to build automaton for {}", self.to_str());
			return (true,None); //default conservative value
		}
		assert!(self.vec_subsig_obj.len() == self.vec_subsig_automaton.len(),
			"sig: {}, vec_subsig.len(): {} != vec_subsig_automaton.len(): {}, call set_vec_automaton",
			self.to_str(), self.vec_subsig_obj.len(), self.vec_subsig_automaton.len());

		let mut bres = true;
		let mut min_dnf_id = 0usize;
		let mut min_cost = 1usize<<30;
		let mut found_discharge = false;
		let mut dnf_id = 0usize;
		let s2 = u8_to_hex(str_src).as_bytes().to_vec().iter()
			.map(|s| *s as char).collect::<Vec<char>>();
		for item in &self.eval_dnf.vec_disjunc{
			let mut item_res = false;
			let total_cost = item.len();
			for id in item{
				let res = match self.vec_subsig_obj[*id].subsig_type{
					SubSigType::GeneralRegex => {
						self.subsig_accepts_by_automaton(*id, &s2)
					},
					SubSigType::CounterConstraint => {
						self.subsig_accepts_by_automaton(*id, &s2)
					},
					SubSigType::SubsigCountConstraint => {
						let mut cnt_true = 0;
						let mut _cnt_false= 0;
						let min_required = self.vec_subsig_obj[*id]
							.min_required;
						let set_subsigs = self.vec_subsig_obj[*id].set_subsigs
							.clone();
						for cid in set_subsigs{
							let res = self.subsig_accepts_by_automaton(cid, 
								&s2);
							match res{
								true => cnt_true +=1,
								false => _cnt_false +=1,
							}
						}
						let res = cnt_true>=min_required;

						res

					}
				};
				//let res2 = if self.vec_bneg[*id] {!res} else {res};
				if b_debug{
					let subsig_id= HexACDFA::gen_subsig_id_worker(
						sig_id, *id + 1); 
					println!("DEBUG USE 6735.1 discharge sig: {} subsig: {} by dfa: {}", self.name, subsig_id, res);
				}
				item_res = item_res || res;
			}
			bres = bres && item_res;
			if item_res==false{//this is a good discharging proof!
				found_discharge = true;
				if min_cost > total_cost{
					min_cost = total_cost;
					min_dnf_id = dnf_id; 
				}
			}
			dnf_id += 1;
		}

		let info = if !found_discharge {None} else {
			let subsig_ids = self.collect_subsig_ids(min_dnf_id);
			let subsig_igc = subsig_ids.iter().map(|id|
				self.vec_subsig_obj[*id].b_ignore_case
			).collect::<Vec<bool>>();

			Some(DischargeSigInfo{
				sig_name: self.name.clone(),
				b_success: true,
				min_cost, 
				min_dnf_id,
				subsig_ids,
				subsig_igc,
			})
		};

		(bres, info)
	}

	/// collect all patterns appeared in each subsignature
	pub fn collect_all_patterns(&self)->HashSet<String>{
		let mut hset = HashSet::<String>::new();
		for (id, x) in self.vec_subsig_obj.iter().enumerate(){
			let vec_pat = x.get_patterns(id, &self.vec_subsig_obj, &self.vec_subsig_bagwords);
			for u in vec_pat{
				for x in u{
					hset.insert(x);
				}
			}
		}

		hset
	}

	/// for each subsignature generate its pm_pos_bounds
	/// If it is general expression, needs to approximate 
	/// its vec_subsig_obj first.
	pub fn gen_approx_pm_bounds(&mut self, cfg: &ClamavApproxConfig){
		//self.gen_approx_pm_bounds_old();
		self.gen_approx_pm_bounds_new(cfg);
	}

	/// OLD approach: approximate the regex to PM first and then collect.
	pub fn gen_approx_pm_bounds_old(&mut self, cfg: &ClamavApproxConfig){
		//1. if no PM-Reg, approximate each subsiganture
		let vec_subsig_obj = if self.sigtype==ClamSigType::PM 
			{self.vec_subsig_obj.clone()} else{
				self.vec_subsig_obj.iter().map(|s| s.approx_to_pm(cfg)).
				collect::<Vec<SubSigObj>>()
			};
		//2. for each sub-signature generates its PM-Bounds
		self.vec_subsig_pm_bounds = vec_subsig_obj.iter().map(|s|
			s.gen_pm_bounds(cfg)).collect::<Vec<Vec<(String, (usize, usize))>>>();

	}

	/// NEW approach: directly based on regex structure
	pub fn gen_approx_pm_bounds_new(&mut self, cfg: &ClamavApproxConfig){
		self.vec_subsig_pm_bounds = self.vec_subsig_obj.iter().map(|s|{
			let vec = match s.subsig_type{
				SubSigType::GeneralRegex => 
					collect_pm_reg_from_rustomaton_regex(&s.real_value, cfg.min_pm_word_len),
				SubSigType::SubsigCountConstraint => {
					// its related subsigs will collect pm-reg
					// no need to generate
					vec![]
				},
				SubSigType::CounterConstraint =>{
					let sig = &s.value;
					if !is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", &sig){
						panic!("INVALID counter sig: {}", &sig);
					}
					let id = extract_nums(&sig)[0]; 
					let num = extract_nums(&sig)[1]; 
					let sop = find_only(r">|<|=", &sig);
					let (op, num) = Self::strop_to_comp_op(&sop, num);
					let hir = rustomaton_to_hir(
						&self.vec_subsig_obj[id].real_value); 
					let vec= collect_pm_reg_from_rustomaton_regex_worker(&hir, cfg.min_pm_word_len);
					let mut res = vec![];
					let repeat = if op==CompOp::LT{
						//e.g., 0 < 3
						// repeat pm-reg 3 times
						// if NOT match can justify as True! otherwise Maybe
						num
					}else if op==CompOp::EQ{
						if num>0{
							//e.g. 0 = 2 (2 times)
							// can pm-reg pattern 2 times
							// if NOT match can justify as False! 
							// otherwise Maybe
							num 
						}else{
							// do one pm-reg sequence
							// if return False -> True (because no match)
							// otherwise maybe is maybe
							1
						}
					}else{//GT
						//e.g. 0>2
						//repeat pm-reg patterns for 3 times
						//if NOT match can justify as False! otherwise Maybe
						num + 1
					};
					let repeat = if repeat >cfg.repeat_limit
							{cfg.repeat_limit} else {repeat};
					for _i in 0..repeat {res.append(&mut vec.clone());}
					let res = vec_pmreg_to_res(&res);
					let maxlen= if res.len()>cfg.max_pm_sections{
						cfg.max_pm_sections} else {res.len()};
					res[0..maxlen].to_vec()
				}
			};

			let new_vec = self.remove_special_pats(&vec, s);
			new_vec
		}).collect::<Vec<Vec<(String, (usize, usize) )>>>();
	}

	/// handle special patterns like 0000
	/// e.g., given abcd....0000...dede 
	/// which has vec_subsig_pm_bounds: 
	/// [ ("abcd", (0,0)), ("0000", (4,4)), ("dede",(3,3))]
	/// we merge it to
	/// abcd...........dede
	/// thus we are dropping the item ("0000",(4,4)) and change the last item
	/// to
	/// ("dede", (7,7))
	fn remove_special_pats(&self, v: &Vec<(String,(usize,usize))>, _subsig_obj: &SubSigObj)->Vec<(String,(usize,usize))>{
		let vec_r = vec![
			Regex::new(r"^0+$").unwrap(),
			Regex::new(r"^((ff)+|(FF)+)$").unwrap(),
			Regex::new(r"^(1|2|3|4)0000000$").unwrap(),
			Regex::new(r"^(2|4)000$").unwrap(),
			Regex::new(r"^488.$").unwrap(),
			Regex::new(r"^430.$").unwrap(),
			Regex::new(r"^0004$").unwrap(),
			Regex::new(r"^feff$").unwrap(),
			Regex::new(r"^00008$").unwrap(),
			Regex::new(r"^000080$").unwrap(),
			Regex::new(r"^000.$").unwrap(),
			Regex::new(r"^0.00$").unwrap(),
			Regex::new(r"^00.0$").unwrap(),
			Regex::new(r"^0.0000$").unwrap(),
			Regex::new(r"^202020$").unwrap(),
			Regex::new(r"^909090$").unwrap(),

	// the following section cuts 
	// acc_states/path_len: avg: 2.644863392127692%, max: 4.188081767927191%
    // pat ratio: avg: 5.9035273%, max: 14.321802%
	Regex::new(r"^fffe+$").unwrap(), //max acc_rate: 16%, pat_rate: 16%
	Regex::new(r"^80000000+$").unwrap(), //max acc_rate: 6%, pat_rate: 6%
	Regex::new(r"^003000+$").unwrap(), //max acc_rate: 3%, pat_rate: 6%
	Regex::new(r"^30003000+$").unwrap(), //max acc_rate: 3%, pat_rate: 6%
	Regex::new(r"^00005+$").unwrap(), //max acc_rate: 6%, pat_rate: 6%
	Regex::new(r"^20202020+$").unwrap(), //max acc_rate: 6%, pat_rate: 6%
	Regex::new(r"^0001000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 5%
	Regex::new(r"^01000000+$").unwrap(), //max acc_rate: 4%, pat_rate: 5%
	Regex::new(r"^000000be+$").unwrap(), //max acc_rate: 1%, pat_rate: 4%
	Regex::new(r"^00be+$").unwrap(), //max acc_rate: 1%, pat_rate: 4%
	Regex::new(r"^0000be+$").unwrap(), //max acc_rate: 1%, pat_rate: 4%

	//the following section further cuts to:
	//acc_states/path_len: avg: 2.4027024486509037%, max: 4.035532885396304%
	//pat ratio: avg: 5.424644%, max: 13.7453165%
	Regex::new(r"^03000000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^ffff8b85+$").unwrap(), //max acc_rate: 2%, pat_rate: 3%
	Regex::new(r"^8b85+$").unwrap(), //max acc_rate: 2%, pat_rate: 3%
	Regex::new(r"^3c00000000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^3c0000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^00e9+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^ff25+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^34343434343434343434343434343434+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^02000000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^0c000000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^000006+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^3d3078+$").unwrap(), //max acc_rate: 1%, pat_rate: 3%
	Regex::new(r"^3078+$").unwrap(), //max acc_rate: 1%, pat_rate: 3%
	Regex::new(r"^0fb6+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^24000000+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%
	Regex::new(r"^ffff00+$").unwrap(), //max acc_rate: 3%, pat_rate: 3%

	//the following section further cuts to:
	//acc_states/path_len: avg: 1.6504275105446908%, max: 2.526902270768031% 
	//pat ratio: avg: 3.9314427%, max: 13.319191%
	Regex::new(r"^0068+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^000068+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^5050505050505050+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^00010000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^00000a+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^28000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^3001+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^c78424+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^000002000000+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^1500+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^46000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^0000000e+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^07000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^4100+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^8b45+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^5420+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^726d+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^666f726d+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^303030+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^3030+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^0069+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^000069+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^00e8+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^0000e8+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^13000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^00000040+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^676574+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^5f676574+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^2c20+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^894424+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^48894424+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^4885c0+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^85c0+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^faff+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^180000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^8d05+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^488d05+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^646d696e+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^61646d696e+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^696e+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^5bc3+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^0401+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^4c000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^000041+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^1c00+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^8985+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^51515151515151+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^01000000000000000000+$").unwrap(), //max acc_rate: 2%, pat_rate: 2%
	Regex::new(r"^0074+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%
	Regex::new(r"^000074+$").unwrap(), //max acc_rate: 1%, pat_rate: 2%

	//the following section further cuts to:
	//acc_states/path_len: avg: 0.991%, max: 1.67%
	//pat ratio: avg: 2.4242725%, max: 13.2924%
	Regex::new(r"^006f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0f85+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^466f726d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488b15+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b15+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^002600+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^89c7e8+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^b8000000+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^00010000000100000001000000+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^b800+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^c70424+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^000000ba+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b0d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488b0d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^31c0+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^786d6c+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8d7c24+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6973+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^70726f746f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^4883c4+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^83c4+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^68747470+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^83c0+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b95+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^83ec+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^4883ec+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8dbc24+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^51000000+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^2f6170692f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^7100+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8d15+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^000000000002+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b4424+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^292e+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^616e+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^4f000000+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^2e676f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^ff15+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6c616e67+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b1d+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^488b1d+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^c1e8+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8b35+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^488b35+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^2028+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0280+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0345+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488944+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^302e+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^00040000+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^482d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^4944+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^5049+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^895c24+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^5c24+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^00000000ff+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^2e2e+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^85c074+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488d35+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^c744+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8bb424+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^5068+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^004d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^616d+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^73747265616d+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^6f6e+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^272c27+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^7468+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^1700+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^c74424+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^88d9+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^2746+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0355+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^ff05+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0fbd+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^7405+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^736574+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6060+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488b3d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^696e6b+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^6c696e6b+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^4e4f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6c73+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^5442+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^01000000e8+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^666f72+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^696e707574+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^85c00f85+$").unwrap(), //max acc_rate: 0%, pat_rate: 1%
	Regex::new(r"^800f+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^895424+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6d61746368+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0065+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^488d3d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^2623+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^005079+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^6600+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^8d0d+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^ffe0+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%
	Regex::new(r"^0175+$").unwrap(), //max acc_rate: 1%, pat_rate: 1%

	// The following CANNOT BE INCLUDED because they are too long
	// and mostly are the "ONLY" anchor word in subsigs, dropping them will
	// lead to failure to discharge signatures. 
	//Regex::new(r"^20202020$").unwrap(), -> longer will be worst
	//Regex::new(r"^0100010001000100+$").unwrap(), //max acc_rate: 11%, pat_rate: 11%
	//Regex::new(r"^55555555+$").unwrap(), //max acc_rate: 13%, pat_rate: 13%

		];
		let is_special = |s: &String,vec_r: &Vec<Regex>| -> bool{
			for r1 in vec_r{
				if r1.is_match(s){
					return true;	
				}
			}
			return false;
		};

		let mut res = vec![];
		let mut i = 0;
		while i<v.len(){
			let item = &v[i];
			let s = &item.0;
			let (mut min,mut max) = (item.1.0, item.1.1);
			if !is_special(&s, &vec_r){
				res.push(item.clone());
				i += 1;
			}else{
				//loop to find the next item to merge
				//note: if not found, no item to add anyway
				//the ".*" will be appended automatically
				i += 1;
				while i<v.len(){
					let next_item = &v[i];
					min = if next_item.1.0==usize::MAX || min==usize::MAX {
						usize::MAX
					} else {
							min + next_item.1.0 + v[i-1].0.len()
					};
					max = if next_item.1.1==usize::MAX || max==usize::MAX{
						usize::MAX} else {
							max + next_item.1.1 + v[i-1].0.len()
						};
					if !is_special(&next_item.0, &vec_r){
						let new_item = (next_item.0.clone(), (min,max));
						res.push(new_item);
						i +=1; 
						break;
					}else{
						i += 1;
					}
				}
			}
		}


		res
	}

	// based on dnf_id, collect the raw_subsig_ids
	// if there are subcomponents, collect them as well
	fn collect_subsig_ids(&self, dnf_id: usize) -> Vec<usize>{
		let raw_subsig_ids = self.eval_dnf.vec_disjunc[dnf_id].clone();
		let mut vec_res:Vec<usize> = vec![];
		for id in raw_subsig_ids{
			let stype = &self.vec_subsig_obj[id].subsig_type;
			match stype{
				SubSigType::GeneralRegex => vec_res.push(id),
				SubSigType::CounterConstraint=> vec_res.push(id),
				SubSigType::SubsigCountConstraint => {
					vec_res.append(&mut 
						self.vec_subsig_obj[id].set_subsigs.iter().
							map(|x| *x).collect::<Vec<usize>>() );
					vec_res.push(id);
				},
			}
		}
		let set_vec = vec_res.iter().map(|x| *x)
			.collect::<HashSet<usize>>();
		let mut res = set_vec.into_iter().map(|x| x)
			.collect::<Vec<usize>>(); 
		res.sort();

		res
	}


	/// accept using the pm-bounds
	/// the result is conservative. When unsure, return Maybe.
	/// the 2nd option in return is set to Some  when TriVal is False 
	/// (meaning signature discharged).
	/// the information <usize, usize, Vec<usize>>
	/// refers to (min_cost, min_dnf_id, dnf_item located at min_dnf_id>).
	/// note the min_dnf_id starts from 0
	pub fn accepts_approx_pm_bounds(&self, hs: &HashMap<String, Vec<usize>>,
		hs_igc: &HashMap<String, Vec<usize>>, fname: &str)
	-> (TriVal, Option<DischargeSigInfo>){
		let mut b_debug = B_DEBUG;
		if b_debug {
			let debug_sig = "Win.Packed.Gandcrab-6911085-1";
			b_debug = b_debug && format!("{}",debug_sig) == self.name;
			if b_debug{
				println!("DEBUG USE 6999.1: sig: {}", self.name);
				for i in 0..self.vec_subsig_obj.len(){
					println!(" -- subsig[{}]: {}", 
						i, self.vec_subsig_obj[i].value);
				}
			}
		}

		assert!(self.vec_subsig_obj.len() == self.vec_subsig_pm_bounds.len(),
			"vec_subsig.len() not matching vec_subsig_pm_bounds, call gen_approx_pm_bounds");
		let mut bres = TriVal::True;
		let mut min_dnf_id = 0usize;
		let mut min_cost = 1usize<<30;
		let mut found_discharge = false;
		let mut dnf_id = 0usize;
		for item in &self.eval_dnf.vec_disjunc{
			let mut item_res = TriVal::False;
			let mut total_cost = 0;
			for id in item{
				let (res,_cost,cost) = self.approx_eval_pm_bounds_subsig(*id,hs, hs_igc, fname);
				total_cost += cost;
				let res = match self.vec_subsig_obj[*id].subsig_type{
					SubSigType::GeneralRegex => res,
					SubSigType::CounterConstraint => {
						let sig = &self.vec_subsig_obj[*id].value;
						if !is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", &sig){
							panic!("INVALID counter sig: {}", &sig);
						}
						let _id = extract_nums(&sig)[0]; 
						let num = extract_nums(&sig)[1]; 
						let sop = find_only(r">|<|=", &sig);
						let (op, num) = Self::strop_to_comp_op(&sop, num);
						match op{
							CompOp::NONE=> panic!("op is NONE"),
							CompOp::LT => !res,
							CompOp::EQ => if num>0 {res} else {!res},
							CompOp::GT => res,
						}
					},
					SubSigType::SubsigCountConstraint => {
						let mut cnt_true = 0;
						let mut cnt_maybe= 0;
						let mut _cnt_false= 0;
						for cid in &self.vec_subsig_obj[*id].set_subsigs{
							let (res, _cost, _cost2)=
								self.approx_eval_pm_bounds_subsig(
									*cid, hs, hs_igc, fname
								);
							match res{
								TriVal::True => cnt_true +=1,
								TriVal::Maybe => cnt_maybe+=1,
								TriVal::False => _cnt_false +=1,
							}
						}
						let min_required = self.vec_subsig_obj[*id]
							.min_required;
						let res = if cnt_true>=min_required {
							TriVal::True //for sure
						} else if cnt_true + cnt_maybe < min_required{
							TriVal::False //for sure
						} else {
							TriVal::Maybe //not for sure
						};

						res
					}
				};
				//NO need to take care of bneg (because the < and =0 logic
				//already taken care of
				//let res = if self.vec_bneg[*id] { !res } else {res};
				item_res = item_res | res;

			}//end of evaluating DNF
			if item_res==TriVal::False{//this is a good discharging proof!
				found_discharge = true;
				if min_cost > total_cost {
					min_cost = total_cost;
					min_dnf_id = dnf_id; 
				}
				if b_debug{
					println!("-- DEBUG USE 6999.2 found one discharge dnf_id: {}, dnf_item: {:?}, cost: {}, min_dnf_id: {}, min_cost: {}", dnf_id, item, total_cost, min_dnf_id, min_cost);
				}
			}else{
				//min_cost = 0; //it fails anyway, will not discharge
							//through sed.
			}
			dnf_id += 1;

			bres = bres & item_res;
		}

		let subsig_ids = self.collect_subsig_ids(min_dnf_id);
		let subsig_igc = subsig_ids.iter().map(|id|
			self.vec_subsig_obj[*id].b_ignore_case
		).collect::<Vec<bool>>();

		let info=Some(DischargeSigInfo{
				sig_name: self.name.clone(),
				b_success: found_discharge,
				min_cost, 
				min_dnf_id,
				subsig_ids,
				subsig_igc,
			});

		(bres, info)
	}

	/// evaluate subsignature for PM/SED approach.
	/// Return: (TriVal, cost)
	/// cost is the total length of the allowed_pos for all legs of the
	/// subsignature
	/// cost2 is the total number of appearance for all ag words
	/// in the subsignature. (cost2 is much greater than cost, as
	/// cost is the result applying the range check between neighboring
	/// patterns)
	/// return (DisChargeResult, cost, cost2)
	///
	/// NOTE: when vec_subsig_pm_bounds has NO PATTERNS at all
	/// it will simply return MayBe (because there is no way to tell
	/// if the subsig is satisfied by the string or not).
	/// NOTE2: for "regular" case there is always two outcomes:
	///   Maybe and False (because you can NEVER assuure that it's a True).
	fn approx_eval_pm_bounds_subsig(&self, subsig_id: usize,  
		hs:&HashMap<String,Vec<usize>>, hs_igc: &HashMap<String,Vec<usize>>,
		_fname: &str) 
		->(TriVal, usize, usize){
		let pat = &self.vec_subsig_pm_bounds[subsig_id];
		let mut cost = 0;
		let mut cost2 = 0;
		//if pat.len()==0{
			//println!("WARN: pm bounds empty for sig: {}, subsig_id: {}", 
			//	self.to_str(), subsig_id);
			//NO need to return Maybe as it will skip the loop and
			//arr_pos decides the return value
		//}
		let mut arr_pos = vec![0];
		for id in 0..pat.len(){
			let word = &pat[id].0;
			let rg = pat[id].1;
			let allowed = arr_pos.iter().map(|x|{
				let min = if rg.0==usize::MAX {usize::MAX} 
					else {x + rg.0 + word.len()};
				let max = if rg.1==usize::MAX {usize::MAX}
					else {x + rg.1 + word.len()};
				let min = if min>RANGE_MAX {RANGE_MAX} else {min};
				let max = if max>RANGE_MAX {RANGE_MAX} else {max};
				(min,max) 
			}).collect::<Vec<(usize,usize)>>();
			let arr_cur_pos = if self.vec_subsig_obj[subsig_id].b_ignore_case{
				hs_igc.get(word).map_or(vec![], |v| v.to_vec())
			}else{
				hs.get(word).map_or(vec![], |v| v.to_vec())
			};
			cost2+= arr_cur_pos.len();

			let allowed_pos = arr_cur_pos.into_iter().filter(|x|{
				if allowed.len()==0 {return false;}

				//FAST version
				//binary search find the SMALLEST idx s.t. allowd[idx]>=x 
				let mut idx1= 0;
				let mut idx2 = allowed.len()-1;
				let mut idx = (idx1+idx2)/2;

				while idx1<=idx2{
					idx = (idx1+idx2)/2;
					if allowed[idx].0<*x{
						idx1 = idx + 1;
					}else if allowed[idx].0>*x{
						if idx>=1{
							idx2 = idx - 1;
						}else{
							break;
						}
					}else{// = case
						break;
					}
				}
				if idx>allowed.len()-1{
					idx = allowed.len()-1;
				}else{
					if allowed[idx].0>*x && idx>0{
						idx-=1;
					}
				}
				let res = *x>=allowed[idx].0 && *x<=allowed[idx].1;
				//SLOW VERSION
				if B_DEBUG {
					let res2 = allowed.iter().map(|y| *x>=y.0 && *x<=y.1)
						.collect::<Vec<bool>>().into_iter()
						.fold(false, |acc, val| acc || val);
					assert!(res==res2, "FAILED on binary search for range");
				}

				res
			}
			).collect::<Vec<usize>>();
			cost += allowed_pos.len();
			arr_pos = allowed_pos;
		}
		let res = if arr_pos.len()>0 {TriVal::Maybe} else {TriVal::False};
		(res, cost, cost2)
	}

	/// collect bagwords from pmreg (in case it uses different min-len requirement)
	pub fn collect_bagwords_from_pmreg(&self, b_ignore_case: bool) -> HashSet<String>{
		let mut hs_res = HashSet::<String>::new();
		//assert!(self.vec_subsig_pm_bounds.len()>0, "WARN: pm_bounds vec 0: {}", self.name);
		//NO NEED it should be equal to the number of sugsigs
		for (id, vec) in self.vec_subsig_pm_bounds.iter().enumerate(){
			if b_ignore_case != self.vec_subsig_obj[id].b_ignore_case{
				continue;
			}
			for t in vec{
				hs_res.insert(t.0.clone());
			}

		}

		hs_res
	}

	/// collect from the vec_subsig_bagwords
	pub fn collect_all_bagwords(&self, b_ignore_case: bool)->HashSet<String>{
		let mut hs_res = HashSet::<String>::new();
		//1. do it for all bag words
		for (id, hs) in self.vec_subsig_bagwords.iter().enumerate(){
			if b_ignore_case != self.vec_subsig_obj[id].b_ignore_case{
				continue;
			}
			for vec in hs{
				for s in vec{
					hs_res.insert(s.clone());
				}
			}
		}

		//2. do it for all pm-reg
		let hs2 = self.collect_bagwords_from_pmreg(b_ignore_case);
		let hs_res2 = hs_res.union(&hs2).into_iter().cloned().collect::<HashSet<String>>();

		hs_res2
	}

	/// given a sequence of "(a|b...|d) (a|b..|d) ...(....)"
	/// regex, extract the terms and collect the bag of words
	/// so that each bag does not exceed the limit
	/// Return a hashset of bag of words. Each bag is a 
	/// vector of string (union of strings)
	fn extract_bagwords_from_dnf_regex(s: &str, limit: usize)->
		HashSet<Vec<String>>{
		//1. get all unit (...)'s
		let items = find_all(r"\(.*?\)", s);

		//2. collect the number of items in each unit
		let item_lens = (&items).into_iter().map(|x| 
			x.split("|").collect::<Vec<&str>>().len())
			.collect::<Vec<usize>>();

		//3. construct bags
		let mut processed = 0;
		let mut final_res = HashSet::<Vec<String>>::new();
		while processed<item_lens.len(){
			//1. decode how many items to take
			let mut combo_num = item_lens[processed];
			let mut id = processed;
			assert!(item_lens[processed]<=limit, "limit too small!");
			while combo_num<limit && id < item_lens.len(){
				combo_num = if id==processed {item_lens[id]} 
					else {combo_num*item_lens[id]};
				id +=1;
			}
			if combo_num>limit {id-=2;} else {id-=1};

			//2. build up the combinations
			let mut cur_combo = HashSet::<String>::new();
			cur_combo.insert("".to_string());
			for i in processed..id+1{
				let cur_items = find_all(r"[a-f0-9]+", &items[i]);
				let new_combo = (&cur_combo).iter().map(|x| 
					(&cur_items).iter().map(|y| x.to_string()+y).
					collect::<Vec<String>>()
				).flat_map(|z| z).
					collect::<HashSet<String>>();
				cur_combo = new_combo;
			}
			let mut vec_combo = cur_combo.into_iter().map(|x| x).
				collect::<Vec<String>>();
			vec_combo.sort();
			final_res.insert(vec_combo);

			//3. advance
			processed = id+1;
		}

		final_res
	}

	/// generate the bag of words patterns for a given signature
	pub fn gen_approx_patterns_for_sig_old(s: &str, cfg: &ClamavApproxConfig) 
		-> HashSet<Vec<String>>{
		let r1 = Regex::new(r"^\([a-f0-9]*\($").unwrap();
		let r2 = Regex::new(r"^[a-f0-9\(\)\|\.\*\?]*$").unwrap();
		let r3 = r"(\([a-f0-9\|]+\))+";
		let r_word = r"[a-f0-9]+";
		assert!(!r1.is_match(s), "nested ( structure. s: {}", s);
		assert!(r2.is_match(s), "ERROR matching r2. s: {}", s);

		//2. split by long sequences
		let all_par_seq = find_all(r3, s);
		let all_fixed= Regex::new(r3).unwrap().split(s).collect::<Vec<_>>();
		//improve the later, could be done using iterator pattern.
		let mut bags_from_fixed= HashSet::<Vec<String>>::new();
		all_fixed.into_iter().for_each(|s| {
				let vec_words = find_all(r_word, s);
				for word in vec_words{
					bags_from_fixed.insert(vec![word]);
				}
			});
		let bags_from_dnf = all_par_seq.iter().map(|s|
			Self::extract_bagwords_from_dnf_regex(s, cfg.combination_limit)
		).collect::<Vec<_>>().into_iter()
			.flat_map(|vec_s| vec_s).collect::<HashSet<Vec<String>>>();
		let mut bags_both = bags_from_dnf.clone();
		for x in bags_from_fixed {bags_both.insert(x);}
		bags_both.remove(&vec![]);

		bags_both
	}

	/// NEW version which uses regex structure Hir instead.
	pub fn gen_approx_patterns_for_sig_new(s: &str, cfg: &ClamavApproxConfig)
		-> HashSet<Vec<String>>{
		let res = collect_bag_words_from_rustomaton_regex(s, cfg.min_bag_len, cfg.combination_limit);
		/*
		//perform the filtering here
		let res2 = res.iter().map(|v| {
			let mut newv = vec![];
			for x in v {if x.len()>=min_bag_len {newv.push(x.clone());}}
			newv
		}
		).collect::<HashSet<Vec<String>>>();
		let res3 = res2.into_iter().filter(|v| v.len()>0).collect::<HashSet<Vec<String>>>();
		*/
		let res3 = filter_bag_of_words(&res, cfg.min_bag_len);
		res3
	}

	/// generate the bag of words patterns for a given signature
	pub fn gen_approx_patterns_for_sig(s: &str, cfg: &ClamavApproxConfig) -> HashSet<Vec<String>>{
		//let res = Self::gen_approx_patterns_for_sig_old(s);
		let res = Self::gen_approx_patterns_for_sig_new(s, cfg);
		res
	}

	/// extract patterns from the each sub-signature. For each subsignature
	/// it is a CONJUNCTION of BagOfWords, where each Bag is a UNION
	/// of words (meaning any of them satisfying counter constraint would
	/// be ok).
	/// For each sub_sig_obj it has: `HashSet<Vec<String>>` where
	/// each `Vec<String>` is the Bag of Words (union), and the 
	/// HashSet elements (vec of strings) are in the conjunction relation.
	/// For Instance `< [ab, cd], [12, 34] >`, a string "ab34" would
	/// satisfy it but "abab" would not because none of `[12, 34]` appears.
	pub fn gen_approx_bagwords(&mut self, cfg: &ClamavApproxConfig){
		let b_debug = read_global_config().log_level >= LOG6;

		for obj in &self.vec_subsig_obj{
			//0. if obj is not general regex or counter constraint ignore.
			if obj.subsig_type==SubSigType::SubsigCountConstraint{
				self.vec_subsig_bagwords.push( HashSet::<Vec<String>>::new() );
				continue;
			}

			//1. check if it has no nested structure
			assert!(obj.subsig_type==SubSigType::GeneralRegex ||
				obj.subsig_type==SubSigType::CounterConstraint, 
				"type needs to be general regex or counter constraint");
			let s = &obj.real_value;
			let bags_both = Self::gen_approx_patterns_for_sig(s, cfg);

			self.vec_subsig_bagwords.push(bags_both);
		}
		let total_size = self.vec_subsig_bagwords.iter().map(|v| v.len()).sum::<usize>();
		if total_size==0{
			if b_debug{
				println!("WARNING: all empty bag words for sig: {}", self.to_str());
			}
		}
	}

	/// evaluate the subsignature of given id, and it returns
	/// a conservative answer. When it's False or True, it really
	/// means Fralse or True for the real match. Maybe means don't know.
	/// when b_fast is true, use hs, otherwise process s_src
	fn approx_eval_bagwords_subsig(&self, id: usize,  s_src: &Vec<u8>, 
		hs:&HashMap<String,usize>, b_fast: bool)
	->TriVal{
		let text = u8_to_hex(s_src); 
		//NOTE: ignore b_neg (it is ONLY used to flip real_value)
		let subsig = &self.vec_subsig_obj[id];
		let res = match subsig.subsig_type{
			SubSigType::GeneralRegex => self.
				approx_eval_bagwords_subsig_general(id, &text, hs, b_fast),
			SubSigType::CounterConstraint => self.
				approx_eval_bagwords_subsig_counter_constraint(id, &text, hs, b_fast),
			SubSigType::SubsigCountConstraint => {
				let mut cnt_true = 0;
				let mut cnt_maybe= 0;
				let mut _cnt_false= 0;
				for cid in &self.vec_subsig_obj[id].set_subsigs{
					let res = self.approx_eval_bagwords_subsig(*cid, 
						s_src, hs, b_fast);
					match res{
						TriVal::True => cnt_true +=1,
						TriVal::Maybe => cnt_maybe+=1,
						TriVal::False => _cnt_false +=1,
					}
				}
				let min_required = self.vec_subsig_obj[id].min_required;
				let res = if cnt_true>=min_required{ 
					TriVal::True //for sure
				} else if cnt_true + cnt_maybe < min_required{ 
					TriVal::False //for sure
				} else {
					TriVal::Maybe //could be either true or false
				};

				res

			}
		};

		res
	}

	/// given patterns (conjunection of disjunctive bag of words), 
	/// count each conjunected bag appearance in text, and return the
	/// min and max appearance
	fn count_pattern_occ(patterns: &HashSet::<Vec<String>>, text: &str)->(usize, usize){
		let arr_occ = patterns.iter().map(|vec|
			vec.iter().map(|word| count_occ(word, text)).sum()	
		).collect::<Vec<usize>>();
		let minocc = arr_occ.iter().min().expect("vec_occ is empty!");
		let maxocc = arr_occ.iter().max().expect("vec_occ is empty!"); 

		(*minocc, *maxocc)
	}

	/// fast counter mode given the hashmap of occurence of words
	/// return the min:max mode
	fn count_pattern_occ_fast(patterns: &HashSet::<Vec<String>>, 
		hs: &HashMap<String,usize>)->(usize, usize){
		let arr_occ = patterns.iter().map(|vec|
			vec.iter().map(|word| hs.get(word).unwrap_or(&0)).sum()	
		).collect::<Vec<usize>>();
		let minocc = if arr_occ.len()==0 {&0} else {arr_occ.iter().min().expect("vec_occ is empty!")};
		let maxocc = if arr_occ.len()==0 {&0} else {arr_occ.iter().max().expect("vec_occ is empty!")}; 

		(*minocc, *maxocc)
	}

	/// evaluate the occurence of pattern regarding the CompOp
	fn eval_pattern_occ(tuple: &(usize, usize), op: CompOp, val: usize)->TriVal{
		let (minocc, _maxocc) = (tuple.0, tuple.1); //note minocc represents
		// the REQUIRED item with the minocc occurence. 
		// for example, if the minocc < target_value it means that
		// one required item appears less than the required value, it's a false.
		match op{
			CompOp::NONE => {panic!("eval_pattern_occ ERR: op is none")},
			CompOp::GT => if minocc<=val {TriVal::False} else {TriVal::Maybe}, 
			CompOp::LT => if minocc<val {TriVal::True} else {TriVal::Maybe}, 
			CompOp::EQ => if minocc<val {TriVal::False} else {TriVal::Maybe}  
		}
	}

	/// Works by count the total occurence for each bag. 
	/// When unsure, return Maybe
	fn approx_eval_bagwords_subsig_general(&self, id: usize, text: &str,
		hs: &HashMap<String,usize>, b_fast: bool)->TriVal{
		assert!(self.vec_subsig_obj[id].subsig_type==SubSigType::GeneralRegex,
			"subsig needs to be GeneralRegex");
		let _sig = &self.vec_subsig_obj[id].real_value;
		let patterns = &self.vec_subsig_bagwords[id];
		if patterns.len()==0 {
			//println!("WARN: bagwords len is 0 for {}", self.to_str());
			return TriVal::Maybe;
		}
		let occ = if b_fast {Self::count_pattern_occ_fast(patterns, hs)}
			else {Self::count_pattern_occ(patterns, text)};
		let res = Self::eval_pattern_occ(&occ, CompOp::GT, 0);

		res
	}

	/// convert string operator to CompOp
	pub fn strop_to_comp_op(s: &str, target: usize) -> (CompOp, usize){
		match s{
			"=" => (CompOp::EQ, target),
			">" => (CompOp::GT, target),
			"<" => (CompOp::LT, target),
			_ => panic!("cannot handle operator: {}", s)
		}
	}
	/// This is a conservation handling. If not sure, return Maybe
	fn approx_eval_bagwords_subsig_counter_constraint(&self, id: usize, text: &str,
		hs: &HashMap<String,usize>, b_fast: bool)
		->TriVal{
		assert!(self.vec_subsig_obj[id].subsig_type==SubSigType::CounterConstraint, "subsig needs to be ConsterConstraint");
		let sig = &self.vec_subsig_obj[id].value;

		if is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", sig){
			let id = extract_nums(&sig)[0]; 
			let num = extract_nums(&sig)[1]; 
			let sop = find_only(r">|<|=", &sig);
			let (op, num) = Self::strop_to_comp_op(&sop, num);
			let pattern = &self.vec_subsig_bagwords[id];
			if pattern.len()==0 {
				//println!("WARN: bagwords len is 0 for {}", self.to_str());
				return TriVal::Maybe;
			}
			let occ = if b_fast {Self::count_pattern_occ_fast(pattern, hs)}
				else {Self::count_pattern_occ(pattern, text)};
			let res = Self::eval_pattern_occ(&occ, op, num);

			return res;
		}

		panic!("cannot handle subsignaure: {}", sig)
	}

	/// accept using the approximated patterns
	/// the result is conservative. When unsure, return Maybe.
	pub fn accepts_approx_bagwords(&self, s: &Vec<u8>) -> TriVal{
		self.accepts_approx_bagwords_worker(s, 
			&HashMap::<String,usize>::new(), 
			&HashMap::<String,usize>::new(),
			false)
	}

	/// faster mode using accept path stats
	pub fn accepts_approx_bagwords_fast(&self, hs: &HashMap<String,usize>,
		hs_igc: &HashMap<String,usize>) 
	-> TriVal{
		self.accepts_approx_bagwords_worker(&vec![], hs, hs_igc, true)
	}

	/// when b_fast is set, use the hashmap for stats, otherwise
	/// use the string (use the hs or hs_igc correspondingly for
	/// each subsig
	pub fn accepts_approx_bagwords_worker(&self, s: &Vec<u8>, 
		hs: &HashMap<String,usize>, hs_igc: &HashMap<String, usize>,
		b_fast: bool) -> TriVal{
		assert!(self.vec_subsig_obj.len() == self.vec_subsig_bagwords.len(),
			"vec_subsig.len() not matching vec_subsig_bagwords, call gen_approx_bagwords");

		let mut bres = TriVal::True;
		for item in &self.eval_dnf.vec_disjunc{
			let mut item_res = TriVal::False;
			for id in item{
				let res = if !self.vec_subsig_obj[*id].b_ignore_case{
					self.approx_eval_bagwords_subsig(*id,s,hs,b_fast)
				}else{
					self.approx_eval_bagwords_subsig(*id,s,hs_igc,b_fast)
				};
				item_res = item_res | res;
			}

			bres = bres & item_res;
		}

		bres 
	}
	/// internal function: eval pattern and generate score
	fn score(&self, set_pat: &HashSet<String>, 
		map: &HashMap::<String,Vec<String>>) -> usize{
		//1.0 early check
		if set_pat.len()==0 {return 0;}

		//1.1 constants
		let len_limit = 10000000;
		let num_limit = 1000;

		//1.2 compute the min_len and avg_len of the hs_item
		let mut cnt = 0;
		let mut tlen = 0;
		let mut min_len = 100000000;
		for x in set_pat{ 
			if map.contains_key(x) {cnt+=1;} 
			tlen+=x.len(); 
			if x.len()<min_len {min_len = x.len();}
		}

		//1.3 use a heurstics to DISCOURAGE multiple patterns included
		let mut pat_len_heu = set_pat.len() * set_pat.len() /2;
		pat_len_heu = if pat_len_heu>0 {pat_len_heu} else {1};
		let avg_len = if set_pat.len()>0 {tlen/pat_len_heu} else {0};
		let diff_cnt = if num_limit>cnt {num_limit-cnt} else {0};
		let mut score = diff_cnt * len_limit + avg_len;
		const MIN_LEN_BAR:usize = 10; 
		if min_len < MIN_LEN_BAR {
			score = min_len; //NOTE: this only lowers the possibility of
						// short words (because we need to handle 
						// GeneralRegex
		}

		score
	}
	/// internal function: update map function which given max_set and map
	/// updates the map
	fn update_map(&self, max_set: &HashSet<String>, 
		map: &mut HashMap<String,Vec<String>>)  {
		const MIN_LEN_BAR:usize = 10; 
		for x in max_set{
			if x.len()<MIN_LEN_BAR{
				log(0, LOG1, &format!("WARNING: critial pattern: {} in {} is short!", &x, &self.name));
			}
		}
		for pat in max_set{
			assert!(pat.len()>0, "sig: {} has empty str as critical pattern, max_set: {:#?}", self.name, max_set);
			match map.entry(pat.clone()){
				Entry::Vacant(e) => {e.insert(vec![self.name.clone()]);},
				Entry::Occupied(mut e) => {
					e.get_mut().push(self.name.clone());
				}
			}
		}//end for
	}

	/// If the set of critical patterns contains ""
	/// it implies that one of the required subsigs has NO appropriate
	/// critical pattern (either because of too short <min_bag_len, as
	///   critical_pat extraction extractoin reuses bag_words extraction),
	/// or other situations like special counter constraints which blindly
	/// fails critical pat test.
	///
	/// An example below:
	/// the last (#4): no fixed string long enough
	/// it generates "" as critical pattern for subsig while
	/// 0,1,2 have valud ones. But given the subsigs 3 and 4 are
	/// connected using disjunction: their critical pattern is
	/// INDEED NEEDed to discharge. In this case, the signature
	/// CANNOT be discharged via critical section.
	/// --  "Trojan.Agent-1388728;Engine:51-255,Target:1;(0&1&2)|3|4;726563646973636d33322e657865;5c5c25735c736861726564245c737973776f773634;5c5c25735c736861726564245c73797374656d3332;8D??????5?687E6604805?E8????????8D??????6A105?5?E8????????8B????????????8D??????5?8D??????6A005?6A006A0089??????89??????89??????C7??????????????E8????????33??5?85C00F9F??8B??E8;E8????????8B??E8????????0FAF??E8????????0FAF??9933??2B??33??F7??8B??5?E8"
	/// -----
	/// There are other cases that counter constraint is set to =0
	/// which blindly fails crit pat approach as well.
	/// in this case the max_set will have "" inside it as well.
	#[inline(always)]
	fn is_bad_critical_pat(pat: &HashSet<String>)->bool{
		pat.contains(&("".to_string()))
	}

	/// collect the criticical patterns from the subsignatures
	/// try avoid duplicate patterns as much as possible
	/// insert the pattern and its mapping to the signame
	/// map is for case_sensitive, map_igc is for case-ignore
	/// When checking critical patterns, will make two separate
	/// checks using two ACDFAs. If none of the patterns included
	/// in the 2 critical pattern sets (case sensitive and ignore-case)
	/// the pattern is discharged. 
	/// NOTE: for a subsignature a critical pattern is a collection of
	/// strings, if none of the words from the critical pattern appear, it
	/// discharges the subsignature.
	/// E.g., for subsignature ".*abc.*123", the critical pattern could
	/// contain both "abc" and "123". But in practice "abc" is good enough
	/// to discharge the subsig. But for subsignature ".*(abc|123).*",
	/// the critical pattern should contain both "abc", "123".
	/// This function modifies a map which maps from the words (such as "123")
	/// to the SIGNATURE (not subsignature) it triggers. It does consider the
	/// DNF structure of subsignatures.
	///
	/// RETURN: true means ok, false means no critical pattern can be
	/// found thus the signature HAS TO  enter next round of check (e.g., bag
	/// of words or SED/PM)
	pub fn add_critical_pattern(&self, map: &mut HashMap::<String,Vec<String>>,
		map_igc: &mut HashMap<String,Vec<String>>)->bool{

		//3. MAIN LOGIC:
		// process each disjunctive item (just need to pick ONE result LATER)
		let mut vec_all = vec![];
		for item in &self.eval_dnf.vec_disjunc{
			let mut hs_item_cs = HashSet::<String>::new(); //case sensitive
			let mut hs_item_igc = HashSet::<String>::new(); //ignore case
			//note that need to collect ALL of disjuncted item
			//so that if none appear, the signature can be NOT processed
			//if ONE of them appear, the signature NEEDS to be processed
			for id in item{
				let subtype = &self.vec_subsig_obj[*id].subsig_type;
				if *subtype==SubSigType::SubsigCountConstraint{
					//as it's union type
					//should include CRITICAL SECTION of all UNION subsigs
					for cid in &self.vec_subsig_obj[*id].set_subsigs{
						let stype = &self.vec_subsig_obj[*cid].subsig_type;
						assert!(*stype==SubSigType::GeneralRegex ||
							*stype==SubSigType::CounterConstraint, 
							"subtype is not general regex or counter cons");
						let hs = self.vec_subsig_obj[*cid]
							.get_critical_pattern(*cid, &map, 
							&self.vec_subsig_obj, &self.vec_subsig_bagwords);
						if self.vec_subsig_obj[*cid].b_ignore_case{
							for x in hs {hs_item_igc.insert(x);}
						}else{
							for x in hs {hs_item_cs.insert(x);}
						}
					}
				}else{
					assert!(*subtype==SubSigType::GeneralRegex ||
						*subtype==SubSigType::CounterConstraint, 
						"subsigtype is not general regex or counter cons");
					let hs = self.vec_subsig_obj[*id]
						.get_critical_pattern(*id, &map, &self.vec_subsig_obj, &self.vec_subsig_bagwords);
					if self.vec_subsig_obj[*id].b_ignore_case{
						for x in hs {hs_item_igc.insert(x);}
					}else{
						for x in hs {hs_item_cs.insert(x);}
					}
				}
			}
			//this is the patterns for ONE DNF item
			//e.g., for the "0|1" in (then patterns for BOTH subsignatures
			//0 and 1 ARE required. But they'll compute the ones for (2|3)
			//because ONLY either critical patterns for (0|1) & (2|3)
			//would be needed for discharging.
			// (0|1) & (2|3)
			vec_all.push( (hs_item_cs, hs_item_igc) ); 
		}

		//3. make the choice of all available options based on DNF.
		let mut max_id = 0;
		let mut max_score = 0;
		let mut id = 0;
		for set_pat in &vec_all{
			let (hs_item_cs, hs_item_igc) = (&set_pat.0, &set_pat.1);
			let score1 = self.score(hs_item_cs, map);
			let score2 = self.score(hs_item_igc, map_igc);
			let total_score = score1+ score2;
			if total_score>=max_score{
				max_score = total_score;
				max_id = id;
			}
			id +=1;
		}
		let max_set_cs = &vec_all[max_id].0;
		let max_set_igc = &vec_all[max_id].1;
		if !Self::is_bad_critical_pat(&max_set_cs) && 
			!Self::is_bad_critical_pat(&max_set_igc){
			self.update_map(&max_set_cs, map);
			self.update_map(&max_set_igc, map_igc);
			return true;
		}else{//note just set it to false
			return false;
		}
	}


	/// try to measure the size of all subsig DFA
	/// if success, return a vector with the same size of number of
	/// subvectors, otherwise return false.
	pub fn measure_dfa_size(&self, timeout_sec: usize,cfg: &ClamavApproxConfig)->(String, bool, Vec<usize>){
		let (sender, receiver) = mpsc::channel();
		let mut obj = self.clone();
		let cfg = cfg.clone();
		let _t = thread::spawn(move ||{
			obj.gen_approx_bagwords(&cfg);
			obj.gen_approx_pm_bounds(&cfg);
			obj.set_vec_automaton(&cfg);
			let mut res = vec![];
			for x in obj.vec_subsig_automaton{
				res.push( x.transitions.len() );
			}
			match sender.send(res){
				Ok(()) => {},
				Err(_)=>{}
			}
		});

		let res = receiver.recv_timeout(Duration::from_millis((
			timeout_sec as u64)*1000));
		if !res.is_err(){
			return (self.name.clone(), true, res.unwrap());
		}else{
			return (self.name.clone(), false, vec![]);
		}
	}

	/// Convert to Automataon (of the negated formula)
	/// E.g., for `(0|1) & (2|3)` will evaluate
	/// `(not 0 \and not 1) | (not 2 and not 3)`
	/// if the NFA is too big, try converting each item
	/// to a vectof of vector: e.g.,
	/// `[ [not 0, (and) not 1], [not 2, (and) not 3] ]` (or relation
	/// in between).
	/// return (b_success, b_complex, `Vec<Vec<NFA>>`). If it's type 1,
	/// b_complex is set to false, and the ONLY DFA is placed
	/// as the ONLY ONE element of the 2d vector
	pub fn to_neg_automaton(&self, timeout_sec: usize)
		->(bool, bool, Vec<Vec<NFA<char>>>, String){
		let log_level = LOG2;
		log(0, log_level, &format!("TO automaton{:?}: Attempt 1: single NFA", 
			self.name));
		log(0, log_level+1, &format!("DETAILS: {:?}", self));
		let (sender, receiver) = mpsc::channel();
		let obj = self.clone();
		let _t = thread::spawn(move ||{
			let mut timer = Timer::new();
			let mut nfa = empty_nfa();
			//Note: conjunctions of list of DISJUNCTIONS!
			//Then to compute its NEGATION: Disjunctions of CONJUNCTIONS!
			for item_id in 0..obj.eval_dnf.vec_disjunc.len(){
				let item = &obj.eval_dnf.vec_disjunc[item_id];
				log(0, log_level+1, &format!("--- Processing item: {:?}", &item));
				let mut item_nfa = empty_nfa();
				for i in 0..item.len(){
					let id = item[i];	
					let cur_nfa= build_nfa(&obj.vec_subsigs[id], obj.vec_bneg[id]);
					log(0, log_level+1, &format!("---- ---- Handle id: {}, expr: {}, b_neg: {}, resulting dfa size: {:?}", id, obj.vec_subsigs[id], obj.vec_bneg[id], size_nfa(&cur_nfa)));
					item_nfa = if i==0 {cur_nfa.clone()} else {item_nfa.unite(cur_nfa)};
					//dfa = dfa.minimize_hop();
					log(0, log_level+1, &format!("---- ----  UNITING NFA => {:?}", size_nfa(&item_nfa)));
				}
				log(0, log_level+1, &format!("---- BEFORE NEGATE NFA size: {:?}", size_nfa(&item_nfa)));
				let item_nfa = item_nfa.negate();
				log(0, log_level+1, &format!("---- AFTER NEGATE Item {:?} => NFA: {:?} \n", &item, size_nfa(&item_nfa)));
				nfa = if item_id==0 {item_nfa} else {nfa.unite(item_nfa)}; 
				log(0, log_level+1, &format!("---- AFTER UNITE DNF automata => NFA: {:?} \n", size_nfa(&nfa)));
			}
			log_perf(0, log_level, &format!("FINAL SIZE of NFA_easy: {}: {:?}", &obj.name, size_nfa(&nfa)), &mut timer);
			let vec_res = vec![vec![nfa]];
			match sender.send(vec_res){
				Ok(()) => {},
				Err(_) => {}
			}
		});

		let res = receiver.recv_timeout(Duration::from_millis((timeout_sec as u64)*1000));
		if !res.is_err() {
			let vec_res = res.unwrap();
			return (true, false, vec_res, self.name.clone());
		}

		//2. try step two  DISJUNCTION of CONJUNCTION OF A LOT DFA
		log(0, log_level, &format!("Attempt 2: Disjunction of Conjunction of DFA"));
		let (sender, receiver) = mpsc::channel();
		let obj = self.clone();
		let _t = thread::spawn(move ||{
			let mut timer = Timer::new();
			let mut vec_res = vec![];
			for item_id in 0..obj.eval_dnf.vec_disjunc.len(){
				let mut vec_dfa = vec![];
				let item = &obj.eval_dnf.vec_disjunc[item_id];
				log(0, log_level, &format!("--- Processing item: {:?}", &item));
				for i in 0..item.len(){
					let id = item[i];
					//note: already negated
					let cur_dfa= build_nfa(&obj.vec_subsigs[id], !obj.vec_bneg[id]);
					log(0, log_level, &format!("---- ---- Handle id: {}, expr: {}, b_neg: {}, resulting negated dfa size: {:?}", id, obj.vec_subsigs[id], obj.vec_bneg[id], size_nfa(&cur_dfa)));
					vec_dfa.push(cur_dfa);
				}
				log(0, log_level, &format!("--- vec_dfa size: {}", vec_dfa.len()));
				vec_res.push(vec_dfa);
			}
			log_perf(0, log_level, &format!("FINAL SIZE of NFA_complex: {}: {:?}", &obj.name, get_total_size(&vec_res)), &mut timer);
			match sender.send(vec_res){
				Ok(()) => {},
				Err(_) => {}
			}
		});
		let res = receiver.recv_timeout(Duration::from_millis(
			(timeout_sec as u64)*1000));
		match res{
			Ok(vec_res) => {(true, true, vec_res, self.name.clone())},
			Err(_) => {(false, true, vec![vec![]], self.name.clone())}
		}
	}

	/// return precedence of char
	fn precedence(c: char)->usize{
		match c{
			'&' => 1,
			'|'=> 2,
			')'=> 0,
			'('=> 0,
			_=> panic!("unknown operator: {}", c)
		}
	}

	/// use infix evaluation of expr
	fn gen_eval_dnf(&mut self){
		let log_level = LOG6;
		log(0, log_level, &format!("gen_eval_dnf: {}", self.expr));
		let mut stack_operator = VecDeque::<char>::new();
		let mut stack_operands = VecDeque::<EvalDNF>::new();
		let chars:Vec<char> = self.expr.chars().into_iter().collect();
		let n = chars.len();
		let mut i = 0;
		while i<n{
			let c = chars.get(i).unwrap().clone();
			if c.is_digit(10){//read all digits
				let mut s_n = String::from("");
				let mut j = i;
				while j<n{
					let c2 = chars.get(j).unwrap().clone();
					if c2.is_digit(10) {s_n.push(c2);}
					else{
						break;
					}
					j += 1;
				} // j is either a non-digit, or n
				i = j-1; //because it will be increased by 1 later
				let num = s_n.parse::<usize>().unwrap();
				let dnf = EvalDNF::new(num);
				stack_operands.push_back(dnf);
			}else if c=='('{
				stack_operator.push_back('(');
			}else if c==')'{
				while *stack_operator.back().unwrap()!='('{
					Self::one_op(&mut stack_operator, &mut stack_operands);
				}
				stack_operator.pop_back(); //pop the '('
			}else if c=='&' || c=='|'{
				while !stack_operator.is_empty() &&
				  Self::precedence(*stack_operator.back().unwrap())
				  	>=Self::precedence(c){
					Self::one_op(&mut stack_operator, &mut stack_operands);
				}
				stack_operator.push_back(c);
			}else{
				panic!("gen_dnf_eval cannot handle: {}", c);
			}
			i += 1;
		}
		while !stack_operator.is_empty(){
			Self::one_op(&mut stack_operator, &mut stack_operands);
		}
		assert!(stack_operands.len()==1, "stack_operands.len!=1, dump: {:?}", self);
		self.eval_dnf = stack_operands.pop_back().unwrap();
		log(0, log_level, &format!("gen_eval_dnf RESULT: {:?}", self.eval_dnf));
	}

	/// perform ONE operator, and change the stacks, assuming
	/// stack always have proper number of operands and operators
	fn one_op(stack_operator: &mut VecDeque::<char>, 
		stack_operands: &mut VecDeque::<EvalDNF>){
		let op = stack_operator.pop_back().unwrap();
		let b = stack_operands.pop_back().unwrap();
		let a = stack_operands.pop_back().unwrap();
		match op{
			'&' => { 
				let res = a.and(&b);
				stack_operands.push_back(res);
			},
			'|' => {
				let res = a.or(&b);
				stack_operands.push_back(res);
			}
			_ => panic!("unknown operator: {}", op)
		}
	}

	/// validate the given sub-signature is a SINGLE PATTERN word
	fn validate_subsig_single_pattern(&self, id: usize){
		let hay = &self.vec_subsigs[id];
		let res = is_match(r"^(\.\*)?[a-f0-9]+\.\*$", hay);
		assert!(res, "subsig: {} not a single pattern word", hay);
	}

	// based on id sop num (e.g., id<5), generate the extracted patterns
	fn extract_rel_pat(sop: &str, num: usize, pat: &str, 
		_subexp: &str) -> (bool, String){
		let (b_res, new_str) = if sop=="=" {
			if num==0{ 
				(true, pat.to_string() + &".*")
			}else{
				(false, pat.repeat(num) + ".*") 
			}
		}else if sop=="<" {
			(true, pat.repeat(num) + ".*")
		}else if sop==">"{
			(false, pat.repeat(num+1) + ".*")
		}else{
			panic!("cannot find either of =, <, > ops")
		};
		(b_res, new_str)
	}
	/// To extract expressions like "0>5", "1=0" to add new subsigs
	/// These ops are pushed as extra signatures on counters
	/// these counter signatures will be stored in vec_subsig_objs
	/// Require that subsignature involved be ONE single pattern word
	/// The output will generate the vec_subsib_obj
	/// if b_pm is set, check all subsignatures has simplified single pattern
	/// (i.e., no class chars, no union class etc.)
	fn preprocess_expr_new(&mut self, b_pm: bool){
		//0. make a copy of all existing subsigs
		let log_level = LOG6;
		let mut vec_sig_obj= vec![];
		for (id,x) in self.vec_subsigs.iter().enumerate(){
			vec_sig_obj.push( SubSigObj{value: x.clone(),
				subsig_type: SubSigType::GeneralRegex,
				real_value: x.clone(),
				b_ignore_case: !self.vec_bcase_sensitive[id],
				set_subsigs: HashSet::<usize>::new(),
				min_required: 0,
				});
		}


		//1. process "id=num or id<num or id>num or id==num" case
		log(0, log_level, &format!("preprocess_expr_pm: name: {}, expr: {}", self.name, self.expr));
		let mut sexpr2 = String::from(&self.expr);
		for subexp in find_all(r"\d+( *)(=|<|>|==)( *)\d+", &self.expr){
			let id = extract_nums(&subexp)[0]; 
			let num = extract_nums(&subexp)[1]; 
			let sop = find_only(r">|<|=", &subexp);
			if b_pm {self.validate_subsig_single_pattern(id);}
			let pat = drop_last_dotstar(&self.vec_subsigs[id]);
			let (b_neg, r_val) = Self::extract_rel_pat(
				&sop, num, &pat, &subexp);
			self.vec_bneg.push(b_neg);
			let newid = vec_sig_obj.len(); 
			let b_igc = !self.vec_bcase_sensitive[id];
			let newobj = SubSigObj{value: subexp.clone(), subsig_type: SubSigType::CounterConstraint, real_value: r_val, b_ignore_case: b_igc,
				set_subsigs: HashSet::<usize>::new(),
				min_required: 0,
			}; 
			vec_sig_obj.push(newobj);
			sexpr2 = sexpr2.replace(&subexp, 
				&format!("{}",newid));
		}

		//3. process "(id1|id2|id3...|idn)>x,y" case or < or = cases
		// handle the SubexprCounter constraint. 
		// semantics (check type_def.rs regarding min_quired)
		// NOTE this also has a BRANCH to handle the 
		//    (id1|...|idn)>x case, which is easier
		// 
		// Consider the SubsigCountConstraint example
		// e.g. (2|3|4)>4,2 requires at least 5 matches and
		// 2 distinct subsignatures. 
		// Here we have to actually generate 2 new subsigs
		// 1st new subsig: SubsigCountConstraint with vec_components 2,3,4
		//   with min_required 2 Let it the new ID be 9
		// 2nd new subsig: rewrite (2|3|4)>4 as one
		// subsig (content of 2|content of 3|content of 4)>4
		// Then this subexp is replaced y the conjunection of the above
		// two subsig.
		for subexp in find_all(r"\(\d+(\|\d+)+\)( *)(>|=|<)( *)(\d+)(,\d+)?", &self.expr){
			//4.1. initial set up extract 
			// e.g. (2|3|4)>4,2
			// "4 "is stored in num, ">" in sop and 2 in min_required
			let old_subexp = subexp.clone();
			let arr = split(&subexp, ",");
			let subexp= &arr[0];
			let nums = extract_nums(&subexp);
			let ids = &nums[0..nums.len()-1];
			let _num = nums[nums.len()-1]; 
			let _sop = find_only(r">|<|=", &subexp);
			let mut _newexpr = String::from("(");
			let b_subsig_count = old_subexp.contains(",");
			let mut set_subsigs = HashSet::<usize>::new();

			if !b_subsig_count{//NO SubsigCountConstraint
				// pure (id1|...|idn)>x case
				let old_subexp = subexp.clone();
				let nums = extract_nums(&subexp);
				let ids = &nums[0..nums.len()-1];
				let num = nums[nums.len()-1]; 
				let sop = find_only(r">|<|=", &subexp);
				let mut newexpr = String::from("(");
				let mut b_first = true;
				let mut set_subsigs = HashSet::<usize>::new();
				for id in ids{
					if b_pm { self.validate_subsig_single_pattern(*id);}
					let newstr = format!("{}{}{}", id, sop, num);
					let newid = vec_sig_obj.len();
					let pat = drop_last_dotstar(&self.vec_subsigs[*id]);
					let (b_neg, r_val) = Self::extract_rel_pat(&sop, 
						num, &pat, &newstr);
					let b_igc = !self.vec_bcase_sensitive[*id];
					let newobj = SubSigObj{value: newstr.clone(), subsig_type: SubSigType::CounterConstraint, real_value: r_val, b_ignore_case: b_igc,
						set_subsigs: HashSet::<usize>::new(),
						min_required: 0,
					}; 
					vec_sig_obj.push(newobj);
					set_subsigs.insert(vec_sig_obj.len()-1);
					self.vec_bneg.push(b_neg);
					let newitem = if b_first {format!("{}", newid)} else {format!("|{}",newid)};
					newexpr = newexpr + &newitem;
					b_first = false;
				}
				newexpr = newexpr + ")";
				sexpr2 = sexpr2.replace(&old_subexp, &newexpr);
			}else{//THE SubsigCountConstraint case.
				assert!(b_subsig_count, "ERROR: expecting SubsigCountConstraint!");
				assert!(arr.len()>1);
				//4.2 build the SubsigCounterObj
				let min_required:usize = arr[1].parse::<usize>().unwrap();
				for id in ids{
					if b_pm { self.validate_subsig_single_pattern(*id);}
					set_subsigs.insert(*id);
				}
				let newobj = SubSigObj{value: old_subexp.clone(), subsig_type: SubSigType::SubsigCountConstraint, real_value: old_subexp.clone(), b_ignore_case: false, set_subsigs: set_subsigs, min_required: min_required};
				vec_sig_obj.push(newobj.clone());
				let newid = vec_sig_obj.len()-1;
				sexpr2 = sexpr2.replace(&old_subexp, &format!("{}", newid));

				// HERE WE SKIP the subsig contents processing here.
				// Mainly for saving development cost as the pasted
				// component subsig contents have to go through pre-processing
				// again, which is hard to re-factor here.
				// Thus the result here is CONSERVATIVE APPROXIMATED
				// That is: it may report FALSE-POSITIVE.
				//e.g., consider (1|2)>100, 2
				// if there is a match of both subsig 1 and 2, it
				// will be reported as a match (ignoring the counting of 100).
				// We run the real data and linux binexec samples all
				// pass without FALSE-POSITIVES caused by this check.
				// leave it for future work.
				//4.3  build the repeate subsig by pasting contents of subsigs
				/*
				for id in ids{
					if b_pm { self.validate_subsig_single_pattern(*id);}
					let newstr = format!("{}{}{}", id, sop, num);
					let newid = vec_sig_obj.len();
					let pat = drop_last_dotstar(&self.vec_subsigs[*id]);
					let (b_neg, r_val) = Self::extract_rel_pat(&sop, 
						num, &pat, &newstr);
					let b_igc = !self.vec_bcase_sensitive[*id];
					let newobj = SubSigObj{value: newstr.clone(), subsig_type: SubSigType::CounterConstraint, real_value: r_val, b_ignore_case: b_igc,
						set_subsigs: HashSet::<usize>::new(),
						min_required: 0,
					}; 
					vec_sig_obj.push(newobj);
					set_subsigs.insert(vec_sig_obj.len()-1);
					self.vec_bneg.push(b_neg);
					let newitem = if b_first {format!("{}", newid)} else {format!("|{}",newid)};
					newexpr = newexpr + &newitem;
					b_first = false;
				}
				newexpr = newexpr + ")";
				if !b_subsig_count{
					sexpr2 = sexpr2.replace(&old_subexp, &newexpr);
				}else{
					let newobj = SubSigObj{value: old_subexp.clone(), subsig_type: SubSigType::SubsigCountConstraint, real_value: old_subexp.clone(), b_ignore_case: false, set_subsigs: set_subsigs, min_required: min_required};
					vec_sig_obj.push(newobj.clone());
					let newid = vec_sig_obj.len()-1;
					sexpr2 = sexpr2.replace(&old_subexp, &format!("{}", newid));
				}
				*/
			}//end the handling of SubsigCountConstraint Case

		}

		//5. process "(id1&id2&id3...&idn)>x" case or < or = cases
		for subexp in find_all(r"\(\d+(\&\d+)+\)( *)(>|=|<)( *)(\d+)(,\d+)?", &self.expr){
//			if find_all(",", &subexp).len()>0{
//				println!("WARNING : expressions such as (0&2&4)>1,3 makes no sense. Details: {}", &subexp);
//			}

			let old_subexp = subexp.clone();
			let arr = split(&subexp, ",");
			let subexp= &arr[0];
			let nums = extract_nums(&subexp);
			let ids = &nums[0..nums.len()-1];
			let num = nums[nums.len()-1]; 
			let sop = find_only(r">|<|=", &subexp);
			let mut newexpr = String::from("(");
			let mut b_first = true;
			for id in ids{
				if b_pm {self.validate_subsig_single_pattern(*id);}
				let newstr = format!("{}{}{}", id, sop, num);
				let newid = vec_sig_obj.len(); 
				let pat = drop_last_dotstar(&self.vec_subsigs[*id]);
				let (b_neg, r_val) = Self::extract_rel_pat(&sop, 
					num, &pat, &newstr);
				let b_igc = !self.vec_bcase_sensitive[*id];
				let newobj = SubSigObj{value: newstr.clone(), subsig_type: SubSigType::CounterConstraint, real_value: r_val, b_ignore_case: b_igc,
				set_subsigs: HashSet::<usize>::new(),
				min_required: 0,
				}; 
				vec_sig_obj.push(newobj);
				self.vec_bneg.push(b_neg);
				let newitem = if b_first {format!("{}", newid)} else {format!("&{}",newid)};
				newexpr = newexpr + &newitem;
				b_first = false;
			}
			newexpr = newexpr + ")";
			sexpr2 = sexpr2.replace(&old_subexp, &newexpr);
		}

		//6. validate the rest of expression are ok
		validate_expr(&sexpr2, &self.name);
		self.expr = sexpr2;
		self.vec_subsig_obj = vec_sig_obj;
		log(0, log_level, &format!("preprocess_expr COMPLETED: name: {}, expr: {}", self.name, self.expr));

	}

}


impl fmt::Debug for EvalDNF{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result{
		write!(f,"[").unwrap();
		for i in 0..self.vec_disjunc.len(){
			if i>0 {write!(f, "&").unwrap();}
			let item = &self.vec_disjunc[i];
			write!(f, "<").unwrap();
			for j in 0..item.len(){
				if j>0 {write!(f, "|").unwrap();}
				write!(f, "{}", item[j]).unwrap();
			}
			write!(f, ">").unwrap();
		}
		write!(f,"]").unwrap();
		Ok(())
	}
}
impl EvalDNF{
	/// constructor
	pub fn new(token_id: usize)->EvalDNF{
		EvalDNF{ vec_disjunc: vec![vec![token_id]] }
	}

	/// or with another DNF
	pub fn or(&self, other: &EvalDNF)->EvalDNF{
		let mut set = HashSet::<Vec<usize>>::new();
		for item1 in &self.vec_disjunc{
			for item2 in &other.vec_disjunc{
				let new_item = Self::union_vecs(&item1, &item2);
				set.insert(new_item);
			}
		}
		let mut res: Vec<Vec<usize>> = set.into_iter().collect();
		res.sort();
		EvalDNF{ vec_disjunc:res}
	}

	/// logical and with another DNF (easy) just 
	/// merge the list
	pub fn and(&self, other: &EvalDNF)->EvalDNF{
		let set1:HashSet<Vec<usize>> = self.vec_disjunc.iter().cloned().collect();
		let set2:HashSet<Vec<usize>> = other.vec_disjunc.iter().cloned().collect();
		let set3 = set1.union(&set2);
		let mut res:Vec<Vec<usize>> = set3.into_iter().cloned().collect();
		res.sort();
		EvalDNF{vec_disjunc: res}
	}

	/// union the two vectors and remove duplicates
	fn union_vecs(vec1: &Vec<usize>, vec2: &Vec<usize>)->Vec<usize>{
		let set1:HashSet<usize> = vec1.iter().cloned().collect();
		let set2:HashSet<usize> = vec2.iter().cloned().collect();
		let set3 = set1.union(&set2);
		let mut res:Vec<usize> = set3.into_iter().cloned().collect();
		res.sort();
		res
	}
}

/// filter a hashmap by the set of given keys
pub fn	filter_by(hs: &HashMap<String,Vec<usize>>, set: &HashSet<String>) 
->HashMap<String,Vec<usize>>{
		let mut res = HashMap::<String,Vec<usize>>::new();
		for (k,v) in hs{
			if set.contains(k){
				res.insert(k.clone(),v.clone());
			}
		}
		res
}


/// QUICK_MODE (without generating proof) discharge file by 
/// five approaches: crit_pattern, bag, and pm_reg (SED), 
/// DFA and individual pm_reg (ISED).
/// Return the FailDischargeRecord.
/// NOTE that all three approaches are discharged directly.
/// ONLY when the first three is NOT effective, the remaining
/// signatures are discharged by DFA.
/// NOTE: when b_optimize_pm is set, if it's already discharged by BAG approach
/// it's automatically filtered.
///
/// To save memory, we do not save DFA for each signature.
/// When calling load_discharge_data (in driver.rs), pass
/// a HashSet of signatures that NEED to generate DFA.
/// The function will crash if the DFA does not exist, then modify
/// the hashset to load_discharge_data correspondingly.
///
/// WE NOW disable the bag_of_words and independent SED approach.
#[allow(dead_code)]
pub fn quick_discharge_file_by_crit_bag_pm_old(fname: &str,
	nibbles: &Vec<u8>, 
	v_sigs: &Vec<Arc<ClamavSig>>,
	vec_sigs_no_crit_pat: &Vec<Arc<ClamavSig>>,
	map_crit_pat: &HashMap<String, Vec<String>>,
	map_crit_pat_igc: &HashMap<String, Vec<String>>,
	dfa_crit: &HexACDFA, dfa_bag: &HexACDFA,
	dfa_crit_igc: &HexACDFA, dfa_bag_igc: &HexACDFA,
	b_optimize_pm: bool, cfg: &ClamavApproxConfig
	)->(FailDischargeRecord, WordInfo){
	let b_include_bs = false;

	//1. process by critical pattern
	let pats_crit = dfa_crit.get_patterns(&dfa_crit.acc_path(&nibbles));
	let pats_crit_igc = dfa_crit_igc.get_patterns( 
		&dfa_crit_igc.acc_path(&nibbles));
	let mut set_sigs_crit = HashSet::<String>::new();
	for pat in pats_crit{
		let vec1 = map_crit_pat.get(&pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for pat in pats_crit_igc{
		let vec1 = map_crit_pat_igc.get(&pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for s in vec_sigs_no_crit_pat{ //add those for sure will FAIL crit_sec
		set_sigs_crit.insert(s.as_ref().name.clone());
	}
	
	//2. process by bag of words
	let v_sigs_failed_crit = v_sigs.into_iter().filter(|x| set_sigs_crit.contains(&x.name)).
		map(|v| v.clone()).
		collect::<Vec<Arc<ClamavSig>>>();
	let dfa_acc_path = dfa_bag.acc_path(&nibbles);
	let hs= dfa_bag.get_pattern_stats(&dfa_acc_path);
	let dfa_acc_path_igc = dfa_bag_igc.acc_path(&nibbles);
	let total_unique_states = dfa_acc_path.par_iter().map(|&s|
		s).collect::<HashSet<usize>>().len()
			+ dfa_acc_path_igc.par_iter().map(|&s| s)
		.collect::<HashSet<usize>>().len();

	let hs_igc= dfa_bag_igc.get_pattern_stats(&dfa_acc_path_igc);
	let mut set_sigs_bag = HashSet::<String>::new();
	let v_sigs_failed_bag = if b_include_bs{
		let v_sigs_to_discharge = if b_optimize_pm {v_sigs_failed_crit.to_vec()} else {v_sigs.to_vec()};
		for sig in v_sigs_to_discharge{
			let res = sig.accepts_approx_bagwords_fast(&hs, &hs_igc);
			if res==TriVal::Maybe || res==TriVal::True{
				set_sigs_bag.insert( sig.name.clone() );
			}
		}
		let v_sigs_failed_bag = v_sigs.into_iter().filter(|x| set_sigs_bag.contains(&x.name)).
			map(|v| v.clone()).
			collect::<Vec<Arc<ClamavSig>>>();
		v_sigs_failed_bag
	}else{
		v_sigs_failed_crit.to_vec()
	};
	let set_sigs_bag: HashSet::<String> = if b_include_bs{set_sigs_bag}
		else {set_sigs_crit.clone()}; 
	
	//3 process by pm bounds
	let pats_failed_bag = (&v_sigs_failed_bag).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>();
	let pats_failed_bag_igc = (&v_sigs_failed_bag).into_iter().map(|s| 
			s.collect_all_bagwords(true)).flat_map(|s| s).
			collect::<HashSet<String>>();
	let hs_occ_old = dfa_bag.get_pattern_pos(&dfa_acc_path);
	let hs_occ_igc_old = dfa_bag_igc.get_pattern_pos(&dfa_acc_path_igc);
	let hs_occ = if b_optimize_pm {filter_by(&hs_occ_old, &pats_failed_bag)} else {hs_occ_old.clone()};
	let hs_occ_igc = if b_optimize_pm {filter_by(&hs_occ_igc_old, &pats_failed_bag_igc)} else {hs_occ_igc_old.clone()};


	let sum_vec_size = |hs: &HashMap<String,Vec<usize>>| -> usize{
		hs.into_iter().map(|(_,v)| v.len()).sum::<usize>()
	};
	let mut set_sigs_pm = HashSet::<String>::new();
	let _bags_failed = v_sigs_failed_bag.len();
	let v_sigs_pm = if b_optimize_pm {v_sigs_failed_bag} else {v_sigs.to_vec()};
	//represents the total length of all layer traces of the pm-reg approach
	let mut total_pm_witness_len = 0; 
	for sig in &v_sigs_pm{
		//1. apply another layer of filter
		let bag_pm = sig.collect_bagwords_from_pmreg(false); 
		let bag_pm_igc = sig.collect_bagwords_from_pmreg(true);

		//2. collect the stats
		let hs_occ_new = if b_optimize_pm {filter_by(&hs_occ, &bag_pm)} else {hs_occ.clone()};
		let hs_occ_igc_new = if b_optimize_pm {filter_by(&hs_occ_igc, &bag_pm_igc)} else {hs_occ_igc.clone()}; 
		//println!("DEBUG USE 302: hs_occ: {} => {}, sum_vec(hs_occ): {} -> {}", hs_occ.len(), hs_occ_new.len(), sum_vec_size(&hs_occ), sum_vec_size(&hs_occ_new));

		//3. filter by the new one
		let (res,info)= sig.accepts_approx_pm_bounds(
			&hs_occ_new, &hs_occ_igc_new, fname);
		let info = info.unwrap(); //will always succeed 
		total_pm_witness_len += info.min_cost;
		if res ==TriVal::Maybe || res==TriVal::True{
			set_sigs_pm.insert( sig.name.clone() );
		}
	}
	let total_acc_path_len = dfa_acc_path.len() + dfa_acc_path_igc.len();
	let total_hs_size = hs_occ.len() + hs_occ_igc.len();
	let total_accepted = sum_vec_size(&hs_occ) + sum_vec_size(&hs_occ_igc);

	//4. process by dfa
	let set_sigs = set_sigs_crit.clone().intersection(&set_sigs_bag).cloned().
		collect::<HashSet<String>>().intersection(&set_sigs_pm).cloned().
		collect::<HashSet<String>>();
	let dfa_sigs = v_sigs.iter().filter(|s| set_sigs.contains(&s.name)).
		map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();
	let set_dfa = dfa_sigs.iter().filter(|s| {
		let sig_id = 0; //just pass a fake value as this function
			//is not used.
		let (res, _discharge_info) = s.accepts_by_automaton(sig_id, nibbles);
		res
	}).map(|s| s.name.clone()).collect::<HashSet<String>>();

	//5. try individual pm-reg
	let mut set_ind_pm_reg = HashSet::<String>::new();
	let dfa_sigs_left = v_sigs.iter().filter(|s| set_dfa.contains(&s.name)).
        map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();
	if set_dfa.len()>0{
		for s in &dfa_sigs_left{
			let mut sig: ClamavSig =s.as_ref().clone(); //will not change Arc
			let mut new_cfg = cfg.clone();
			new_cfg.min_bag_len = 0;
			sig.gen_approx_pm_bounds(&new_cfg); //NO RESTRICTION!
			let bag_pm = sig.collect_bagwords_from_pmreg(false); 
			let bag_pm_igc = sig.collect_bagwords_from_pmreg(true);
			let mut vec_pm = bag_pm.iter().map(|s| s.clone()).collect::<Vec<String>>();
			let mut vec_pm_igc = bag_pm_igc.iter().map(|s| s.clone()).collect::<Vec<String>>();
			vec_pm.push("0123456789abcdef190918230981212fa".to_owned());//to satisfy hex alphbet
			vec_pm_igc.push("0123456789abcdef19091823098123123fa".to_owned());
			let dfa_pm = HexACDFA::new(0, &vec_pm);
			let dfa_pm_igc = HexACDFA::new_adv(0, &vec_pm_igc, false);
			let dfa_acc_path = dfa_pm.acc_path(&nibbles);
			let dfa_acc_path_igc = dfa_pm_igc.acc_path(&nibbles);
			let hs_occ= dfa_pm.get_pattern_pos(&dfa_acc_path);
			let hs_occ_igc= dfa_pm_igc.get_pattern_pos(&dfa_acc_path_igc);
			let (res,_) = sig.accepts_approx_pm_bounds(&hs_occ, &hs_occ_igc,fname);
			//println!("DEBUG USE 603: res: {:?}", res);
			if res==TriVal::Maybe || res==TriVal::True{
				set_ind_pm_reg.insert( sig.name.clone() );
			}
		}
	}

	// 5.4 compute combinations
	let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
	let _data = FailDischargeRecord{
		fname: fname.to_string(),
		flen: file_len,
		bag: set_sigs_bag,
		crit: set_sigs_crit,
		pm: set_sigs_pm,
		all_dfa: set_dfa,
		total_acc_path_len: total_acc_path_len,
		total_hs_size: total_hs_size,
		total_accepted: total_accepted,
		total_pm_witness_len: total_pm_witness_len,
		ind_pm_reg: set_ind_pm_reg,
		total_unique_states: total_unique_states,
		most_freq_sed_cs_pats: None,

		seg_size:0, //this function is not used, just to satisfy syntax req.
		max_seg_acc_rate:0.0,
		max_seg_pat_rate:0.0,
		most_freq_seg_cs_pats: None,
	};

	panic!("should call quick_discharge_file_by_crit_bag_new")
}

///new version (if not working use the old version)
///mainly for paper_data report
///Now to be more consistent with quick_discharge_file_adv
#[allow(dead_code)]
pub fn quick_discharge_file_by_crit_bag_pm_new(fname: &str,
	nibbles: &Vec<u8>, 
	v_sigs: &Vec<Arc<ClamavSig>>,
	vec_sigs_no_crit_pat: &Vec<Arc<ClamavSig>>,
	map_crit_pat: &HashMap<String, Vec<String>>,
	map_crit_pat_igc: &HashMap<String, Vec<String>>,
	dfa_crit: &HexACDFA, dfa_bag: &HexACDFA,
	dfa_crit_igc: &HexACDFA, dfa_bag_igc: &HexACDFA,
	_b_optimize_pm: bool, _cfg: &ClamavApproxConfig,
	sig_to_id: &HashMap<String,usize>)
->(FailDischargeRecord, WordInfo){
	//0. internal function closure
	let sum_vec_size = |hs: &HashMap<String,Vec<usize>>| -> usize{
		hs.into_iter().map(|(_,v)| v.len()).sum::<usize>()
	};

	//1. process by critical pattern
	let pats_crit = dfa_crit.get_patterns(&dfa_crit.acc_path(&nibbles));
	let pats_crit_igc = dfa_crit_igc.get_patterns( 
		&dfa_crit_igc.acc_path(&nibbles));
	let mut set_sigs_crit = HashSet::<String>::new();

	for pat in &pats_crit{
		let vec1 = map_crit_pat.get(pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for pat in &pats_crit_igc{
		let vec1 = map_crit_pat_igc.get(pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for s in vec_sigs_no_crit_pat{ 
		set_sigs_crit.insert(s.as_ref().name.clone());
	}
	let set_sigs_bag = set_sigs_crit.clone(); //skipping bag so take all from cirt
			//directly and pass it to pm (SED approach).
	
	//2. process by pm bounds
	let dfa_acc_path = dfa_bag.acc_path(&nibbles);
	let dfa_acc_path_igc = dfa_bag_igc.acc_path(&nibbles);
	let total_unique_states = dfa_acc_path.par_iter().map(|&s|
		s).collect::<HashSet<usize>>().len()
			+ dfa_acc_path_igc.par_iter().map(|&s| s)
		.collect::<HashSet<usize>>().len();
		
	let hs_occ_old = dfa_bag.get_pattern_pos(&dfa_acc_path);
	let hs_occ_igc_old = dfa_bag_igc.get_pattern_pos(&dfa_acc_path_igc);
	//let hs_occ = filter_by(&hs_occ_old, &pats_crit);
	//let hs_occ_igc = filter_by(&hs_occ_igc_old, &pats_crit_igc);
	let hs_occ = hs_occ_old;
	let hs_occ_igc = hs_occ_igc_old;


	let mut set_sigs_pm = HashSet::<String>::new(); //failed by pm
	let v_sigs_pm = v_sigs.into_iter()
		.filter(|x| set_sigs_crit.contains(&x.name))
		.map(|v| v.clone() )
		.collect::<Vec<Arc<ClamavSig>>>();
	let pm_res = v_sigs_pm.par_iter().map(|sig|{//parallel processing
		//1. collect the pag of words and their appearance location
		let bag_pm = sig.collect_bagwords_from_pmreg(false); 
		let bag_pm_igc = sig.collect_bagwords_from_pmreg(true);
		let hs_occ_new = filter_by(&hs_occ, &bag_pm);
		let hs_occ_igc_new = filter_by(&hs_occ_igc, &bag_pm_igc); 
	
		//3. process each one and return the result
		let (res, info) = 
			sig.accepts_approx_pm_bounds(&hs_occ_new, &hs_occ_igc_new, fname);
		let info = info.unwrap();
		let _pm_witness_len = sum_vec_size(&hs_occ_new) + sum_vec_size(&hs_occ_igc_new);
		let new_pm_witness_len = info.min_cost; //more accurate because
		let mut max_occ = 0;
		let mut max_pat = format!("unknown");
		for (pat, vec) in hs_occ_new{
			if vec.len()>max_occ{
				max_occ = vec.len();
				max_pat = pat.clone();
			}
		}
		(res, sig.name.clone(), Some(info), new_pm_witness_len, (max_pat, max_occ))
	}).collect::<Vec<(TriVal,String, Option<DischargeSigInfo>,usize, (String,usize))>>();
	let mut vec_sed_sigs_info = vec![]; 
	let mut total_pm_witness_len = 0; 
	for pres in &pm_res{
		let (res, name, info, wit_len, _) = pres;
		total_pm_witness_len += wit_len;
		if *res==TriVal::Maybe || *res==TriVal::True{
			set_sigs_pm.insert( name.clone() );
		}else{//for discharged ones, push info
			vec_sed_sigs_info.push(info.clone().unwrap());
		}
	}
	let total_acc_path_len = dfa_acc_path.len() + dfa_acc_path_igc.len();
	let total_hs_size = hs_occ.len() + hs_occ_igc.len();
	let total_accepted = sum_vec_size(&hs_occ) + sum_vec_size(&hs_occ_igc);

	let mut max_occ = 0;
	let mut max_pat = format!("");
	for (_,_,_,_,(pat, occ)) in &pm_res{
		if *occ>max_occ{
			max_occ = *occ;
			max_pat = pat.clone();
		}
	}
	if total_accepted*10>total_acc_path_len{
		println!("DEBUG USE 8801: fname: {}, accepted ratio: {}%, max pat: {}", 
			fname, (total_accepted as f64)/(total_acc_path_len as f64)*100.0, 
			max_pat);
	}

	//4. process by dfa
	let dfa_sigs = v_sigs.iter().filter(|s| set_sigs_pm.contains(&s.name)).
		map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();
	//let set_sigs_dfa = dfa_sigs.iter().filter(|s| {
	//	let (res,_discharge_info) = s.accepts_by_automaton(nibbles);
	//	res
	//}).map(|s| s.name.clone()).collect::<HashSet<String>>();
	let mut set_sigs_dfa = HashSet::<String>::new();
	let mut vec_dfa_sigs_info = vec![];
	for s in dfa_sigs{
		let sig_id = sig_to_id.get(&s.name).expect(
			&format!("cannot find id for {}", s.name));
		let (res, info) = s.accepts_by_automaton(*sig_id, nibbles);
		if res==true{
			set_sigs_dfa.insert(s.name.clone()); //failed to discharge via dfa
		}else{
			vec_dfa_sigs_info.push(info.unwrap()); //add info about best route
		}
	}
	let set_ind_pm_reg = set_sigs_dfa.clone(); //no ind_pm setp, just clone dfa result

	//5. collect most frequent pats
	let acc_ratio = (total_accepted as f64)/(total_acc_path_len as f64)*100.0;
	let most_freq_sed_cs_pats = if acc_ratio<5.0{
		None
	}else{
		Some(dfa_bag.get_most_freq_patterns(&dfa_acc_path))
	};
	let top_n = 10;
	let seg_size = 62 * 512 * 4;
	let (most_freq_seg_cs_pats, max_seg_acc_rate, max_seg_pat_rate) =
		dfa_bag.get_most_freq_seg_patterns(&dfa_acc_path,
			top_n, seg_size);
	let most_freq_seg_cs_pats = Some(most_freq_seg_cs_pats);

	//6. compute stats 
	let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
	let fdr = FailDischargeRecord{
		fname: fname.to_string(),
		flen: file_len,
		bag: set_sigs_bag,
		crit: set_sigs_crit.clone(),
		pm: set_sigs_pm.clone(),
		all_dfa: set_sigs_dfa.clone(),
		total_acc_path_len: total_acc_path_len,
		total_hs_size: total_hs_size,
		total_accepted: total_accepted,
		total_pm_witness_len: total_pm_witness_len,
		ind_pm_reg: set_ind_pm_reg,
		total_unique_states: total_unique_states,
		most_freq_sed_cs_pats,

		seg_size,
		max_seg_acc_rate,
		max_seg_pat_rate,
		most_freq_seg_cs_pats,
	};

	let vec_sed_sigs = set_sigs_crit.difference(&set_sigs_pm).map(|s|
		*sig_to_id.get(s).unwrap()).collect::<Vec<usize>>();
	let vec_dfa_sigs = set_sigs_pm.difference(&set_sigs_dfa).map(|s|
		*sig_to_id.get(s).unwrap()).collect::<Vec<usize>>();
	let vec_ised_sigs = set_sigs_dfa.iter().map(|s|
		*sig_to_id.get(s).unwrap()).collect::<Vec<usize>>(); //
		//this actually indicates failed sigs because
		//dfa is the last step

	//6.-- no need, we will direclty jump to dfa approach
	let vec_ised_sigs_info = vec![];
	assert!(vec_sed_sigs_info.len()==vec_sed_sigs.len());
	assert!(vec_dfa_sigs_info.len()==vec_dfa_sigs.len());


	let wi = WordInfo{
		vec_sed_sigs, vec_dfa_sigs, vec_ised_sigs,
		vec_sed_sigs_info, vec_ised_sigs_info, vec_dfa_sigs_info};

	// 2026-05-16: probe 77319.1 — dump the raw discharge-prover
	// output for this file. This is the GROUND TRUTH from
	// quick_discharge_file_by_crit_bag_pm_new, BEFORE any advice
	// construction in the ZK side. If the offending subsigs are
	// missing from wi.vec_sed_sigs_info[i].subsig_ids HERE, the
	// bug is in discharge_prover (this function or its callees).
	// Reverse sig_id -> sig_name via the sig_to_id map passed in.
	if std::env::var("ZKR_PROBE_77317").is_ok() {
		let id_to_name: std::collections::HashMap<usize, &String>
			= sig_to_id.iter().map(|(n, id)| (*id, n)).collect();
		println!(
			"DEBUG USE 77319.1: discharge_prover OUT fname={} \
			 vec_sed_sigs.len={} vec_dfa_sigs.len={} \
			 vec_ised_sigs.len={}",
			fname,
			wi.vec_sed_sigs.len(),
			wi.vec_dfa_sigs.len(),
			wi.vec_ised_sigs.len());
		let dump_sigs = |label: &str, ids: &Vec<usize>,
			infos: &Vec<DischargeSigInfo>|
		{
			for k in 0..ids.len() {
				let sid = ids[k];
				let name = id_to_name.get(&sid)
					.map(|s| s.as_str()).unwrap_or("?");
				let n_sub = infos.get(k)
					.map(|i| i.subsig_ids.len()).unwrap_or(0);
				let subs: Vec<usize> = infos.get(k)
					.map(|i| i.subsig_ids.iter().copied()
						.take(16).collect())
					.unwrap_or_default();
				println!(
					"DEBUG USE 77319.1.{}: sig_id={} name={} \
					 n_subsigs={} subsig_ids[0..16]={:?}",
					label, sid, name, n_sub, subs);
			}
		};
		dump_sigs("sed", &wi.vec_sed_sigs,
			&wi.vec_sed_sigs_info);
		dump_sigs("dfa", &wi.vec_dfa_sigs,
			&wi.vec_dfa_sigs_info);
		// ised has no info vec (always empty)
		for sid in &wi.vec_ised_sigs {
			let name = id_to_name.get(sid)
				.map(|s| s.as_str()).unwrap_or("?");
			println!(
				"DEBUG USE 77319.1.ised: sig_id={} name={} \
				 (final-failed, no discharge evidence)",
				sid, name);
		}
	}

	(fdr, wi)
}

/// Return the FailDischargeRecord and WordInfo (even if it fails
/// to discharge)
pub fn quick_discharge_file_by_crit_bag_pm(
	fname: &str,
	nibbles: &Vec<u8>, 
	v_sigs: &Vec<Arc<ClamavSig>>,
	vec_sigs_no_crit_pat: &Vec<Arc<ClamavSig>>,
	map_crit_pat: &HashMap<String, Vec<String>>,
	map_crit_pat_igc: &HashMap<String, Vec<String>>,
	dfa_crit: &HexACDFA, 
	dfa_bag: &HexACDFA,
	dfa_crit_igc: &HexACDFA, 
	dfa_bag_igc: &HexACDFA,
	b_optimize_pm: bool, 
	cfg: &ClamavApproxConfig,
	sig_to_id: &HashMap<String,usize>)
->(FailDischargeRecord,WordInfo){
	quick_discharge_file_by_crit_bag_pm_new(
		fname,
		nibbles, v_sigs, vec_sigs_no_crit_pat,
		map_crit_pat, map_crit_pat_igc,
		dfa_crit, dfa_bag, dfa_crit_igc, dfa_bag_igc,
		b_optimize_pm, cfg, sig_to_id)
}

/// This one works by cp -> sed -> dfa and return the WordInfo
/// NOTE: we didn't do the bag of words as in quick_discharge old version,
/// just for saving implementation cost.
///
/// NOTE: this function is deprecated
pub fn deprecated_quick_discharge_file_adv(
	fname: &str,
	nibbles: &Vec<u8>, 
	v_sigs: &Vec<Arc<ClamavSig>>,
	vec_sigs_no_crit_pat: &Vec<Arc<ClamavSig>>,
	map_crit_pat: &HashMap<String, Vec<String>>,
	map_crit_pat_igc: &HashMap<String, Vec<String>>,
	dfa_crit: &HexACDFA, dfa_bag: &HexACDFA,
	dfa_crit_igc: &HexACDFA, dfa_bag_igc: &HexACDFA,
	_cfg: &ClamavApproxConfig,
	sig_to_id: &HashMap<String,usize>
	)->WordInfo{
	if 1>0 {panic!("Deprecated: call quick_discharge_file_by_pm_reg");}
	//1. process by critical pattern
	let pats_crit = dfa_crit.get_patterns(&dfa_crit.acc_path(&nibbles));
	let pats_crit_igc = dfa_crit_igc.get_patterns( 
		&dfa_crit_igc.acc_path(&nibbles));
	let mut set_sigs_crit = HashSet::<String>::new();
	for pat in &pats_crit{
		let vec1 = map_crit_pat.get(pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for pat in &pats_crit_igc{
		let vec1 = map_crit_pat_igc.get(pat).unwrap();	
		for x in vec1{ set_sigs_crit.insert(String::from(x)); }
	}
	for s in vec_sigs_no_crit_pat{ 
		set_sigs_crit.insert(s.as_ref().name.clone());
	}
	
	//2. process by pm bounds
	let dfa_acc_path = dfa_bag.acc_path(&nibbles);
	let dfa_acc_path_igc = dfa_bag_igc.acc_path(&nibbles);
	let hs_occ_old = dfa_bag.get_pattern_pos(&dfa_acc_path);
	let hs_occ_igc_old = dfa_bag_igc.get_pattern_pos(&dfa_acc_path_igc);
	//let hs_occ = filter_by(&hs_occ_old, &pats_crit);
	//let hs_occ_igc = filter_by(&hs_occ_igc_old, &pats_crit_igc);
	let hs_occ = hs_occ_old; //now there are 90 failing sigs separated
							 //so, no good to use pats_crit to filter anymore
							 //because they miss hte patterns fro mthese 90 
							 //failing sigs.
	let hs_occ_igc = hs_occ_igc_old;


	let mut set_sigs_pm = HashSet::<String>::new(); //failed by pm
	let v_sigs_pm = v_sigs.into_iter()
		.filter(|x| set_sigs_crit.contains(&x.name))
		.map(|v| v.clone() )
		.collect::<Vec<Arc<ClamavSig>>>();
	let pm_res = v_sigs_pm.par_iter().map(|sig|{//parallel processing
		//1. collect the pag of words and their appearance location
		let bag_pm = sig.collect_bagwords_from_pmreg(false); 
		let bag_pm_igc = sig.collect_bagwords_from_pmreg(true);
		let hs_occ_new = filter_by(&hs_occ, &bag_pm);
		let hs_occ_igc_new = filter_by(&hs_occ_igc, &bag_pm_igc); 

		//3. process each one and return the result
		let (res, info) = 
			sig.accepts_approx_pm_bounds(&hs_occ_new, &hs_occ_igc_new,fname);
		(res, sig.name.clone(), info)
	}).collect::<Vec<(TriVal,String, Option<DischargeSigInfo>)>>();
	let mut vec_sed_sigs_info = vec![]; 
	for pres in pm_res{
		let (res, name, info) = pres;
		if res==TriVal::Maybe || res==TriVal::True{
			set_sigs_pm.insert( name.clone() );
		}else{//for discharged ones, push info
			vec_sed_sigs_info.push(info.unwrap());
		}
	}

	//4. process by dfa
	let dfa_sigs = v_sigs.iter().filter(|s| set_sigs_pm.contains(&s.name)).
		map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();
	let mut set_sigs_dfa = HashSet::<String>::new();
	let mut vec_dfa_sigs_info = vec![];
	for s in dfa_sigs{
		let sig_id = sig_to_id.get(&s.name).expect(
			&format!("cannot find id for {}", s.name));
		let (res, info) = s.accepts_by_automaton(*sig_id, nibbles);
		if res==true{
			set_sigs_dfa.insert(s.name.clone()); //failed to discharge via dfa
		}else{
			vec_dfa_sigs_info.push(info.unwrap()); //add info about best route
		}
	}

/*
	//5. try individual pm-reg
	let mut set_ind_pm_reg = HashSet::<String>::new();
	let dfa_sigs_left = v_sigs.iter().filter(|s| set_dfa.contains(&s.name)).
        map(|s| s.clone()).collect::<Vec<ClamavSig>>();
	if set_dfa.len()>0{
		for s in &dfa_sigs_left{
			println!("\n===========*********=============\nDEBUG USE 601. try pm-reg indivudally for sig: {} on file: {}", s.to_str(), fname);
			let mut sig  = s.clone();
			let mut new_cfg = cfg.clone();
			new_cfg.min_bag_len = 0;
			sig.gen_approx_pm_bounds(&new_cfg); //NO RESTRICTION!
			let bag_pm = sig.collect_bagwords_from_pmreg(false); 
			let bag_pm_igc = sig.collect_bagwords_from_pmreg(true);
			let mut vec_pm = bag_pm.iter().map(|s| s.clone()).collect::<Vec<String>>();
			let mut vec_pm_igc = bag_pm_igc.iter().map(|s| s.clone()).collect::<Vec<String>>();
			vec_pm.push("0123456789abcdef190918230981212fa".to_owned());//to satisfy hex alphbet
			vec_pm_igc.push("0123456789abcdef19091823098123123fa".to_owned());
			let dfa_pm = HexACDFA::new(0, &vec_pm);
			let dfa_pm_igc = HexACDFA::new_adv(0, &vec_pm_igc, false);
			let dfa_acc_path = dfa_pm.acc_path(&nibbles);
			let dfa_acc_path_igc = dfa_pm_igc.acc_path(&nibbles);
			let hs_occ= dfa_pm.get_pattern_pos(&dfa_acc_path);
			let hs_occ_igc= dfa_pm_igc.get_pattern_pos(&dfa_acc_path_igc);
			println!("DEBUG USE 602: sum_vec_size(hs_occ.len): {}, hs_occ_igc.len: {}, filesize: {}", sum_vec_size(&hs_occ), sum_vec_size(&hs_occ_igc), nibbles.len());
			let res = sig.accepts_approx_pm_bounds(&hs_occ, &hs_occ_igc);
			//println!("DEBUG USE 603: res: {:?}", res);
			if res==TriVal::Maybe || res==TriVal::True{
				set_ind_pm_reg.insert( sig.name.clone() );
			}
		}
	}

	// 5.4 compute combinations
	let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
	let _data = FailDischargeRecord{
		fname: fname.to_string(),
		flen: file_len,
		bag: set_sigs_bag,
		crit: set_sigs_crit,
		pm: set_sigs_pm,
		all_dfa: set_dfa,
		total_acc_path_len: total_acc_path_len,
		total_hs_size: total_hs_size,
		total_accepted: total_accepted,
		total_pm_witness_len: total_pm_witness_len,
		ind_pm_reg: set_ind_pm_reg,
	};
	*/

	//5. finally construct the word info
	// the sigs to be charged by sed, dfa, ised
	let vec_sed_sigs = set_sigs_crit.difference(&set_sigs_pm).map(|s|
		*sig_to_id.get(s).unwrap()).collect::<Vec<usize>>();
	let vec_dfa_sigs = set_sigs_pm.difference(&set_sigs_dfa).map(|s|
		*sig_to_id.get(s).unwrap()).collect::<Vec<usize>>();
	let vec_ised_sigs = vec![]; //later decide if need to handle

	//6.-- no need, we will direclty jump to dfa approach
	let vec_ised_sigs_info = vec![];

	WordInfo{ vec_sed_sigs, vec_dfa_sigs, vec_ised_sigs, vec_sed_sigs_info,
		vec_ised_sigs_info, vec_dfa_sigs_info}
}


//-----------------------------------------
//region: utility functions 
//-----------------------------------------
/// find the given signature
pub fn find_sig(sig_name:&str, fpath: &str, sigtype: ClamSigType, cfg: &ClamavApproxConfig) -> Option<ClamavSig>{
	let lines = &read_lines(fpath)[1..].to_vec();
	for s in lines{
		let vec_s:Vec<String> = s.split(";").map(str::to_string).collect();
		let name = &vec_s[0];
		if name.contains(sig_name){
			return Some(gen_clamav_sig(s, sigtype, cfg));
		}
	}
	None
}

/// generate a default clamav config.
pub fn default_clamav_cfg()->ClamavApproxConfig{
	ClamavApproxConfig{
		max_pm_sections: 10, // LATEST OLD 32 does not help much
		combination_limit: 127, 
		repeat_limit: 256,  //-> avg step: 19  
		min_bag_len: 6,  
		min_pm_word_len: 4, // increase to 5 will kill a lot
	}
}
//-----------------------------------------
//endregion: utility functions 
//-----------------------------------------


#[cfg(test)]
mod tests_clamav{
	extern crate rustomaton;
	extern crate utils; 

	use std::{collections::{HashMap,HashSet}, sync::{Arc}};
 	use rustomaton::automaton::Automata;
	use utils::{logger::{log,LOG2,LOG3},data::{hex_to_u8}, os::{proj_root}}; 
	use crate::{
		hex_acdfa::{HexACDFA},
		type_def::{ClamSigType,TriVal,CompOp,ClamavSig,SubSigObj,SubSigType,ClamavApproxConfig},
		fsa_utils::{build_nfa_fast, build_nfa_slow, nfa_eq},
		clamav::{find_sig,gen_clamav_sig,quick_discharge_file_by_crit_bag_pm, filter_by,default_clamav_cfg,RANGE_MAX}
	};


	/// a test case for clamav
	struct ClamavTestCase{
		sig_name: String,
		desc: String,
		// each elel is (desc, test_str, expected_val)
		arr_cases: Vec<(String,String,bool)>
	}

	/// return the cfg for test
	pub fn get_testcfg() -> ClamavApproxConfig{
		default_clamav_cfg()
	}


	//// run a clamav test case
	fn run_clamav_case(c: &ClamavTestCase){
		let testcfg = default_clamav_cfg();
		let src = format!("{}/data/src_sig/clamav/categories/main.dat"
			,proj_root());
		let res = find_sig(&c.sig_name, &src, ClamSigType::General, &testcfg);
		assert!(!res.is_none(), "could not find sig: {}", &c.sig_name);
		log(0, LOG2, &format!("Run clamav on sig: {}\nFor: {}", 
				&c.sig_name, &c.desc)); 
		let mut sig = res.unwrap();
		sig.set_vec_automaton(&testcfg);
		let use_eval = true;
		for (desc, s_test, b_exp) in &c.arr_cases{
			let res = if use_eval{
				// !sig.accepts_by_automaton(&s_test.as_bytes().to_vec())
				let fake_sigid = 0;
				!sig.accepts_by_automaton(fake_sigid,&hex_to_u8(&s_test)).0
			}else{
				let (_, _, v_nfa, _name) = sig.to_neg_automaton(100);
				let nfa = &v_nfa[0][0];
				nfa.run(&s_test.chars().collect::<Vec<char>>())
			};
			log(0, LOG3, &format!(" -- desc: {}, b_exp: {}, res: {}", desc, b_exp, res));
			assert!(res==*b_exp, "ERROR for test str: {}, desc: {}, res: {}, b_exp: {}\nDetails: {:?}", &s_test, &desc, res, b_exp, sig);
		}
	}

	#[test]
	pub fn test_clamav_simple(){
		let case1 = ClamavTestCase{
			sig_name: String::from("Win.Exploit.CVE_2016_7185-1"),
			desc: String::from("test simple list of conjunctions"),
			arr_cases: vec![
				(String::from("missing pattern 1"),
				 String::from("ddddd5361666548616e646c655a65726f4f724d696e75734f6e654973496e76616c6964dddd52656c6561736548616e646c65dddd5c004400650076006900630065005c0044006600730043006c00690065006e007400eeee"),
				 true),
				(String::from("containing all"),
				 String::from("aaaa44616e6765726f757347657448616e646c65ddddd5361666548616e646c655a65726f4f724d696e75734f6e654973496e76616c6964dddd52656c6561736548616e646c65dddd5c004400650076006900630065005c0044006600730043006c00690065006e007400eeee"),
				 false),
			]
		};
		run_clamav_case(&case1);
	}

	#[test]
	pub fn test_clamav_combo(){
		let case1 = ClamavTestCase{
			sig_name: String::from("Win.Virus.CryptoWall4-2"),
			desc: String::from("test combination of and/or"),
			arr_cases: vec![
				(String::from("pattern136 missing 4 or 5"),
				 String::from("ddddf95aaaaaaaa33c0c9c3dddd8b45aa408945ddddffd00f81dddd"),
				 true),
				(String::from("satisfying example: 0146 "),
				 String::from("dddd8b85fcfeffff2b85f0feffff8985fcfeffffc785ecfeffffaaaa4100ddddff95aaaaaaaa33c0c9c3dddd8b000f81ddddffd00f81dddd"),
				 false),
			]
		};
		run_clamav_case(&case1);
	}

	#[test]
	pub fn test_clamav_greater_len(){
		let case1 = ClamavTestCase{
			sig_name: String::from("Win.Trojan.B-473"),
			desc: String::from("test greater len"),
			arr_cases: vec![
				(String::from("0 1"),
				 String::from("dddd") + &"7B35354134393838432D433931462D343035342D393037362D3232304143354543303346467D00".to_lowercase() + "5068aaaaaaaa" + "dddd",
				 true),
				(String::from("0 1 1 1"),
				 String::from("dddd") + &"7B35354134393838432D433931462D343035342D393037362D3232304143354543303346467D00".to_lowercase() + &"5068aaaaaaaa".repeat(3) + "dddd",
				 false),
			]
		};
		run_clamav_case(&case1);
	}

	#[test]
	pub fn test_fast_nfa(){
		let pats = vec![
			"abc",
			"123.*.?.?",
			"123.*.?.?abc...223.*.?.?.?",
			".?.?.*abc.*123...*.?33322.*",
			".?.?.*abc.*123...*.?33322.*",
			"abc.?.?.*abc.*123......*.?33322.*...?.?..",
			"..?.*.?..*123.?abc",
		];
		for pat in pats{
			let nfa1 = build_nfa_slow(pat);
			let nfa2 = build_nfa_fast(pat);
			let _res = nfa1.run(&"12345".chars().collect::<Vec<char>>());
			let _res2 = nfa2.run(&"12346".chars().collect::<Vec<char>>());
			assert!(nfa_eq(&nfa1, &nfa2), "failed on case: {}", pat);
		}
	}


	#[test]
	pub fn test_clamav_negation(){
		let case1 = ClamavTestCase{
			sig_name: String::from("Win.Exploit.CVE_2016_7295-5575139-0"),
			desc: String::from("test negation"),
			arr_cases: vec![
				(String::from("0123 - not satisfying because of 2"),
				 String::from("dddd4164644c6f67436f6e7461696e6572dddd894424204533c94533c033d2488bcfff15883e0000dddd4372656174654c6f674d61727368616c6c696e6741726561dddd52657365727665416e64417070656e644c6f67dddd"),
				 true),
				(String::from("013 missing 2 - satisfying (so virus -> false)"),
				 String::from("dddd4164644c6f67436f6e7461696e6572dddd894424204533c94533c033d2488bcfff15883e0000dddd4372656174654c6f674d61727368616c6c696e6741726561dddd27665416e64417070656e644c6f67dddd"),
				 false),
			]
		};
		run_clamav_case(&case1);
	}

	#[test]
	pub fn test_extract_patterns(){
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 3;
		//NOTE the alt limit is 127, this allows to concat and get
		//more items concatenated
		let test_cases = vec![
			(".*abc.*123", vec![ vec!["abc"], vec!["123"]]),
			(".*abc(11|22).*123(55|66)(77|88)", vec![ vec!["abc11", "abc22"], 
				vec!["1235577", "1235588", "1236677", "1236688"]]),
		];
		for tc in test_cases{
			let sig = tc.0;
			let mut hs_exp = HashSet::<Vec<String>>::new();
			for v in tc.1{ 
				let mut new_v = Vec::<String>::new();
				for x in v{
					new_v.push(x.to_string());
				}
				hs_exp.insert(new_v);
			}
			let hs_act = ClamavSig::gen_approx_patterns_for_sig(sig, &cfg);
			assert!(hs_act==hs_exp, "ERROR on sig: {}, actual patterns: {:?}, expected: {:?}", sig, hs_act, hs_exp);
		}
	}

	#[test]
	pub fn count_pattern(){
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 3;
		let test_cases = vec![
			(	".*abc.*123", //regex pattern
				"abc000123000123", //test string
				vec![
					(CompOp::GT, 1, TriVal::False), //expected values
					(CompOp::GT, 3, TriVal::False), 
					(CompOp::GT, 2, TriVal::False), 
				],
			),
			(	".*abc(11|12)(22|23).*def", //regex pattern
				"abc00011230001223", //test string
				vec![
					(CompOp::GT, 1, TriVal::False), 
					(CompOp::GT, 3, TriVal::False), 
					(CompOp::GT, 2, TriVal::False), 
					(CompOp::EQ, 2, TriVal::False), 
					(CompOp::LT, 1, TriVal::True),  //because no def
					(CompOp::LT, 2, TriVal::True), 
					(CompOp::LT, 3, TriVal::True), 
				],
			),
			(	".*abc(11|12)(22|23).*def", //regex pattern
				"abc11230001223def", //test string
				vec![
					(CompOp::LT, 1, TriVal::Maybe),  
					(CompOp::LT, 2, TriVal::True), 
					(CompOp::LT, 3, TriVal::True), 
				],
			),
		];
		for tc in test_cases{
			let sig= tc.0;
			let text = tc.1;
			let tuples = tc.2;
			let patterns = ClamavSig::gen_approx_patterns_for_sig(sig, &cfg);
			for test_case in tuples{
				let occ = ClamavSig::count_pattern_occ(&patterns, text);
				let act_res= ClamavSig::eval_pattern_occ(&occ, test_case.0, test_case.1);
				let exp_res = test_case.2;
				assert!(act_res == exp_res, "text: {}, sig: {}, op: {:?}, target: {}, act_res: {:?}, expected: {:?}", text,sig, test_case.0, test_case.1, act_res, exp_res);
			}
		}
	}


	#[test]
	pub fn test_approx_eval_bagwords(){
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 3;
		let testcases = vec![
			("0&1;abc??def;123??234", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc123def234", TriVal::Maybe),
			  	("abc123de234", TriVal::False), //missing def
			  ]
			),
			("0|1;abc??def;123??234", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc123def234", TriVal::Maybe),
			  	("abc123de234", TriVal::Maybe), 
			  ]
			),
			("0>2&1>3;abc??def;123??234", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc123def234", TriVal::False),
			  	("123def234abcdef123234abc123def234123234def", TriVal::False), 
			  	("abc123def234abcdef123234abc123def234123234abcdef", TriVal::Maybe), 
			  ]
			),
			("0=2&1=3;abc??def;123??234", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc123def234", TriVal::False),
			  	("123def234abcdef123234abc123def234123234def", TriVal::Maybe), 
			  	("abc123def234abcdef123234abc123def234123234abcdef", TriVal::Maybe), 
			  ]
			),
			("0<2&1<3;abc??def;123??234", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::True),
			  	("abc123def234", TriVal::True),
			  	("123def234abcdef123234abc123def234123234def", TriVal::Maybe), 
			  	("abc123def234abcdef123234abc123def234123234abcdef", TriVal::Maybe), 
			  ]
			),
			("0&1;abc(11|22)(33|44)def;555??666", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc1133def", TriVal::False),
			  	("abc1133def666", TriVal::False),
			  	("abc1133def66655", TriVal::False),
			  	("abc1133def666555", TriVal::Maybe),
			  ]
			),
			("(0|1)>1;abc??def;555??666", //pattern
			  vec![//list of text and expected match result
			  	("abc", TriVal::False),
			  	("abc555ddef666abcdef666555", TriVal::Maybe),
			  ]
			),
			("(0|1)<1;abc??def;555??666", //pattern
			  vec![//list of text and expected match result
			  	("ac", TriVal::True),
			  	("abcdef", TriVal::True),
			  	("abc555ddef666abcdef666555", TriVal::Maybe),
			  ]
			),
		];
		let header = "Win.TEST.TEST-1;Engine:51-255,Target:1;".to_string();
		for tc in testcases{
			let mut sig = gen_clamav_sig(&(header.clone() + tc.0),
				ClamSigType::General, &cfg); 
			sig.gen_approx_bagwords(&cfg);
			for tuple in tc.1{
				let text = hex_to_u8(tuple.0);
				let exp_res = tuple.1;
				let act_res = sig.accepts_approx_bagwords(&text);
				assert!(exp_res==act_res, "approx_val failed on sig: {:?}, text: {}, exp_res: {:?}, act_res:{:?}", sig, tuple.0, exp_res, act_res);
			}
		}
	}

	#[test]
	pub fn test_fast_approx_eval_bagwords(){
		let sigs = vec![
			"0|1;abcdef0123456789;abc", 
			"0&1;abc(11|22)(33|44)def;555??666",
			"0>2;ddee"
		];
		let header = "Win.TEST.TEST-1;Engine:51-255,Target:1;".to_string();
		let arr_cases = vec![
			"abc1133ddeeabcddee012ddee",
			"abcdef0123457890a",
			"abc2244666aaa555",
			"ddee123ddee1ddee11abc",
			"dd1122",
			"ddee1ddee",
		];
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 3;
		let arr_sigs = sigs.into_iter().map(|s|{
			let mut sig = 
				gen_clamav_sig(&(header.clone()+s), ClamSigType::General,&cfg);
				sig.gen_approx_bagwords(&cfg);
				sig.gen_approx_pm_bounds(&cfg);
				sig
			}).
			collect::<Vec<ClamavSig>>();
		let pats = (&arr_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let dfa = HexACDFA::new(0, &pats);
		for s in arr_cases{
			let nibbles = hex_to_u8(s);
			let hs_occ = dfa.get_pattern_stats(&dfa.acc_path(&nibbles));
			for sig in &arr_sigs{
				let act_res = sig.accepts_approx_bagwords(&nibbles);
				let fast_res = sig.accepts_approx_bagwords_fast(&hs_occ, &hs_occ);
				assert!(act_res==fast_res, "for sig: {}, str: {}, act_res: {:?}, fast_res: {:?}", sig.to_str(), s, act_res, fast_res);
			}
		}
	}

	#[test]
	pub fn test_get_tokens(){
		let tcs = vec![
			(".*abc.*", vec![".*", "abc", ".*"]),
			(".*abc...*123", vec![".*", "abc", "...*", "123"]),
			("abc...?.*123", vec!["abc", "...?.*", "123"]),
			("abc....?.*123", vec!["abc", "....?.*", "123"]),
			("abc....?.*123.", vec!["abc", "....?.*", "123", "."]),
			(".a.a.", vec![".", "a", ".", "a", "."]),
			(".a.*.aa.", vec![".", "a", ".*.", "aa", "."])
		];
		for testcase in tcs{
			let s = testcase.0;
			let expected = testcase.1.iter().map(|s| s.to_string()).
				collect::<Vec<String>>();
			let act = SubSigObj::get_tokens(s);
			assert!(expected==act, "FAILED get_tokens() for {}, expected: {:?}, act: {:?}", s, &expected, &act);
		}
	}

	#[test]
	pub fn test_token_to_bound(){
		let tcs = vec![
			(".*", (0, RANGE_MAX)), 
			(".*..", (2, RANGE_MAX)), 
			(".*...*", (2, RANGE_MAX)), 
			(".?", (0, 1)), 
			(".?.?", (0, 2)), 
			("...?.?", (2, 4)), 
			("...?.?..*", (3, RANGE_MAX)), 
			(".....?", (4, 5)),
			("...", (3,3))
		];
		for tc in tcs{
			let s = tc.0;
			let exp = tc.1;
			let act = SubSigObj::reg_to_bound(s);
			assert!(exp==act, "fail token_to_bound. token: {:?}, expected: {:?}, bound: {:?}", s, exp, act);
		}
	}

	#[test]
	pub fn test_gen_pm_bounds(){
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 3;
		let tc = vec![
			(".*abc...de", vec![("abc", (0,RANGE_MAX)), ("de",(3,3))]),
			(".*abc...de..", vec![("abc", (0,RANGE_MAX)), ("de",(3,3))]),
			("abc...de..", vec![("abc", (0,0)), ("de",(3,3))]),
			("abc...de..ef", vec![("abc", (0,0)), ("de",(3,3)), ("ef", (2,2))]),
			("abc...de..*.ef", vec![("abc", (0,0)), ("de",(3,3)), ("ef", (2,RANGE_MAX))]),
			("abc..?..de..*.ef", vec![("abc", (0,0)), ("de",(3,4)), ("ef", (2,RANGE_MAX))]),
			("abc..?..?.de..*.ef", vec![("abc", (0,0)), ("de",(3,5)), ("ef", (2,RANGE_MAX))]),
		];
		for c in tc{
			let s = c.0;
			let expected = c.1.into_iter().map(|s|
				(s.0.to_string(), s.1))
				.collect::<Vec<(String,(usize,usize))>>();
			let sig = SubSigObj{value: s.to_string(), subsig_type:SubSigType::GeneralRegex, real_value: s.to_string(), b_ignore_case: false,
				set_subsigs: HashSet::<usize>::new(), min_required: 0}; 
			let act = sig.gen_pm_bounds(&cfg);
			assert!(expected==act, "failed_gen_pm for s: {}, expected: {:?}, actual: {:?}", s, expected, act);
		}
	}

	#[test]
	pub fn test_approx_pm(){
		//note pattern like "abc.*def" eventually converted to ".*abc.*def"
		let sigs = vec![
			"0;abcdef0123456789", //id: 0
			"0&1;abc??def;555??666", //1
			"0;abc??*def", //2
			"0;abc{2-4}def", //3
			"0;abc(11|22|33)(44|55|66)def", //4
			"(0&1)|2;ab??cd;ef??ab;11??22", //5
			"0>2;dd??ee", //6
			"0<2;dd??ee", //7
			"0=1;dd??ee", //8
			"0=0;dd??ee", //9
		];
		let header = "Win.TEST.TEST-1;Engine:51-255,Target:1;".to_string();
		let arr_cases = vec![
			("abc11def555aa666", 1, TriVal::Maybe),
			("abc111def555aa666", 1, TriVal::False),
			("abc11def555aab666", 1, TriVal::False),
			("abc11def555aa", 1, TriVal::False),
			("abcdef", 2, TriVal::False),
			("abc1def", 2, TriVal::False),
			("abc12def", 2, TriVal::Maybe),
			("abc123def", 2, TriVal::Maybe),
			("abc123def", 3, TriVal::False),
			("abc1234def", 3, TriVal::Maybe),
			("abc123456789def", 3, TriVal::False),
			("abcdef", 4, TriVal::False),
			("abc1144def", 4, TriVal::Maybe),
			("abc114455def", 4, TriVal::False),
			("ab33cdef44ab11aa22", 5, TriVal::Maybe),
			("ab334cdef44ab11aab22", 5, TriVal::False),
			("ab334cdef445ab11aa22", 5, TriVal::Maybe),
			("ab334cdef445ab11aab22", 5, TriVal::False),
			("dd11eedd22eedd3ee", 6, TriVal::False),
			("dd112eedd223eedd33ee333dd44ee", 6, TriVal::False),
			("dd11eedd22eedd33ee", 6, TriVal::Maybe),
			("dd22eedd", 7, TriVal::True),
			("dd222eedd", 7, TriVal::True),
			("dd22eedd22ee", 7, TriVal::Maybe),
			("dd22eedd22ee11dd22ee", 7, TriVal::Maybe),
			("dd22eedd2233ee", 7, TriVal::True),
			("dd22eedd", 8, TriVal::Maybe),
			("dd22eedd22ee", 8, TriVal::Maybe),
			("dd22", 8, TriVal::False),
			("dd22", 9, TriVal::True),
			("dd22ee", 9, TriVal::Maybe),
		];
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 4;
		cfg.min_pm_word_len = 2;
		let arr_sigs = sigs.into_iter().map(|s|{
		let mut sig = 
				gen_clamav_sig(&(header.clone()+s), ClamSigType::General, &cfg);
				sig.gen_approx_bagwords(&cfg);
				sig.gen_approx_pm_bounds(&cfg);
				sig
		}).collect::<Vec<ClamavSig>>();
		let pats = (&arr_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let dfa = HexACDFA::new(0, &pats);
		for (s, sid,exp_val) in arr_cases{
			let nibbles = hex_to_u8(s);
			let hs_occ = dfa.get_pattern_pos(&dfa.acc_path(&nibbles));
			let sig = &arr_sigs[sid];
			let (act_res,_) = sig.accepts_approx_pm_bounds(&hs_occ, &hs_occ,
				"na");
			assert!(act_res==exp_val, "for sig: {}, str: {}, act_res: {:?}, expected: {:?}", sig.to_str(), s, act_res, exp_val);
		}
	}

	#[test]
	pub fn test_approx_pm_for_pm(){
		//note pattern like "abc.*def" eventually converted to ".*abc.*def"
		let sigs = vec![
			"0;abcdef0123456789", //id: 0
			"0&1;abc??def;555??666", //1
			"0;abc??*def", //2
			"0;abc{2-4}def", //3
			"(0&1)|2;ab??cd;ef??ab;11??22", //4
			"0>2;dd??ee", //5
			"0<2;dd??ee", //6
		];
		let header = "Win.TEST.TEST-1;Engine:51-255,Target:1;".to_string();
		let arr_cases = vec![
			("abc11def555aa666", 1, TriVal::Maybe),
			("abc111def555aa666", 1, TriVal::False),
			("abc11def555aab666", 1, TriVal::False),
			("abc11def555aa", 1, TriVal::False),
			("abcdef", 2, TriVal::False),
			("abc1def", 2, TriVal::False),
			("abc12def", 2, TriVal::Maybe),
			("abc123def", 2, TriVal::Maybe),
			("abc123def", 3, TriVal::False),
			("abc1234def", 3, TriVal::Maybe),
			("abc123456789def", 3, TriVal::False),
			("ab33cdef44ab11aa22", 4, TriVal::Maybe),
			("ab334cdef44ab11aab22", 4, TriVal::False),
			("ab334cdef445ab11aa22", 4, TriVal::Maybe),
			("ab334cdef445ab11aab22", 4, TriVal::False),
			("dd11eedd22eedd3ee", 5, TriVal::False),
			("dd11eedd22eedd33ee", 5, TriVal::Maybe),
			("dd112eedd223eedd33ee333dd44ee", 5, TriVal::False),
			("dd22eedd22ee", 6, TriVal::Maybe),
			("dd22eedd222ee", 6, TriVal::True),
			("dd22eedd", 6, TriVal::True),
		];
		let arr_sigs = sigs.into_iter().map(|s|{
		let mut cfg = get_testcfg();
		cfg.min_pm_word_len = 2;
		cfg.min_bag_len= 4;
		let mut sig = 
				gen_clamav_sig(&(header.clone()+s), ClamSigType::General, &cfg);
				sig.gen_approx_bagwords(&cfg);
				sig.gen_approx_pm_bounds(&cfg);
				sig
		}).collect::<Vec<ClamavSig>>();
		let pats = (&arr_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		println!("\n************ DEBUG USE 101: collected patterns: {:?}", pats);
		let dfa = HexACDFA::new(0, &pats);
		for (s, sid,exp_val) in arr_cases{
			let nibbles = hex_to_u8(s);
			let hs_occ = dfa.get_pattern_pos(&dfa.acc_path(&nibbles));
			let sig = &arr_sigs[sid];
			let bagwords_pm = sig.collect_bagwords_from_pmreg(false);
			let hs_occ = filter_by(&hs_occ, &bagwords_pm); 
			let (act_res,_) = sig.accepts_approx_pm_bounds(&hs_occ, &hs_occ, "na");
			assert!(act_res==exp_val, "for sig: {}, str: {}, act_res: {:?}, expected: {:?}", sig.to_str(), s, act_res, exp_val);
		}
	}

	#[test]
	pub fn test_discharge(){
		//1. generate sigs, critical patterns and bag of words and ACDFAs
		// name "p" indicates pm-reg, name "g" indicates general
		let mut cfg = get_testcfg();
		cfg.min_bag_len = 4;
		cfg.min_pm_word_len = 4;
		let v_sig_inp = vec![
			"m0;Engine:51-255,Target:1;0;0123456789abcdef",
			"m02;Engine:51-255,Target:1;0;0123456789abcdef::i",
			"m1;Engine:51-255,Target:1;(0|1|2|3);1001aabbcc;1002aabbcc;1003aabbcc;1004aabbcc",
			"m2;Engine:51-255,Target:1;(0&1&2);2001aabbcc;2002aabbcc;2003aabbccd",
			"g3;Engine:51-255,Target:1;0;3001aabbcc(3002aabbcc|3003aabbcc)3004aabbcc",
			"g4;Engine:51-255,Target:1;0;4001aabbcc??4002aabbcc",
			"g5;Engine:51-255,Target:1;0>2;5001aabbcc",
			"g6;Engine:51-255,Target:1;0;6001aabbcc4164::i", //Ad
			"g7;Engine:51-255,Target:1;0&1;7001aabbcc4164::i;7002aabbcc4165", 
			"g8;Engine:51-255,Target:1;0;8001aabbcc4161??8002aabbcc4162::i", 
			"g9;Engine:51-255,Target:1;1;9001aabbcc4161;0/abcde/i", 
			"g10;Engine:51-255,Target:1;1;100011aabbcc4161;0/ccccbbbbaaaa(11|22)aaaabbbbcccc/", 
			"g11;Engine:51-255,Target:1;0;110011aabbcc{2-4}110012ccddcc", 
			"g12;Engine:51-255,Target:1;1;120001aabbcc;0/ababababab(123|4567){1,2}dedededede/", 
			"g13;Engine:51-255,Target:1;1;130001aabbcc;0/12[^a]{2}34/", 
			//simplified Pdf.Exploit.CVE_2013_3353_1
			"g14;Engine:51-255,Target:0;0|1|2;68656164{2}!(00|00)??????68686561;68656164{2}??!(00|00)????68686561;68656164{2}????!(00|00)??68686561",
			"g15;Engine:51-255,Target:0;0=0&1;15001ccddee;15002ccddee",
			//g16 will HAVE TO BE INCLUDED for everyone's critical set!
			//because its first subsig CANNOT be discharged by critical pat
			//also it cannot be discharged via bag!
			"g16;Engine:51-255,Target:0;0<2|1;16001ccddee;16002ccddee",
			//used for testing bag of words counter constraint 1
			"g17;Engine:51-255,Target:0;0=0&1;17001ccddee;17002ccddee",
			//used for testing bag of words counter constraint <
			"g18;Engine:51-255,Target:0;0<2&1;18001ccddee;18002ccddee",
			"g19;Engine:51-255,Target:0;0>1&1;19001ccddee;19002ccddee",
			//used for testing TotalSubsigCount type, requiring
			//at least 2 subsigs ok
			"g20;Engine:51-255,Target:0;(0|1|2)>1,2;201001aaccee;201002aaccee;201003aaccee",
			"g21;Engine:51-255,Target:0;(0|1|2)>1,2;2111ace??2112ace;2121ace??2122ace;2131ace??2132ace",
			"g22;Engine:51-255,Target:0;(0|1|2)>1,2;2211ace!(00|01)!(00|01)2212ace;2221ace!(00|01)!(00|01)2222ace;2231ace!(00|01)!(00|01)2232ace",
		];
		let v_sigs:Vec<Arc<ClamavSig>> = v_sig_inp.iter().map(|s| {
			let vc: Vec<char> = s.chars().collect();
			let sig_type = if vc[0]=='m' 
				{ClamSigType::PM} else {ClamSigType::General};
			Arc::new(gen_clamav_sig(s, sig_type,&cfg))
		}).collect();
		let sig_to_id = v_sigs.iter().enumerate().map(|(i,s)|
			(s.name.clone(), i+1)
		).collect::<HashMap<String,usize>>();
		
		let mut v_sigs = v_sigs.iter().map(|s1| {
			let mut s = s1.as_ref().clone();
			s.gen_approx_bagwords(&cfg);
			s.gen_approx_pm_bounds(&cfg);
			s.set_vec_automaton(&cfg);

			Arc::new(s)
		}).collect::<Vec<Arc<ClamavSig>>>();
		let mut map_crit_pat = HashMap::<String,Vec<String>>::new();
		let mut map_crit_pat_igc = HashMap::<String,Vec<String>>::new();
		let mut v_sigs_no_crit_pat = vec![];
		let mut new_v_sigs = vec![];
		for i in 0..v_sigs.len(){ 
			let mut sig = v_sigs[i].as_ref().clone();
			let b_res = sig.add_critical_pattern(&mut map_crit_pat, 
				&mut map_crit_pat_igc); 
			if !b_res{ sig.b_no_crit_pat= true; }
			let arc_sig = Arc::new(sig);
			if !b_res{ v_sigs_no_crit_pat.push(arc_sig.clone());}
			new_v_sigs.push(arc_sig);
		}
		v_sigs = new_v_sigs;

		let vec_crit_pat = map_crit_pat.keys().cloned()
			.collect::<Vec<String>>();
		let vec_crit_pat_igc = map_crit_pat_igc.keys().cloned()
			.collect::<Vec<String>>();
		let dfa_crit = HexACDFA::new(0, &vec_crit_pat);
		let dfa_crit_igc = HexACDFA::new_adv(0, &vec_crit_pat_igc, true);

		let pats = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let pats_igc = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(true)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let dfa_bag = HexACDFA::new(0, &pats);
		let dfa_bag_igc = HexACDFA::new_adv(0, &pats_igc, true);

		//2. test cases
		let test_cases = vec![
			("1001aabbcc", vec!["m1", "g16"], vec!["m1", "g16"], vec!["m1", "g16"], vec!["m1", "g16"]),
			("1001", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]),
			//below will fail crit pattern approach, i.e.,
			// (reporting m2 as false positive),
			//because the last eq length 2003aabbccd is the ONLY crit pat
			//even though it misses the first 2 required patterns 2001.. 2002..
			("2001aabbcc", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]),
			("2003aabbccd", vec!["g16","m2"], vec!["g16"], vec!["g16"], vec!["g16"]),
			("2001aabbcc1112003aabbccd", vec!["g16","m2"], vec!["g16"], vec!["g16"], vec!["g16"]),
			("2001aabbcc2002aabbcc2003aabbccd", vec!["g16","m2"], vec!["g16","m2"], vec!["g16","m2"], vec!["g16","m2"]),
			("3001aabbcc3003aabbcc3004aabbcc", vec!["g16","g3"], vec!["g16","g3"], vec!["g16","g3"], vec!["g16","g3"]),
			("3001aabbcc1111dddddd3004aabbcc", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]),
			("4001aabbcc004002aabbcc", vec!["g16","g4"], vec!["g16","g4"], vec!["g16","g4"], vec!["g16","g4"]),
			// not a match because extra 0 between 4001aabbcc and 4002aabbcc
			("4001aabbcc0004002aabbcc", vec!["g16","g4"], vec!["g16","g4"], vec!["g16"], vec!["g16"]),
			//g4 can't be discharged by bag but can be discharged by pm-reg
			//because the order of the two words are different
			("4002aabbcc004001aabbcc", vec!["g16","g4"], vec!["g16","g4"], vec!["g16"], vec!["g16"]),
			("5001aabbcc", vec!["g16","g5"], vec!["g16"], vec!["g16"], vec!["g16"]),
			("5001aabbcc5001aabbccdddd5001aabbcc", vec!["g16","g5"], vec!["g16","g5"], vec!["g16","g5"], vec!["g16","g5"]),
			//use aD to match Ad, ignore-case
			("6001aabbcc6144aabb", vec!["g16","g6"], vec!["g16","g6"], vec!["g16","g6"], vec!["g16","g6"]), 
			("6001aabbcc6164aabb", vec!["g16","g6"], vec!["g16","g6"], vec!["g16","g6"], vec!["g16","g6"]), 
			("6001aabbcc6165aabb", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			// the critical pattern actually includes 7002aabbcc4165 
			// so it is discharged by g7
			("7001aabbcc4144aabb007002aabbcc4146", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("7001aabbcc4144aabb007002aabbcc4145", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("7001aabbcc4147aabb007002aabbcc4147", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("aa8001aabbcc41418002aabbcc61620000", vec!["g16","g8"], vec!["g16","g8"], vec!["g16"], vec!["g16"]), 
			("aa8001aabbcc4141dd8002aabbcc61620000", vec!["g16","g8"], vec!["g16","g8"], vec!["g16","g8"], vec!["g16","g8"]), 
			("aa8001aabbcc4141dd8002aabbcc61690000", vec!["g16","g8"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("aa9001aabbcc4161dd90026162636465aaaa", vec!["g16","g9"], vec!["g16","g9"], vec!["g16","g9"], vec!["g16","g9"]), 
			("100011aabbcc4161aaaa6363636362626262616161613131616161616262626263636363aaaa", vec!["g16","g10"], vec!["g16","g10"], vec!["g16","g10"], vec!["g16","g10"]), 
			// the middle "11" is replaced by "12", will confuse pm-reg discharged) by dfa and
			// critical pattern because the extraction of alt trick
			("100011aabbcc4161aaaa6363636362626262616161613132616161616262626263636363aaaa", vec!["g16"], vec!["g16"], vec!["g16","g10"], vec!["g16"]), 
			("110011aabbcc000000110012ccddcc", vec!["g16","g11"], vec!["g16","g11"], vec!["g16","g11"], vec!["g16","g11"]), 
			("120001aabbcc00616261626162616261626162313233313233646564656465646564650000", vec!["g16","g12"], vec!["g16","g12"], vec!["g16","g12"], vec!["g16","g12"]), 
			("120001aabbcc00616261626162616261626162313433313233646564656465646564650000", vec!["g16"], vec!["g16"], vec!["g16","g12"], vec!["g16"]), 
			//not matching the bound {1,2}, will fail pm
			("120001aabbcc00616261626162616261626162313233313233131333132333132333132333646564656465646564650000", vec!["g16","g12"], vec!["g16","g12"], vec!["g16"], vec!["g16"]), 
			//discharged by DFA approach put an "a" into the ["g16",bcde]{2}, whill be discovered (discharged) by dfa
			("130001aabbcc313262623334", vec!["g16","g13"], vec!["g16","g13"], vec!["g16","g13"], vec!["g16","g13"]), 
			("130001aabbcc313262613334aacd", vec!["g16","g13"], vec!["g16","g13"], vec!["g16","g13"], vec!["g16"]), 
			//discharged by DFA because the "00" byte after 
			// fc (which violates the pattern on !(00|00)
			("68656164e7fc0000003668686561", vec!["g16","g14"], vec!["g16","g14"], vec!["g16","g14"], vec!["g16"]),
			("15001ccddee", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("aa16002ccddee1122", vec!["g16"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			("aa17002ccddee1122", vec!["g16", "g17"], vec!["g16", "g17"], vec!["g16", "g17"], vec!["g16", "g17"]), 
			//cannot charge because =0 by bag still returns Maybe even if 17001 is there.
			("aa17002ccddee1122aaabb17001ccddee", vec!["g16", "g17"], vec!["g16", "g17"], vec!["g16", "g17"], vec!["g16"]), 
			("aa18002ccddee1122aaabb18001ccddee", vec!["g16", "g18"], vec!["g16", "g18"], vec!["g16", "g18"], vec!["g16", "g18"]), 
			("aa18002ccddee1122aaabb18001ccddee112218001ccddee00", vec!["g16", "g18"], vec!["g16", "g18"], vec!["g16", "g18"], vec!["g16"]), 
			("aa19002ccddee1122aaabb19001ccddee112219001ccddee00", vec!["g16", "g19"], vec!["g16", "g19"], vec!["g16", "g19"], vec!["g16", "g19"]), 
			//discharged by bag
			("aa19002ccddee1122aaabb19001ccddee112219001ccddee00", vec!["g16", "g19"], vec!["g16", "g19"], vec!["g16", "g19"], vec!["g16", "g19"]), 
			//discharged by all except critical pattern, because only 19001ccdeee is used
			("ccddee1122aaabb19001ccddee1122", vec!["g16", "g19"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			//will satisfy g20 because there are two matches
			("201001aaccee00201003aaccee11201002aacceebb201001aaccee00201002aacceeffff", vec!["g16", "g20"], vec!["g16", "g20"], vec!["g16", "g20"], vec!["g16","g20"]), 
			//will fail g20 because ONLY has >1 match
			("201001aaccee00201003aaccee11201002aacceebb201001aaccee00201003aacceedddd", vec!["g16", "g20"], vec!["g16", "g20"], vec!["g16", "g20"], vec!["g16","g20"]), 
			("201001aaccee00201003aaccee11201002aacceebb201001aaccee00", vec!["g16", "g20"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			//will fail bag of words but critical section will pass
			("2111ace002112ace002121ace002131ace00", vec!["g16", "g21"], vec!["g16"], vec!["g16"], vec!["g16"]), 
			//will fail pm-reg as seq reversed for 2121ace and 2122ace
			("2111ace002112ace002122ace002121ace002131ace002132ace002111ace002112ace002122ace002121ace002132ace002131ace", vec!["g16", "g21"], vec!["g16", "g21"], vec!["g16"], vec!["g16"]), 
			("2211ace12342212ace002221ace12342222ace002231ace12342232ace2211ace12342212ace002221ace12342222ace002231ace12342232ace", vec!["g16", "g22"], vec!["g16", "g22"], vec!["g16", "g22"], vec!["g16", "g22"]), 
			//will pass pm-reg but fail DFA because it does not handle
			//the restricted class nicely
			("2211ace01002212ace002221ace01002222ace002231ace01002232ace2211ace12342212ace002221ace12342222ace002231ace12342232ace", vec!["g16", "g22"], vec!["g16", "g22"], vec!["g16", "g22"], vec!["g16"]), 
		];
		for tc in test_cases{
			let s = tc.0;
			let set_crit = tc.1.into_iter().map(|s| s.to_string())
				.collect::<HashSet<String>>();
			let set_bag= tc.2.into_iter().map(|s| s.to_string())
				.collect::<HashSet<String>>();
			let set_pm= tc.3.into_iter().map(|s| s.to_string())
				.collect::<HashSet<String>>();
			let set_dfa= tc.4.into_iter().map(|s:&str| s.to_string())
				.collect::<HashSet<String>>();
			let nibbles = hex_to_u8(s);
			let act = quick_discharge_file_by_crit_bag_pm("tc", &nibbles,
				&v_sigs, &v_sigs_no_crit_pat,
				&map_crit_pat, &map_crit_pat_igc,
					&dfa_crit, &dfa_bag, &dfa_crit_igc,
					&dfa_bag_igc, false, &cfg,
					&sig_to_id).0;
			assert!(act.crit==set_crit, "ERROR: s: {}. act.crit: {:?} != set_crit: {:?}", s, act.crit, set_crit);
			assert!(act.bag==set_bag, "ERROR: s: {}. act.bag: {:?} != set_bag: {:?}", s, act.bag, set_bag);
			assert!(act.pm==set_pm, "ERROR: s: {}. act.pm: {:?} != set_pm: {:?}", s, act.pm, set_pm);
			assert!(act.all_dfa==set_dfa, "ERROR: s: {}. act.dfa: {:?} != set_dfa: {:?}", s, act.all_dfa, set_dfa);
		}

	}
}

