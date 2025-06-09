/// Common utility related to DFA, ACDFA, and NFA
/*
 Created 01/04/2024
 Refactored 01/17/2024
 Revised: 06/11/2024: removed b_ignore logic to ACDFA
 Ported: 07/24/2024
*/

extern crate rustomaton;
extern crate aho_corasick;
extern crate regex;
use std::collections::{HashSet};
use self::aho_corasick::{dfa::DFA as ACDFA};
use rustomaton::{
	nfa::{NFA},
	regex::{Regex as Regex2},
	automaton::{Automata,Buildable},
	nfa::{ToNfa},
	dfa::{ToDfa, DFA as DFA}
};
use std::collections::HashMap;
use crate::strings::{find_first_match, is_sequential_regex};

/// return the clamav alphabet
pub fn clamav_alphabet()->HashSet<char>{
    vec!['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'].into_iter().map(char::from).collect()
}

/// check if two are equivalent
pub  fn nfa_eq(nfa1: &NFA<char>, nfa2: &NFA<char>)->bool{
	nfa1.contains(nfa2) && nfa2.contains(nfa1)
}

/// return an empty NFA for empty set of strings
pub fn empty_nfa() -> NFA<char>{
	NFA::from_raw(
		clamav_alphabet(),
		HashSet::new(),
		HashSet::new(),
		Vec::new(),
	).unwrap()
}

/// return an true DFA for any string
pub fn full_dfa() -> DFA<char>{
	Regex2::<char>::parse_with_alphabet( clamav_alphabet(), ".*" ).unwrap().to_dfa()
}

/// build fa given the regular expression
/// when b_neg is set, negate it
pub fn build_dfa(s_reg: &str, b_neg: bool) -> DFA<char>{
	let mut dfa = Regex2::<char>::parse_with_alphabet( clamav_alphabet(), s_reg ).unwrap().to_dfa();
	if b_neg {
		dfa = dfa.negate();
	}
	dfa
	//let _prev_size = dfa.transitions.len();
	//let dfa2 = dfa.minimize();
	//println!("DEBUG USE 333: BEFORE minimize: {}, after: {}", _prev_size, dfa2.transitions.len());
	//dfa2
}

/// build NFA that accepts  (the original rustomaton is too slow)
pub fn nfa_at_most(n: usize) -> NFA<char>{
	let alpha = clamav_alphabet();
	let mut inits = HashSet::<usize>::new();
	inits.insert(0);
	inits.insert(n);
	let mut finals = HashSet::<usize>::new();
	finals.insert(n);
	let mut transitions:Vec<HashMap<char, Vec<usize>>> = (0..n).into_iter()
	.map(|i|
			(&alpha).into_iter().map(|v| (*v, vec![i+1, n])).collect()
	).collect();
	transitions.push( (&alpha).into_iter().map(|v| (*v, Vec::<usize>::new())).collect() );

	NFA::<char>::from_raw(alpha, inits, finals, transitions).expect("nfa fails")
}


/// build nfa given the regular expression
/// when b_neg is set, negate it (rustomaton not good handling .?.?...
pub  fn build_nfa_slow(s_reg: &str) -> NFA<char>{
	Regex2::<char>::parse_with_alphabet(clamav_alphabet(), s_reg)
		.unwrap().to_nfa()
}


/// if its is_sequential_regex do it first.
pub fn build_nfa_fast(s_reg: &str) -> NFA<char>{
	let mut cur_str = String::from(s_reg);
	//last pattern prevents . followed by a question mark or star
	let patterns = vec![ "[0-9a-f]+", "(\\.\\*)+", "(\\.\\?)+", "(\\.)+"]; 
	let mut vec_nfas = vec![];
	while cur_str.len()>0{
		//1. find the pattern
		let mut res = None;
		let mut idx = 0;
		while idx<patterns.len(){
			res = find_first_match(patterns[idx], &cur_str);
			if !res.is_none() && res.clone().unwrap().1==0 {break;}
			idx +=1;
		}
		assert!(!res.is_none(), "build_nfa_fast failed on s_reg: {}, cur_str: {}", s_reg, cur_str);

		//2. process the pattern
		let (mut subs, pos) = res.unwrap();
		if cur_str.len()>subs.len() && (&cur_str[subs.len()..subs.len()+1]=="*" || &cur_str[subs.len()..subs.len()+1]=="?"){
			subs = subs[0..subs.len()-1].to_string(); //to prevent taking the "." for next op
		}
		assert!(pos==0, "pos need to be 0");
		let item_nfa = if idx==0{//constant string
			build_nfa_slow(&subs)
		}else if idx==1{//.*
			build_nfa_slow(".*")
		}else if idx==2{//.?.? sequence
			nfa_at_most(subs.len()/2)
		}else if idx==3{//....
			build_nfa_slow(&subs)
		}else{ 
			panic!("unknown idx to handle")
		};
		vec_nfas.push(item_nfa);
		cur_str = cur_str[pos + subs.len() ..].to_string();
	}

	let mut final_nfa = vec_nfas[0].clone();
	for id in 1..vec_nfas.len(){
		final_nfa = final_nfa.concatenate(vec_nfas[id].clone());
	}
	final_nfa
}

/// if its is_sequential_regex do it first.
pub fn build_nfa(s_reg: &str, b_neg: bool) -> NFA<char>{
	let b_test = false;
	let nfa = if is_sequential_regex(s_reg){
		build_nfa_fast(s_reg)
	}else{
		build_nfa_slow(s_reg)
	};
	if b_test{
		println!(" DEBUG USE 102: test_build_nfa ... s: {}", s_reg);
		let nfa2 = build_nfa_slow(s_reg);
		assert!(nfa==nfa2, "incorrect build_nfa");
	}

	if b_neg {nfa.negate()} else {nfa}
}


/// return (states, trans)
pub fn size_dfa(fsa: &DFA<char>)->(usize, usize){
	let num_states = fsa.transitions.len();
	let mut num_trans = 0;
	for trans in &fsa.transitions{
		num_trans += trans.len();
	}
	(num_states, num_trans)
}

/// return the num_states and num_trans
pub fn size_nfa(fsa: &NFA<char>)->(usize, usize){
	let num_states = fsa.transitions.len();
	let mut num_trans = 0;
	for trans in &fsa.transitions{
		num_trans += trans.len();
	}
	(num_states, num_trans)
}


/// return total of NFA size
pub fn get_total_size(v: &Vec<Vec<NFA<char>>>)->(usize, usize){
	let mut sum_states = 0;
	let mut sum_trans = 0;
	for vec in v{
		for fsa in vec{
			let (s,t) = size_nfa(&fsa);
			sum_states += s;
			sum_trans += t;
		}
	}
	(sum_states, sum_trans)
}

/// biuld ACDFA
pub fn build_ac_dfa(patterns: &Vec<String>)
	->ACDFA{
	let dfa = ACDFA::new(patterns).unwrap();

	dfa
}
