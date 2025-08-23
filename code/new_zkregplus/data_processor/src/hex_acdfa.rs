/// Hexidecimal AC-DFA.
/// This is an adaptor of the aho-crasick package of DFA version
/// with the restriction that the alphabet is 4-bit nibble set (16 elements)
/* Created 01/23/2024
 	Revised: 06/08/2024. Added serde serialization
 	Revised: 06/10/2024. Added handling of case-insensitivity
	Refactored: 07/24/2024
*/

extern crate aho_corasick;
extern crate serde;
use rayon::iter::{IntoParallelRefIterator,ParallelIterator,IndexedParallelIterator};
use std::collections::{HashMap,HashSet};
use aho_corasick::{automaton::{Automaton},dfa::DFA as ACDFA,Anchored, state_id_to_usize, pattern_id_to_usize};
use serde::{Serialize, Deserialize};
use utils::{logger::{flog,log,LOG1}, data::hex_to_u8};
use crate::{clam_db::{RANGE2_BIT}};
use ark_ff::{Zero};


pub const DEFAULT_ACDFA_DA_BITS:usize = 2; //bits to represent id
pub const B_DEBUG:bool = true;

#[derive(Serialize, Deserialize,Clone)]
pub struct HexACDFA{
	/// DFA ID
	pub id: usize,
	/// the number of bits to represent DFA ID
	pub id_bits: usize,
	/// number of states
	pub num_states: usize,
	/// state_bits. id_bits + state_bits is the TOTAL bits for state ID
	pub state_part_bits: usize,
	/// patterns
	pub patterns: Vec<String>,
	/// outputs (from ID to pattern ID)
	pub outputs: HashMap<usize,Vec<usize>>,
	/// transitions (from ID to vector of 16 element)
	pub trans: HashMap<usize, Vec<usize>>,
	/// init state
	pub init_state: usize,
	/// number of accept states
	pub num_acc_states: usize,
	/// whether this ACDFA is for case insensitivity
	pub b_case_ignore: bool,
	/// maps from pattern to its id in patterns	
	pub pattern_to_id: HashMap<String, usize>,
	/// accept states ID for pattern
	pub pattern_to_accept_ids: Vec<Vec<usize>>,
}

impl HexACDFA{
	/// create a new HexACDFA (default case sensitive)
	pub fn new(dfa_id: usize, patterns: &Vec<String>)->HexACDFA{
		Self::new_adv(dfa_id, patterns, false)
	}

	/// We generate subsig_id combined within state_part_bits
	/// NOTE: subsig_id should be ADJUSTED value (+1).
	/// Keep it for legacy, call gen_subsig_id_worker
	pub fn gen_subsig_id(&self, sig_id: usize, subsig_id: usize)->usize{
		assert!(sig_id!=0 && subsig_id!=0);
		Self::gen_subsig_id_worker(sig_id, subsig_id)
	}

	/// We generate subsig_id combined within state_part_bits
	/// NOTE: subsig_id should be ADJUSTED value (+1).
	pub fn gen_subsig_id_worker(sig_id: usize, subsig_id: usize)->usize{
		let bits = RANGE2_BIT;
		let bit_part1 = bits*2/3; //16 for accomodating 64k sigs for bits 24
		let bit_part2 = bits - bit_part1;
		assert!(sig_id < (1<<bit_part1));
		assert!(subsig_id < (1<<bit_part2));
		let res = (sig_id<<bit_part2) + subsig_id;

		res
	}

	/// convert a hex string to its lower version
	/// e.g. [6,1, 4, 1] ("aA") 
	/// is converted to [6,1,6,1] ("aa") and keep other chars
	/// the same as they are. 
	/// This is to prevent the capitical case letters in 
	/// the pattern string causes trouble for others.
	/// For instance, if the system processes "Ab" first, it will
	///    redirect transitions for "a".
	/// But then if the system processes "ac" next, it will redirect
	///    "A" agagin, which causes incorrect translation when future
	/// patterns depend on "A" and "a".
	pub fn to_v8_lower(s_src: &Vec<u8>)->Vec<u8>{
		let mut s = s_src.clone(); 
		for i in (0..s.len()).step_by(2){
			let ch1 = s[i];
			if i+1>=s.len() {break;}
			let ch2 = s[i+1];
			let val = ch1*16 + ch2;
			if val>=0x41 && val<=0x5a{
				let newval = val-0x41 + 0x61;
				let newch1 = newval/16;
				let newch2 = newval%16;
				s[i] = newch1;
				s[i+1] = newch2;
			} 
		}

		s
	}

	//from the start_state, find the the collection of init state
	//that reaches the given end_state
	fn rev_run(
		end_states: &Vec<usize>, 
		s: &Vec<u8>, 
		trans: &Vec<Vec<Vec<usize>>>
	)-> HashSet<usize>{
		println!("DEBUG USE 6200.8 ---  end_states: {:#?}", end_states);
		let mut cur_set = end_states.iter().map(|x| *x)
			.collect::<HashSet::<usize>>();
		for i in 0..s.len(){
			let idx = s.len()-1 -i;
			let ch = s[idx];
			assert!(ch<16);
			let idx_ch = ch as usize;
			cur_set = cur_set.into_iter().map(|state|{
				trans[state][idx_ch].clone()
			}).flatten().into_iter().filter(|prev| !prev.is_zero())
			.map(|prev| prev) //filter for avoiding trap state 0
			.collect::<HashSet<usize>>();
			println!(" -- DEBUG USE 6200.9 after ch: {} => {:#?}", ch, cur_set);
		}
		cur_set
	}

	/// create a new HexACDFA
	pub fn new_adv(dfa_id: usize, patterns: &Vec<String>, b_case_ignore: bool)->HexACDFA{
		let b_debug = true;
		if b_debug{
			println!("DEBUG USE 6200: HexACDFA::new_adv b_igc: {}, patterns: {:#?}", b_case_ignore, patterns);
		}
		//1. build the ACDFA DFA version
		assert!(dfa_id<(1<<DEFAULT_ACDFA_DA_BITS), "DEFAULT_ACDFA_DA_BITS:{} too small! id: {} >= (1<<DEFAULT_ACDFA_DA_BIS)", DEFAULT_ACDFA_DA_BITS, dfa_id);
		let vecu8 = patterns.iter().map(|s| {hex_to_u8(s)}).collect::<Vec<Vec<u8>>>();
		let vecu8 = if b_case_ignore{
				//need to convert all strings to lower case to avoid
				//confusion, see comment v8_to_lower
				vecu8.par_iter().map(|s| Self::to_v8_lower(s))
					.collect::<Vec<Vec<u8>>>() 
		}else{
			vecu8
		};
		let dfa = ACDFA::new(&vecu8).unwrap();
		let dfa_init = state_id_to_usize(dfa.start_state(Anchored::No).unwrap())/32;

		let alpha_size = dfa.alphabet_len;
		assert!(alpha_size==17, "alpha_size: {} !=17, consider providing patterns covering all 16 hex digits!", alpha_size); //implies: each state has 32 transitions
		let num_states = dfa.num_states();
		let dfa_trans = &dfa.trans;
		assert!(num_states*32==dfa_trans.len(), "states*32!=trans_len. states: {}, trans: {}", num_states, dfa_trans.len());
		let dfa_outputs = &dfa.matches;
		let acc_states = dfa.get_max_match_id()/32-1;
		assert!(acc_states==dfa_outputs.len(), "acc_states!=dfa_outputs.len()");
		assert!(num_states<(1<<RANGE2_BIT), "num_states: {}> 1<<RANGE2_BIT", num_states);

		//1.5 build a state map which maps from original ACDFA states to
		//new state. In the original ACDFA state [0,1] are NOT final
		//states, then [2, 2+acc_states) are the final states, then
		//the rest are non-accepting states
		//we map [0,1] -> [acc_states, acc_states+1]
		//		 [2, acc_states+1] -> [0, acc_states-1]
		//		 [acc_states+2, END] -> [acc_states+2, END] the same
		let mut map_states = HashMap::<usize, usize>::new();
		for i in 0..num_states{
			if i<2{
				map_states.insert(i, acc_states+i);
			}else if i>=2 && i<=acc_states+1{
				map_states.insert(i, i-2);
			}else{
				map_states.insert(i, i);
			}
		}


		//2. build up the transitions
		// keep the original state (but ignore deadsstead 0, and ignore
		// all other alphabet char other than 16
		let mut hash_trans = HashMap::<usize,Vec<usize>>::new();
		let mut hash_rev_trans = if b_case_ignore{
			vec![vec![vec![];16]; num_states]
		}else {vec![vec![vec![];16];0]}; //hash_rev_trans[state]
									 //has 16 elements for each char
									 //we need it fore igc case only for
									 //making updates of transitions.
		for i in 1..num_states{
			let idx = i * 32;
			let mut vec = vec![];
			let new_state = Self::state_id(dfa_id, map_states[&i]);
			for j in 0..16{
				let dst = state_id_to_usize(dfa_trans[idx+j])/32;
				let new_dst = Self::state_id(dfa_id, map_states[&dst]);
				vec.push(new_dst);
				if b_case_ignore{//only expand hash_rev_trans in i_igc mode
					if !hash_rev_trans[new_dst][j].contains(&new_state){
						hash_rev_trans[new_dst][j].push(new_state);
					}
				}
			}
			if hash_trans.contains_key(&new_state){
				panic!("ERROR already hash state: {} for i: {}", new_state, i);
			}
			hash_trans.insert(new_state, vec);
		}
		let state0 = Self::state_id(dfa_id, map_states[&0]);
		hash_trans.insert(state0, vec![state0; 16]); //loop to dead state itself
		if b_case_ignore{
			for j in 0..16{
				if !hash_rev_trans[state0][j].contains(&state0){
					hash_rev_trans[state0][j].push(state0);
				}
			}
		}

		//3. build up the outputs table
		let mut hash_outputs = HashMap::<usize,Vec<usize>>::new();
		let mut pattern_to_accept_ids = vec![vec![]; patterns.len()]; 
		for i in 0..acc_states{
			let state_id = Self::state_id(dfa_id, i);
			let mut vec = vec![];
			for pat_id in &dfa_outputs[i]{
				vec.push( pattern_id_to_usize(*pat_id) );
				pattern_to_accept_ids[*pat_id].push(state_id);
			}
			vec.sort();
			hash_outputs.insert(state_id, vec);
		}

		//4. build the pattern to IDs
		let pattern_to_id = patterns.iter().enumerate().map(|(i,p)|
			(p.to_string(), i)).collect::<HashMap<String,usize>>();
		assert!(num_states<(1<<RANGE2_BIT), "RANGE2_BITS too small, reset!");

		//5. if b-ignore case update the transition table
		//assumption: each alpha_numeric char is located at EVEN pos!
		//5.1 build the set of start_states for each string
		let _vec_start_states = if b_case_ignore{
			patterns.iter().enumerate().map(|(i,pat)|{
			let s = &vecu8[i];
			let pat_id = pattern_to_id.get(pat).unwrap();
			let ids = &pattern_to_accept_ids[*pat_id];
			let res = Self::rev_run(ids, s, &hash_rev_trans);

			res
			}).collect::<Vec<HashSet<usize>>>()
		}else{vec![]};

		//REMOVE ALTER ------------------
		if b_case_ignore{
			println!("DEBUG USE 6200.8: vec_start_states: {:#?}", _vec_start_states);
		}
		//REMOVE ALTER ------------------ ABOVE

		let init_state =  Self::state_id(dfa_id, map_states[&dfa_init]);
		if b_case_ignore{
			for pat in patterns{
				println!("DEBUG USE 6200.6: pat: {}", pat);
			/*
				let mut cur_state = init_state;
				for i in (0..s.len()).step_by(2){
					let ch1 = s[i];
					let next_state = hash_trans.get(&cur_state)
						.unwrap()[usize::from(ch1)];
					if i+1>=s.len() {break;}
					let ch2 = s[i+1];
					let next_state2 = hash_trans.get(&next_state)
						.unwrap()[usize::from(ch2)];
					let val = ch1*16 + ch2;
					if (val>=0x41 && val<=0x5a) || (val>=0x61 && val<=0x7a){
						let newval = if val>=0x41 && val<=0x5a 
							{(val - 0x41) + 0x61} else {(val-0x61) + 0x41};
						let newch1 = newval/16;
						let newch2 = newval%16;
						if b_debug{
							println!("DEBUG USE 6200.1: old_val: 0x{:x}, new_val: 0x{:x}, cur_state:{} -> {} -> {}", val, newval, cur_state, next_state, next_state2);
						}
						hash_trans.entry(cur_state).and_modify(|v| v[usize::from(newch1)] = next_state);
						hash_trans.entry(next_state).and_modify(|v| v[usize::from(newch2)] = next_state2);
					} 
					cur_state = next_state2;
				}
			*/
			}//for s in pattern
		}



		//4. return
		let res = HexACDFA{
			id: dfa_id,
			id_bits: DEFAULT_ACDFA_DA_BITS,
			num_states: num_states,
			state_part_bits: RANGE2_BIT,
			patterns: patterns.clone(),
			num_acc_states: hash_outputs.keys().len(),
			outputs: hash_outputs,
			trans: hash_trans,
			init_state: init_state,
			b_case_ignore: b_case_ignore,
			pattern_to_id,
			pattern_to_accept_ids,
		};

		//REMOVE LATER ----------------------
		if b_case_ignore{
		use utils::data::str_to_u8;
		let s1 = str_to_u8("aaaaa");
		let s2 = str_to_u8("9uUuuuu257890abcdefAaaaa123bbbbcC");
		println!("=== DEBUG USE 6200.2 for aaaaa");
		let _acc1 = res.acc_path(&s1);
		println!("DEBUG USE 6200.2: for s2: 9uUuu...Aaaaa123bbbcC");
		let _acc2 = res.acc_path(&s2);
		panic!("STOP HERE 1001");
		}
		
		//REMOVE LATER ---------------------- ABOVE

		res
	}

	/// if word is accepted by the DFA, return the corresponding IDs.
	/// if word is not an accepted word, panic
	pub fn word_to_state_id(&self, w: &String)->Vec<usize>{
		let pat_id: usize = *self.pattern_to_id.get(w).expect(
			&format!("canot find word: {}", w));
		self.pattern_to_accept_ids[pat_id].to_vec()
	}

	/// print stats
	pub fn log_stats(&self, prefix: &str, vlog: &mut Vec<String>){
		flog(LOG1, &format!("==== Status of ACDFA {} =====\n HEX-AC-DFA id: {}, num_states: {}, patterns: {}, accept_states: {}, init_state: {}", prefix, self.id, self.num_states, self.patterns.len(), self.outputs.keys().len(), self.init_state), vlog);
		let mut max_output_size = 0;
		let mut total_output_size = 0;
		for i in 0..self.num_acc_states{
			let state_id = Self::state_id(self.id, i);
			let ilen = self.outputs.get(&state_id).unwrap().len();
			if ilen>max_output_size{max_output_size = ilen;}
			total_output_size += ilen;
		}
		flog(LOG1, &format!("MAX output words for a final state: {}, avg: {}", 
			max_output_size, total_output_size/self.num_acc_states), vlog);
	}

	/// return a hashset, which given a critical pattern map (to sigs),
	/// return for each state, a vector of signatures that are triggered. 
	pub fn state_to_sig_ids(&self, map_crit_pat: &HashMap<String,Vec<String>>, sig_to_id: &HashMap<String,usize>) -> HashMap<usize, Vec<usize>>{
		(0..self.num_acc_states).map(|x| {
			let sid = self.long_state_id(x);
			let vout = self.outputs.get(&x)
				.expect(&format!("Unable to get pattern for state: {}", x));
			let mut set_sigs = HashSet::<String>::new();
			for pat_id in vout{
				let pat = &self.patterns[*pat_id];
				let sigs = map_crit_pat.get(pat).expect(
					&format!("Unable to get {} from map_crit_pat", pat));
				for sig in sigs {set_sigs.insert(sig.clone());}
			}
			let mut v_sigid= set_sigs.iter()
				.map(|s| *sig_to_id.get(s).expect(
					&format!("Unable to find id for {}", s)))
				.collect::<Vec<usize>>();
			v_sigid.sort();
			(sid, v_sigid)
		}).collect::<HashMap::<usize, Vec<usize>>>()
	}

	/// print stats
	pub fn log_stats_adv(&self, prefix: &str, map_crit_pat: &HashMap<String,Vec<String>>, sig_to_id: &HashMap<String, usize>, vlog: &mut Vec<String>){
		flog(LOG1, &format!("==========Adv Stats of ACDFA {} ==========================", prefix), vlog);
		flog(LOG1, &format!("HEX-AC-DFA id: {}, num_states: {}, patterns: {}, accept_states: {}, init_state: {}", self.id, self.num_states, self.patterns.len(), self.outputs.keys().len(), self.init_state), vlog);
		let mut max_output_size = 0;
		let mut total_output_size = 0;
		let states_to_sigs = self.state_to_sig_ids(map_crit_pat, sig_to_id);
		for i in 0..states_to_sigs.len(){
			let vec = states_to_sigs.get(&self.long_state_id(i)).expect(
				&format!("can't get output vec for state: {}", i)).to_vec();
			total_output_size += vec.len();
			max_output_size = if max_output_size>vec.len() {max_output_size}
				else {vec.len()};
		}
		flog(LOG1, &format!("  MAX output sig: {}, avg sigs/acc state: {}", max_output_size, total_output_size/states_to_sigs.len()), vlog);
		flog(LOG1, &format!("=================================="), vlog);
	}

	/// generate the acceptance path for a vector of nibbles
	/// return the vector of state IDs
	pub fn acc_path(&self, s: &Vec<u8>)->Vec<usize>{
		let mut src = self.init_state;
		let mut dst;
		let mut vec = vec![];
		vec.push(src);
		for i in 0..s.len(){
			let ch = s[i];
			dst = self.trans.get(&src).unwrap()[usize::from(ch)];
			if B_DEBUG{
				if self.is_accept(dst){
					log(LOG1, &format!("{} - {} -> {}: {:?}", src, ch, dst, &self.outputs.get(&dst).unwrap()));
				}else{
					log(LOG1, &format!("{} -{} -> {}", src, ch, dst));
				}
			}
			vec.push(dst);
			src = dst;
		}

		vec
	}



	/// each element of return is a tuple of (state_id, step_id)
	pub fn packed_acc_path(&self, s: &Vec<u8>)->Vec<(usize, usize)>{
		let path = self.acc_path(s);
		let mut res = vec![];
		for id in 0..path.len(){
			let state = path[id];
			if self.is_accept(state){
				res.push( (state, id) );
			}
		}
		res
	}

	/// return whether state_idx is a final state
	pub fn is_final(&self, state_idx: usize)-> bool{
		state_idx < self.num_acc_states
	}
	/// given the final state indiex, return the related 
	/// signature names
	pub fn final_to_patterns(&self, final_state_idx: usize)->HashSet<String>{
		assert!(self.is_accept(final_state_idx));
		let vec = &self.outputs[&final_state_idx];
		let mut res = HashSet::<String>::new();
		for id_pat in vec{
			res.insert( self.patterns[*id_pat].clone() );
		}
		res
	}

	/// from the acceptance path, collects the set of patterns
	pub fn get_patterns(&self, acc_path: &Vec<usize>)->HashSet<String>{
		let mut res = HashSet::<String>::new();
		for state in acc_path{
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				for id_pat in vec{
					res.insert( self.patterns[*id_pat].clone() );
				}
			}
		}

		res
	}

	/// for each string show the vector of positions
	pub fn get_pattern_pos(&self, acc_path: &Vec<usize>)->HashMap<String,Vec<usize>>{
		let mut res = HashMap::<String, Vec<usize>>::new();
		for (i, state) in acc_path.iter().enumerate(){
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				if vec.len()>10 {println!("WARN: vec.len: {} for state: {:?}", vec.len(), state);}
				for id_pat in vec{
					let pat = self.patterns[*id_pat].clone();
					let entry = res.entry(pat).or_insert_with(|| vec![]);
					entry.push(i);
				}
			}
		}
		res

	}

	/// from the acceptance path, collects the stats of patterns
	pub fn get_pattern_stats(&self, acc_path: &Vec<usize>)->HashMap<String, usize>{
		let mut res = HashMap::<String, usize>::new();
		for state in acc_path{
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				for id_pat in vec{
					let pat = self.patterns[*id_pat].clone();
					let entry = res.entry(pat).or_insert_with(|| 0);
					*entry += 1;
				}
			}
		}

		res
	}


	/// get the state id given dfa_id
	fn state_id(_dfa_id: usize, state_id: usize)->usize{
		let dfa_id = 0; //Since lookup table is 2D in proof, we do not build it
						//in state any more.
		(dfa_id<<RANGE2_BIT) + state_id
	}

	/// get the LONG VERSION of state id given dfa_id
	fn long_state_id(&self, state_id: usize)->usize{
		(self.id <<RANGE2_BIT) + state_id
	}

	/// map from state id to index in transition
	#[inline]
	pub fn state_to_idx(&self, state_id: usize) -> usize{
		//we do not embed dfaid into state id anymore
		state_id 
	}

	/// check if it is accept state
	#[inline]
	pub fn is_accept(&self, state_idx: usize) -> bool{
		// from state [2, 2+num_accept_states-1]
		// self.state_to_idx(state_idx) <= self.num_acc_states+1
		// from state [0, 0+num_accept_states-1]
		self.state_to_idx(state_idx) <= self.num_acc_states-1
	}
}

#[cfg(test)]
mod tests_hex_acdfa{
	use crate::hex_acdfa::*;
	use std::collections::{HashSet};
	use utils::data::{str_to_u8};

	// test if s generates the expected pattern set
	fn test_one_case(pats: &Vec<&str>, exp: &Vec<&str>, s: &str, bval: bool){
		let patterns = pats.into_iter().map(|s| {String::from(*s)}).collect();
		let dfa = HexACDFA::new(1, &patterns);
		let exp_set = exp.into_iter().map(|s| {String::from(*s)}).collect::<HashSet<String>>();
		let vu8 = hex_to_u8(&s);
		let set1 = dfa.get_patterns( &dfa.acc_path(&vu8) );
		assert!((set1==exp_set)==bval, "failed on s: {}", s);
	}

	#[test]
	fn test_word_to_accept_id(){
		let pats = vec!["0123456789abcdef1", "123", "abc", "345"].iter().
			map(|s| s.to_string()).collect::<Vec<String>>();
		let dfa = HexACDFA::new(1, &pats);
		for w in pats{
			let final_states = dfa.word_to_state_id(&w);
			for f in &final_states{
				let vec_word = dfa.outputs.get(&f).unwrap();
				let wid = dfa.pattern_to_id.get(&w).unwrap();
				let word2 = &dfa.patterns[*wid];
				assert!(vec_word.contains(wid));
				assert!(word2==&w);

			}
		}
	}

	// test if s generates the expected pattern set, ignore case
	fn test_one_case_ig(pats: &Vec<&str>, exp: &Vec<&str>, s: &str, bval: bool){
		let patterns = pats.into_iter().map(|s| {String::from(*s)}).collect();
		let dfa = HexACDFA::new_adv(1, &patterns, true);
		let exp_set = exp.into_iter().map(|s| {String::from(*s)}).collect::<HashSet<String>>();
		let vu8 = hex_to_u8(&s);
		let set1 = dfa.get_patterns( &dfa.acc_path(&vu8) );
		assert!((set1==exp_set)==bval, "failed on s: {}", s);
	}

	#[test]
	fn test_simple_hex_dfa(){
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012356", false);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012346", true);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012a123a123a6", false);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012a123a12346", true);
	}

	#[test]
	fn test_simple_hex_dfa_ignore_case(){
		//A - 0x41
		//a - 0x61
		//2nd entry is actually 'AbC'
		test_one_case_ig(&vec!["01234567789abcdef", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "6162633451", true);
		test_one_case_ig(&vec!["01234567789abcdef", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "5162633451", false);
		test_one_case_ig(&vec!["01234567789abcdef", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "6142433451", true);
		test_one_case_ig(&vec!["01234567789abcdef", "3031416243", "1235", "3451"],
			&vec!["3031416243", "3451"], "112230316142433451", true);
		test_one_case_ig(&vec!["01234567789abcdef", "3031416243", "1235", "3451"],
			&vec!["3031416243", "3451"], "112230311142433451", false);
		test_one_case_ig(&vec!["01234567789abcdef", "3031416243", "1235", "3451"],
			&vec!["3031416243", "3451"], "112230316242433451", false);
	}

	#[test]
	fn test_state_id(){
		//1. build up the acdfa and state_to_sigid
		let patterns = vec!["abc", "dabc", "cde", "1234567890abefdcaa"]
			.iter().map(|s|
			{String::from(*s)}).collect();
		let dfa = HexACDFA::new(1, &patterns);
		let mut map_crit_pat = HashMap::<String, Vec<String>>::new();
		map_crit_pat.insert(String::from("abc"), vec![
			String::from("sig1")]);
		map_crit_pat.insert(String::from("cde"), vec![
			String::from("sig0"),
			String::from("sig2")]);
		map_crit_pat.insert(String::from("dabc"), vec![
			String::from("sig0"),
			]);
		map_crit_pat.insert(String::from("1234567890abefdcaa"), vec![
			String::from("sig2"),
			]);
		let mut sig_to_id = HashMap::<String,usize>::new();
		sig_to_id.insert(String::from("sig0"), 0);
		sig_to_id.insert(String::from("sig1"), 1);
		sig_to_id.insert(String::from("sig2"), 2);
		sig_to_id.insert(String::from("sig3"), 3);
		let states_to_id = dfa.state_to_sig_ids(&map_crit_pat, &sig_to_id);
		let mut vlog = vec![];
		dfa.log_stats_adv("ACDFA", &map_crit_pat, &sig_to_id, &mut vlog);

		//2. test
		let arr_cases = vec![
			//test string and then expected sig ids
			("eabc", vec![1]),
			("edabc", vec![0, 1]),
			("aa1234567890abefdcaa", vec![2]),

		];
		for tc in arr_cases{
			let s = tc.0;
			let sigs = tc.1;
			let acc_path = dfa.acc_path(&hex_to_u8(&s));
			let acc_state = dfa.long_state_id(acc_path[acc_path.len()-1]);
			let act_sigs = states_to_id.get(&acc_state).unwrap().clone();
			assert!(sigs==act_sigs, "ERROR for s: {}, expected sigs: {:?}, actual: {:?}", s, sigs, act_sigs);
		}
		println!("DUMP states_to_id: {:?}", states_to_id);
	}

	#[test]
	fn test_v8_lower(){
		let samples = ["123ABC", "A4a5678"];
		for sample in samples{
			let s2 = sample.to_lowercase();
			let v8_1 = str_to_u8(&sample);
			let v8_2 = str_to_u8(&s2);
			let act_val = HexACDFA::to_v8_lower(&v8_1);
			assert!(act_val == v8_2);
		}
	}
}
