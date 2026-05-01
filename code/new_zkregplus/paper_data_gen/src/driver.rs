//! This module contains main driving functions of preprocessing signatures
//!
//! Created 01/17/2024
//! Modified 06/07/2024: added report_all_approach_stats 

extern crate rayon;
extern crate serde;
extern crate aho_corasick;
extern crate rustomaton;

//use self::rustomaton::nfa::{NFA};
use self::rayon::prelude::*;
//use self::aho_corasick::{automaton::Automaton,dfa::DFA as ACDFA,Input, Match, Anchored};

use data_proc::clamav::*;
use data_proc::common::*;
use data_proc::hex_acdfa::*;
use utils::os::*;
use utils::consts::*;
use std::collections::{HashMap,HashSet};
use std::collections::hash_map::Entry;


/// generate the critical and all patterns
/// src is the source of signatures, critical and all patterns
/// will be saved to the specified destination files
pub fn gen_patterns(job_id: usize, src:&str, sigtype: ClamSigType, dest_crit_file: &str, dest_all_pat_file: &str, dest_sig_file: &str) -> HashMap<String,Vec<usize>>{
	if 2>1 {panic!("THIS FUNCTION IS OUTDATED. Do not call.");}
	log(LOG1, &format!("generate patterns . \nsrc: {}", src));

	//1. read lines
	log(LOG1, &format!("preprocess subsignatures"));
	let subset_lines = &read_lines(src)[1..].to_vec();

	//2. get the signatures
	let mut v_sigs = vec![];
	if B_SINGLE_JOB_MODE{
		for line in subset_lines{
			let sig = gen_clamav_sig(&line, sigtype); 
			log(LOG2, &format!("{:?}", &sig));
			v_sigs.push(sig);
		}
	}else{
		v_sigs = subset_lines.par_iter().map(|s| gen_clamav_sig(s, sigtype)).collect();
	}
	let s_sigs = serde_json::to_string(&v_sigs).unwrap();
	write_to_file(dest_sig_file, &s_sigs);

	//3. collect the critical patterns
	log(LOG1, &format!("collect critical patterns and all patterns"));
	let mut map_crit_pat = HashMap::<String,Vec<String>>::new();
	let mut map_crit_pat_igc = HashMap::<String,Vec<String>>::new();
	let mut vec_all_pat:Vec<String>;
	//3.1 get critical pattern
	log(LOG2, &format!("collect critical patterns"));
	for sig in &v_sigs{ sig.add_critical_pattern(&mut map_crit_pat, &mut
		map_crit_pat_igc); }
	log(LOG1, &format!("#critical patterns: {}, #sigs: {}, #sigs_igc: {}", 
		map_crit_pat.len(), v_sigs.len(), map_crit_pat_igc.len()));
	let s_map_crit = serde_json::to_string(&map_crit_pat).unwrap();
	write_to_file(dest_crit_file, &s_map_crit);

	log(LOG2, &format!("collect all patterns"));
	let vec_pat:Vec<HashSet<String>> = 
		v_sigs.iter().map(|v|  v.collect_all_patterns()).collect();
	let mut hs_all = HashSet::<String>::new();
	for x in vec_pat{
		hs_all.extend(x);
	}
	vec_all_pat = hs_all.into_iter().collect();
	vec_all_pat.sort();
	write_lines(dest_all_pat_file, &vec_all_pat, true);
	log(LOG1, &format!("critical_patterns: {}, all_patterns: {}", map_crit_pat.keys().len(), vec_all_pat.len()));
		
	//4. generate mapping from all_patterns to sig_id
	let mut map_all = HashMap::<String, Vec<usize>>::new();
	for i in 0..v_sigs.len(){
		let sig = &v_sigs[i];
		let pats = sig.collect_all_patterns();
		for pat in pats{
			match map_all.entry(pat) {
            	Entry::Vacant(e) => { e.insert(vec![i]); },
            	Entry::Occupied(mut e) => { e.get_mut().push(i); }
        	}
		}
	}

	map_all

	//4. generate the vector of automaton
	/* DO NOT REMOVE! USE LATER!!!
	log(LOG2, &format!("generating automaton for each"));
	let mut vec_res = vec![];
	if B_SINGLE_JOB_MODE{
		for sig in v_sigs{
			vec_res.push( size_nfa(&sig.to_neg_automaton()) );
		}
		vec_res
	}else{
	 v_sigs.par_iter().map(|s| {let nfa= s.to_neg_automaton(); size_nfa(&nfa)}).collect() 
	}
	*/
}

/// check all executable and examing the signatures
/// via critical pattern near miss. That is: check
/// how many critical patterns are contained along the
/// acceptance path.
pub fn report_exec_critical_pat_stats(job_id: usize, crit_pat_file: &str){
	//1. read the info needed
	log(LOG1, &format!("--- REPORT of Number of Critical Patterns by All Bin Execs ---"));
	log(LOG1, &format!("read info from files ..."));
	let s_crit_pat = read_lines(crit_pat_file)[0].clone();
	let map_crit_pat:HashMap<String,Vec<String>> = serde_json::from_str(&s_crit_pat).unwrap();
	let vec_crit_pat:Vec<String>= map_crit_pat.keys().into_iter().map(|s| {String::from(s)}).collect();

	let dfa = HexACDFA::new(0, &vec_crit_pat);
	dfa.print_stats();
	//2. process each file and for each file get info
	// of num_of_sigs 
	let file_names = &read_lines(LIST_EXEC)[..];
	let mut vec_stats:Vec<Vec<usize>> = vec![vec![]; 32];
	for fpath in file_names{
		let nibbles = read_nibbles(fpath);
		let pats = dfa.get_patterns( &dfa.acc_path(&nibbles) );
		let mut set_sigs = HashSet::<String>::new();
		for pat in pats{
			let vec1 = map_crit_pat.get(&pat).unwrap();	
			for x in vec1{
				set_sigs.insert(String::from(x));
			}
		}
		let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
		vec_stats[file_len].push(set_sigs.len());
	}

	//3. report the stats
	print_stats_vec(&vec_stats);
}

/// print the stats vector
fn print_stats_vec(vec_stats: &Vec<Vec<usize>>){
	println!("SIZE\tCount\tAvg\tMax");
	let mut total = 0;
	let mut total_cnt = 0;
	for i in 0..vec_stats.len(){
		if vec_stats[i].len()>0{
			let max= vec_stats[i].iter().max().unwrap();
			let avg= vec_stats[i].iter().sum::<usize>()/vec_stats[i].len();
			println!("{}\t{}\t{}\t{}", i, vec_stats[i].len(), avg, max);
			total_cnt += vec_stats[i].len();
			total += vec_stats[i].iter().sum::<usize>();
		}else{
			println!("-\t-\t-\t");
		}
	}
	println!("TOTAL FILES: {}, AVG Near Miss: {}", total_cnt, total/total_cnt);
}

/// report the bag of words approach: for each signature organize
/// the same structure of DNF for each subpattern and for each pattern
/// set a bag of required words (missing any of them leads to failure)
/// generate all executable file. This applies to 
/// both the GeneralRegex type and PM-REG
pub fn report_bag_approach_stats(job_id: usize, sig_file: &str, exec_list_file: &str){
	//1. generate all signatures and their approximate patterns
	log(LOG1, &format!("preprocess subsignatures. THIS METHOD IS DEPRECATED. Only handles case-sensitive signatures"));
	let subset_lines = &read_lines(sig_file)[1..].to_vec();
	let mut v_sigs:Vec<ClamavSig> = subset_lines.par_iter().map(|s| gen_clamav_sig(s, ClamSigType::General)).collect();
	v_sigs.par_iter_mut().for_each(|s| s.gen_approx_bagwords(MIN_BAG_WORD_LEN));
	let pats = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();

	//2. collect all patterns and build dfa for match stats
	let dfa = HexACDFA::new(0, &pats);

	//2. for each signature and for each file, check match
	let mut vec_stats:Vec<Vec<usize>> = vec![vec![]; 32];
	let file_names = &read_lines(exec_list_file)[..];
	for fpath in file_names{
		let nibbles = read_nibbles(fpath);
		let hs= dfa.get_pattern_stats(&dfa.acc_path(&nibbles));
		let mut set_sigs = HashSet::<String>::new();
		for sig in &v_sigs{
			let res = sig.accepts_approx_bagwords_fast(&hs, &hs); //ERROR. 
				//NEED to generate hs_igc. Handle later
			if res==TriVal::Maybe || res==TriVal::True{
				set_sigs.insert( sig.name.clone() );
			}
		}
		println!("accepted sigs: {:?}", set_sigs);
		println!("=======================");
		let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
		vec_stats[file_len].push(set_sigs.len());
	}

	//4. process and print stats
	print_stats_vec(&vec_stats);
}

/// report the pm-reg approach.
pub fn report_pm_reg_approach_stats(job_id: usize, sig_file: &str, sigtype: ClamSigType, 
	exec_list_file: &str){
	//1. generate all signatures and their approximate patterns
	log(LOG1, &format!("preprocess subsignatures. This method is DEPRECATED. Only handle case-sensitive signatures"));
	let subset_lines = &read_lines(sig_file)[1..].to_vec();
	let mut v_sigs:Vec<ClamavSig> = subset_lines.par_iter().map(|s| gen_clamav_sig(s, sigtype)).collect();
	v_sigs.par_iter_mut().for_each(|s| {
		s.gen_approx_bagwords(MIN_BAG_WORD_LEN);
		s.gen_approx_pm_bounds(MIN_BAG_WORD_LEN);
	});
	let pats = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();

	//2. collect all patterns and build dfa for match stats
	let dfa = HexACDFA::new(0, &pats);

	//2. for each signature and for each file, check match
	let mut vec_stats:Vec<Vec<usize>> = vec![vec![]; 32];
	let file_names = &read_lines(exec_list_file)[..];
	for fpath in file_names{
		let nibbles = read_nibbles(fpath);
		let hs_occ = dfa.get_pattern_pos(&dfa.acc_path(&nibbles));
		let mut set_sigs = HashSet::<String>::new();
		for sig in &v_sigs{
			let res = sig.accepts_approx_pm_bounds(&hs_occ, &hs_occ); //TO IMPROVE
			if res==TriVal::Maybe || res==TriVal::True{
				set_sigs.insert( sig.name.clone() );
			}
		}
		let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
		vec_stats[file_len].push(set_sigs.len());
	}

	//4. process and print stats
	print_stats_vec(&vec_stats);
}

/// check all executable and examing the acceptance path
/// of patterns, report the ratio of acc_path/file_size
pub fn report_exec_path_stats(job_id: usize, all_pattern_file: &str, pat2sig: &HashMap<String,Vec<usize>>){
	//1. read the info needed
	log(LOG1, &format!("--- REPORT of Length of Acc Path by All Bin Execs ---"));
	log(LOG1, &format!("read info from files ..."));
	let vec_all_pat = read_lines(all_pattern_file);
	let dfa = HexACDFA::new(0, &vec_all_pat);
	dfa.print_stats_adv(pat2sig);
	//REMOVE LATER ----------
	return;
	//REMOVE LATER ---------- ABOVE

	//RECOVER LATER
	/*
	//2. process each file and for each file get info
	// of num_of_sigs 
	let file_names = &read_lines(LIST_EXEC)[..];
	let mut vec_stats:Vec<Vec<usize>> = vec![vec![]; 32];
	let mut total_full_len = 0;
	for fpath in file_names{
		let nibbles = read_nibbles(fpath);
		let packed_acc = dfa.packed_acc_path(&nibbles);
		let file_len = ((nibbles.len()/2).ilog2() + 1) as usize;
		total_full_len += nibbles.len()/2;
		vec_stats[file_len].push(packed_acc.len());
	}

	//3. report the stats
	println!("SIZE\tCount\tAvg\tMax");
	let mut total = 0;
	let mut total_cnt = 0;
	for i in 0..vec_stats.len(){
		if vec_stats[i].len()>0{
			let max= vec_stats[i].iter().max().unwrap();
			let avg= vec_stats[i].iter().sum::<usize>()/vec_stats[i].len();
			println!("{}\t{}\t{}\t{}", i, vec_stats[i].len(), avg, max);
			total_cnt += vec_stats[i].len();
			total += vec_stats[i].iter().sum::<usize>();
		}else{
			println!("-\t-\t-\t");
		}
	}
	println!("TOTAL FILES: {}, AVG Len: {}, Avg Saving: {} times", total_cnt, total/total_cnt, total_full_len/total);
	*/
}

/// report the size of ONE single signature
/// print format: SIZE: [1, 2, 3...]
/// because of rust cannot handle memory problem,
/// we call this function via linux extern command externally
/// and pick up the response in Python
pub fn report_dfa_size(sig_file:&str, idx: usize, timeout: usize){
	let subset_lines = &read_lines(sig_file)[..].to_vec().into_iter()
		.filter(|line| line.chars().next().unwrap()!='#')
		.collect::<Vec<String>>();
	let s= gen_clamav_sig(&subset_lines[idx], ClamSigType::General);
	//let v_sigs_src:Vec<ClamavSig> = subset_lines.iter().map(|s| gen_clamav_sig(s, ClamSigType::General)).collect();
	//let mut s= v_sigs_src[idx].clone();
	let (_name, bres, vec) = s.measure_dfa_size(timeout);
	println!("SIZE: {}, {}, {:?}", &s.name, bres, &vec);
}

/// report the dfa size of all sigs for every nth file
/// when nth is 1, it reports all stats
pub fn report_dfa_stats(job_id: usize, sig_file: &str, timeout_sec: usize, 
nth: usize, logfile: &str){
	let mut vlog = vec![];
	let mut timer = Timer::new();
	let subset_lines = &read_lines(sig_file)[1..].to_vec();
	let v_sigs_src:Vec<ClamavSig> = subset_lines.iter().map(|s| gen_clamav_sig(s, ClamSigType::General)).collect();
	flog_perf(LOG1, &format!("Load all sigs"), &mut timer, &mut vlog);
	let mut v_sigs = vec![];
	for i in 0..v_sigs_src.len(){
		if i%nth==0{ v_sigs.push(v_sigs_src[i].clone());}
	}
	let vreports = v_sigs.par_iter().map(|s| {
		let mut s = s.clone();
		s.gen_approx_bagwords(MIN_BAG_WORD_LEN);
		s.gen_approx_pm_bounds(MIN_BAG_WORD_LEN);
		let res = s.measure_dfa_size(timeout_sec);
        res

	}).collect::<Vec<(String, bool, Vec<usize>)>>();

	let mut vec_failed:Vec<String> = vec![];
	let mut total_size:usize = 0usize;
	let mut total_subsigs:usize = 0usize;
	for report in &vreports{
		let signame = &report.0;
		let bres = report.1;
		let vinfo = &report.2;
		if bres{
			total_size += vinfo.iter().sum::<usize>();
			total_subsigs += vinfo.len(); 
		}else{
			vec_failed.push(signame.clone());
		}
	}
	let avg_dfa = total_size/total_subsigs;
	flog(LOG1, &format!("=========\nREPORT DF Stats\n==========\nSrc File: {}, nth: {}", sig_file, nth), &mut vlog);
	flog(LOG1, &format!("Failed: {}, TotalSigs: {}, TotalSubSigs: {}, AvgDFAStates: {}", vec_failed.len(), v_sigs.len(), total_subsigs, avg_dfa), &mut vlog);
	flog(LOG1, &format!("---- Details of Failed ----"), &mut vlog);
	for signame in &vec_failed{
		flog(LOG1, &format!("{}", signame), &mut vlog);
	}

	write_lines(logfile, &vlog, true);
}

/// collect the generation automata time
pub fn report_automaton_gentime_general_regex(job_id: usize, ser_file: &str, timeout_sec: usize, start_idx: usize){
	//1. collect data
	let s_sigs = read_lines(ser_file)[0].clone();
	let vec_sigs:Vec<ClamavSig> = serde_json::from_str(&s_sigs).unwrap();
	let vec_sigs = &vec_sigs[start_idx..];
	log(LOG1, &format!("report_automaton_gen time, timeout: {} start_idx: {} of {}", timeout_sec, start_idx, vec_sigs.len()));
	let mut sizes:Vec<(bool, bool, (usize,usize), String)>;
	if B_SINGLE_JOB_MODE{
		log(LOG1, &format!("report_automaton_gentime SINGLE JOB MODE"));
		sizes = vec![];
		for s in vec_sigs{
			let (b_s, b_c, v, name) = s.to_neg_automaton(timeout_sec);
			sizes.push( (b_s, b_c, get_total_size(&v), name) );
		}
	}else{
		sizes = vec_sigs.par_iter().map(|s| {let (b_s, b_c, v, name) = s.to_neg_automaton(timeout_sec); (b_s, b_c, get_total_size(&v), name)}).collect();
	}

	//2. summarize
	let mut count_success = 0;
	let mut count_easy = 0;
	let mut count_complex = 0;
	let mut total_state_easy = 0;
	let mut total_state_complex = 0;
	let mut total_trans_easy = 0;
	let mut total_trans_complex = 0;
	for (b_s, b_c, (s, t), name) in &sizes{
		log(LOG1, &format!("name: {}, b_success: {}, b_complex: {}, total states, trans: ({},{})", &name, b_s, b_c, s, t));
		if *b_s{
			count_success += 1;
			if *b_c{
				count_easy += 1;
				total_state_easy += s;
				total_trans_easy += t;
			}else{
				count_complex += 1;
				total_state_complex += s;
				total_trans_complex += t;
			}
		}
	}
	println!("====REPORT of automaton for general regex: ======\n");
	println!("Total: {}, Success: {}, Fail: {}, for Timeout: {}",
		sizes.len(), count_success, sizes.len()-count_success, timeout_sec);
	println!("Easy: {}, States: {}, Trans: {}", count_easy, total_state_easy, total_trans_easy);
	println!("Complex: {}, States: {}, Trans: {}", count_complex, total_state_complex, total_trans_complex);
}

/// report all three approaches stats
pub fn report_all_discharge_approach_stats(job_id: usize, sig_file: &str, 
	sigtype: ClamSigType, exec_list_file: &str, logfile: &str, 
	b_read_cache: bool, cache_prefix: &str, set_needs_dfa: &HashSet<String>){
	let vdata = gen_report_all_discharge_approach_stats(sig_file,
		sigtype, exec_list_file, logfile, b_read_cache, cache_prefix, 
		set_needs_dfa);
	print_discharge_stats(&vdata, logfile);
}

pub fn print_discharge_stats(job_id: usize, vdata: &Vec<FailDischargeRecord>,
	logfile: &str){
	//1. first sort out all by len
	let mut vlog = vec![];
	let mut vec_stats: Vec<Vec<FailDischargeRecord>> = vec![vec![]; 32];
	for rec in vdata{ vec_stats[rec.flen].push(rec.clone()); }
	let b_more_details = false;

	//2. print details
	if b_more_details{
		flog(LOG1, &format!("==== STATS DETAILS ====="), &mut vlog);
		for i in 0..vec_stats.len(){
			println!("-------- log2(file): {} ----------", i);
			for rec in &vec_stats[i]{
				flog(LOG1, &format!("{}: \ncrit: {:?}, bag: {:?}, pm: {:?}, after_dfa: {:?}", 
					rec.fname, rec.crit, rec.bag, rec.pm, rec.all_dfa), &mut vlog);
			}
		}
	}

	//7. print summary
	let avg = |v: &Vec<usize>|->usize {
		let sum:usize = v.iter().sum();
		if sum==0 {0} else {sum/v.len()}
	};
	let max= |v: &Vec<usize>|->usize {
		let imax:usize = *v.into_iter().max().unwrap_or(&0);
		imax
	};
	let ct= |v: &Vec<usize>|->usize {
		let mut res = 0;
		for x in v{ if *x>0 {res +=1;} }
		res	
	};
	flog(LOG1, &format!("==== WARNING: UNABLE TO DISCHARGE by crit_gab_pm which needs DFA discharge ====="), &mut vlog);
	let mut all_cbp = HashSet::<String>::new();
	for rec in vdata{
		let crit_bag:HashSet<String> = rec.crit.clone().intersection(
			&rec.bag).cloned().collect();
		let crit_bag_pm:HashSet<String> = crit_bag.clone().intersection(
			&rec.pm).cloned().collect();
		if crit_bag_pm.len()>0{
			flog(LOG1, &format!("fname: {}, sigs: {:?}", rec.fname, &crit_bag_pm), &mut vlog);
			for x in crit_bag_pm {all_cbp.insert( x.clone() );}
		}
	}
	flog(LOG1, &format!("==== Needs to build DFA for the following ===========\n{:?}=========================\n", all_cbp), &mut vlog);
	flog(LOG1, &format!("==== WARNING: DFA could also not discharge the following ====="), &mut vlog);
	for rec in vdata{
		if rec.all_dfa.len()>0{
			flog(LOG1, &format!("fname: {}, sigs: {:?}", rec.fname, &rec.all_dfa), &mut vlog);
		}
	}
	flog(LOG1, &format!("==== WARNING: ISED could not discharge the following ====="), &mut vlog);
	for rec in vdata{
		if rec.ind_pm_reg.len()>0{
			flog(LOG1, &format!("fname: {}, filesize: {}, sigs: {:?}", rec.fname, ceil_log2(rec.flen), &rec.ind_pm_reg), &mut vlog);
		}
	}

	flog(LOG1, &format!("==== STATS SUMMARY (avg, max, count_non_zero) ========="), &mut vlog);
	flog(LOG1, &format!("Note: set b_optimize_pm to false in \ngen_report_all_discharge_approach_stats\n for accurate PM-REG data, otherwise it's filtered by prevoius step \n"), &mut vlog);
	flog(LOG1, &format!("-------------------------------------------------------"), &mut vlog);
	flog(LOG1, &format!("log(f)\tfiles\tcrit\tbag\tpm\tc_bag\tc_pm\tc_b_p\tdfa\tind_pm"), &mut vlog);
	for i in 0..vec_stats.len(){
		let mut vec_crit:Vec<usize> = vec![];
		let mut vec_bag:Vec<usize> = vec![];
		let mut vec_pm:Vec<usize> = vec![];
		let mut vec_crit_bag:Vec<usize> = vec![];
		let mut vec_crit_pm:Vec<usize> = vec![];
		let mut vec_crit_bag_pm:Vec<usize> = vec![];
		let mut vec_dfa:Vec<usize> = vec![]; //NOTE dfa data is ALREADY after applied first 3
		let mut vec_ind_pm: Vec<usize> = vec![];
		for rec in &vec_stats[i]{
			vec_crit.push( rec.crit.len() );
			vec_bag.push( rec.bag.len() );
			vec_pm.push( rec.pm.len() );
			let crit_bag:HashSet<String> = rec.crit.clone().intersection(
				&rec.bag).cloned().collect();
			let crit_pm:HashSet<String> = rec.crit.clone().intersection(
				&rec.pm).cloned().collect();
			let crit_bag_pm:HashSet<String> = crit_bag.clone().intersection(
				&rec.pm).cloned().collect();
			vec_crit_bag.push( crit_bag.len() );
			vec_crit_pm.push( crit_pm.len() );
			vec_crit_bag_pm.push( crit_bag_pm.len() );
			vec_dfa.push( rec.all_dfa.len() );
			vec_ind_pm.push( rec.ind_pm_reg.len() );
		}
		flog(LOG1, &format!("{} \t {} \t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{}\t({},{},{}))", 
			i, 
			vec_stats[i].len(),
			avg(&vec_crit),  max(&vec_crit), ct(&vec_crit), 
			avg(&vec_bag), max(&vec_bag), ct(&vec_bag), 
			avg(&vec_pm), max(&vec_pm), ct(&vec_pm), 
			avg(&vec_crit_bag), max(&vec_crit_bag), ct(&vec_crit_bag), 
			avg(&vec_crit_pm), max(&vec_crit_pm), ct(&vec_crit_pm),
			avg(&vec_crit_bag_pm) , max(&vec_crit_bag_pm), ct(&vec_crit_bag_pm) , 
			avg(&vec_dfa) , max(&vec_dfa), ct(&vec_dfa) , 
			avg(&vec_ind_pm) , max(&vec_ind_pm), ct(&vec_ind_pm) ), 
			&mut vlog);
	}

	flog(LOG1, &format!("====  Simpler Summary (avg, max, count_non_zero) ====="), &mut vlog);
	flog(LOG1, &format!("log(f)\tfiles\tcrit\tc_bag\tc_b_p\tdfa\tind_pm"), &mut vlog);
	for i in 0..vec_stats.len(){
		let mut vec_crit:Vec<usize> = vec![];
		let mut vec_bag:Vec<usize> = vec![];
		let mut vec_pm:Vec<usize> = vec![];
		let mut vec_crit_bag:Vec<usize> = vec![];
		let mut vec_crit_pm:Vec<usize> = vec![];
		let mut vec_crit_bag_pm:Vec<usize> = vec![];
		let mut vec_dfa:Vec<usize> = vec![]; //NOTE dfa data is ALREADY after applied first 3
		let mut vec_ind_pm:Vec<usize> = vec![]; //
		for rec in &vec_stats[i]{
			vec_crit.push( rec.crit.len() );
			vec_bag.push( rec.bag.len() );
			vec_pm.push( rec.pm.len() );
			let crit_bag:HashSet<String> = rec.crit.clone().intersection(
				&rec.bag).cloned().collect();
			let crit_pm:HashSet<String> = rec.crit.clone().intersection(
				&rec.pm).cloned().collect();
			let crit_bag_pm:HashSet<String> = crit_bag.clone().intersection(
				&rec.pm).cloned().collect();
			vec_crit_bag.push( crit_bag.len() );
			vec_crit_pm.push( crit_pm.len() );
			vec_crit_bag_pm.push( crit_bag_pm.len() );
			vec_dfa.push( rec.all_dfa.len() );
			vec_ind_pm.push( rec.ind_pm_reg.len() );
		}
		flog(LOG1, &format!("{} \t {} \t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})", 
			i, 
			vec_stats[i].len(),
			avg(&vec_crit),  max(&vec_crit), ct(&vec_crit), 
			avg(&vec_crit_bag), max(&vec_crit_bag), ct(&vec_crit_bag), 
			avg(&vec_crit_bag_pm) , max(&vec_crit_bag_pm), ct(&vec_crit_bag_pm) , 
			avg(&vec_dfa) , max(&vec_dfa), ct(&vec_dfa) , 
			avg(&vec_ind_pm) , max(&vec_ind_pm), ct(&vec_ind_pm) ), 
			&mut vlog);
	}

	flog(LOG1, &format!("====  Accepthance Path Stats ======="), &mut vlog);
	let accpath_len:usize=vdata.iter().map(|v| v.total_acc_path_len).sum();
	let hs_len:usize=vdata.iter().map(|v| v.total_hs_size).sum();
	let acc_states:usize=vdata.iter().map(|v| v.total_accepted).sum();
	flog(LOG1, &format!("hs_len/acc_path: {}%, hs_len: {}, accpath_len: {}", (hs_len as f64)*100.0/(accpath_len as f64), hs_len, accpath_len), &mut vlog);
	flog(LOG1, &format!("accepted states/acc_path: {}%, accepted_states: {}, accpath_len: {}", (acc_states as f64)*100.0/(accpath_len as f64), acc_states, accpath_len), &mut vlog);
	let pm_proj_ratios = vdata.iter().map(|v|
		if v.total_accepted>0 {
		(v.total_pm_witness_len as f64)/(v.total_accepted as f64)} else {0.0f64})
		.collect::<Vec<f64>>();
	let r_max: f64 = pm_proj_ratios.clone().into_iter().max_by(|a,b| a.total_cmp(b)).unwrap();
	let r_sum: f64 = pm_proj_ratios.iter().sum::<f64>();
	println!("DEBUG USE 201: r_sum: {}, len: {}", r_sum, pm_proj_ratios.len());
	let r_avg = r_sum/(pm_proj_ratios.len() as f64);
	flog(LOG1, &format!("pm_reg (sde) total projected table size/layer1 table: (avg: max): ({},{}). This indicates the cost of layer2 projectio", r_avg, r_max), &mut vlog);
	let pm_witness_ratio = vdata.iter().map(|v|
		(v.total_pm_witness_len as f64)/(v.total_acc_path_len as f64)).collect::<Vec<f64>>();
	let w_max: f64 = pm_witness_ratio.clone().into_iter().max_by(|a,b| a.total_cmp(b)).unwrap();
	let w_avg: f64 = pm_witness_ratio.iter().sum::<f64>()/(pm_proj_ratios.len() as f64);
	flog(LOG1, &format!("pm_reg (sde) total witness_len/file_size: (avg: max): ({},{}). This indicates total cost of discharging one file against ALL bag left sigs", w_avg, w_max), &mut vlog);


	write_lines(logfile, &vlog, false);
}


/// load the data needed for gen_report_discharge data
/// b_read is for load from cache. fname_prefix: the prefile
/// of file name, set needs_dfa: the set of signatures which
/// should generate DFA.
/// return: vector of signatures, map of critical patterns to signatures,
///  acdfa of critical pattern,
///  dfa for all patterns
fn load_discharge_data(job_id: usize, sig_file: &str, sigtype: ClamSigType,
	exec_list_file:&str, logfile:&str, b_read_cache: bool,
	fname_prefix: &str, set_need_dfa: &HashSet<String>) 
	-> (Vec<ClamavSig>, HashMap<String,Vec<String>>, HashMap<String,Vec<String>>, HexACDFA, HexACDFA, HexACDFA, HexACDFA){
	let mut vlog = vec![];
	let b_perf = true;
	let b_debug = B_DEBUG;
	let mut timer = Timer::new();
	flog(LOG1, &format!("==================\nREPORT All Discharge Stats\n==================\nnpreprocess subsignatures: {}, type: {:?}, exec_list: {}", sig_file, sigtype, exec_list_file), &mut vlog);

	//1. generate all signatures and their approximate patterns
	let v_sigs = if !b_read_cache{
		let subset_lines = &read_lines(sig_file)[1..].to_vec();
		let mut v_sigs:Vec<ClamavSig> = subset_lines.iter().map(|s| gen_clamav_sig(s, sigtype)).collect();
		v_sigs.par_iter_mut().for_each(|s| {
			println!("DEBUG USE 201: handle: s: {}", s.to_str());
			s.gen_approx_bagwords(MIN_BAG_WORD_LEN);
			s.gen_approx_pm_bounds(MIN_PM_WORD_LEN);
			if set_need_dfa.contains(&s.name){
				s.set_vec_automaton();
			}
		});
		if b_perf {flog_perf(LOG1, &format!("Generate signatures"), &mut timer,
			&mut vlog);}
		let s_sigs= serde_json::to_string(&v_sigs).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_v_sigs.txt", 
			fname_prefix, sigtype), &s_sigs);
		if b_perf {flog_perf(LOG1, &format!("Writing signatures"), &mut timer,
			&mut vlog);}
		v_sigs
	}else{
		let s_sigs= read(&format!("data/cache/{}_{:?}_v_sigs.txt", 
			fname_prefix, sigtype));
		let v_sigs:Vec<ClamavSig> = serde_json::from_str(&s_sigs)
			.expect("Convert ClamSigs fails");
		if b_perf {flog_perf(LOG1, &format!("Reading signatures"), &mut timer,
			&mut vlog);}
		v_sigs
	};

	//2. collect acdfa for critical patterns
	let (map_crit_pat, map_crit_pat_igc) = if !b_read_cache{
		let mut map_crit_pat = HashMap::<String,Vec<String>>::new();
		let mut map_crit_pat_igc = HashMap::<String,Vec<String>>::new();
		for sig in &v_sigs{ 
			sig.add_critical_pattern(&mut map_crit_pat,&mut map_crit_pat_igc); 
		}
		let s_map_crit_pat = serde_json::to_string(&map_crit_pat).unwrap();
		let s_map_crit_pat_igc = serde_json::to_string(&map_crit_pat_igc).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_map_crit_pat.txt", 
			fname_prefix, sigtype), &s_map_crit_pat);
		write_to_file(&format!("data/cache/{}_{:?}_map_crit_pat_igc.txt", 
			fname_prefix, sigtype), &s_map_crit_pat_igc);
		if b_perf {flog_perf(LOG1, 
			&format!("Extract Critial Patterns."), 
			&mut timer, &mut vlog);}

		(map_crit_pat, map_crit_pat_igc)
	}else{
		let s_map_crit_pat = read(&format!("data/cache/{}_{:?}_map_crit_pat.txt", fname_prefix, sigtype));
		let map_crit_pat:HashMap<String,Vec<String>> 
			= serde_json::from_str(&s_map_crit_pat)
			.expect("Convert crit_pat fails");
		let s_map_crit_pat_igc = read(&format!("data/cache/{}_{:?}_map_crit_pat_igc.txt", fname_prefix, sigtype));
		let map_crit_pat_igc:HashMap<String,Vec<String>> 
			= serde_json::from_str(&s_map_crit_pat_igc)
			.expect("Convert crit_pat fails");
		if b_perf {flog_perf(LOG1, 
			&format!("Read Critial Patterns."), 
			&mut timer, &mut vlog);}
		(map_crit_pat, map_crit_pat_igc)
	};
	if b_debug{
		//check if each signature is contained in map_crit_pat
		//or map_crit_pat_igc
		let set_sigs_gc = map_crit_pat.values().cloned()
			.collect::<Vec<Vec<String>>>().
			iter().flat_map(|s| s.clone()).
			collect::<HashSet<String>>();
		let set_sigs_igc = map_crit_pat_igc.values().cloned()
			.collect::<Vec<Vec<String>>>().
			iter().flat_map(|s| s.clone()).
			collect::<HashSet<String>>();
		let set_sigs = set_sigs_gc.union(&set_sigs_igc).cloned().
			collect::<HashSet<String>>();
		let set_sigs2 = v_sigs.iter().map(|v| v.name.clone())
			.collect::<HashSet<String>>();
		let set_diff = set_sigs2.difference(&set_sigs).cloned()
			.collect::<HashSet<String>>();
		if set_diff.len()>0{
			println!("ERROR: set_diff of computed: {:?}", set_diff);
			assert!(set_sigs==set_sigs2, "set_sigs.len(): {} != set_sigs2: {}",
				set_sigs.len(), set_sigs2.len() );
		}
	}

	let (dfa_crit, dfa_crit_igc) = if !b_read_cache{	
		let vec_crit_pat = map_crit_pat.keys().cloned()
			.collect::<Vec<String>>();
		let dfa_crit = HexACDFA::new(0, &vec_crit_pat);
		let s_dfa_crit = serde_json::to_string(&dfa_crit).unwrap();

		let vec_crit_pat_igc = map_crit_pat_igc.keys().cloned()
			.collect::<Vec<String>>();
		let dfa_crit_igc = HexACDFA::new_adv(0, &vec_crit_pat_igc, false);
		let s_dfa_crit_igc = serde_json::to_string(&dfa_crit_igc).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_dfa_crit.txt",
			fname_prefix, sigtype), &s_dfa_crit);
		write_to_file(&format!("data/cache/{}_{:?}_dfa_crit_igc.txt", 
			fname_prefix, sigtype), &s_dfa_crit_igc);
		if b_perf {flog_perf(LOG1, 
			&format!("Build ACDFA of Critial Patterns."), 
			&mut timer, &mut vlog);}

		(dfa_crit, dfa_crit_igc)
	}else{
		let s_dfa_crit = read(&format!("data/cache/{}_{:?}_dfa_crit.txt",fname_prefix, sigtype));
		let s_dfa_crit_igc = read(&format!("data/cache/{}_{:?}_dfa_crit_igc.txt", fname_prefix, sigtype));
		let dfa_crit: HexACDFA = serde_json::from_str(&s_dfa_crit)
			.expect("Convert ACDFA_CritPattern fails");
		let dfa_crit_igc: HexACDFA = serde_json::from_str(&s_dfa_crit_igc)
			.expect("Convert ACDFA_CritPattern fails");
		if b_perf {flog_perf(LOG1, 
			&format!("Read ACDFA of Critial Patterns."), 
			&mut timer, &mut vlog);}

		(dfa_crit, dfa_crit_igc)
	};
	flog(LOG1, &format!("#critical patterns: {} (CS) {} (IGC), #sigs: {}, ACDFA for Critical Pattenrs State: {} (CS) {} (IGC)", map_crit_pat.len(), map_crit_pat_igc.len(), v_sigs.len(), dfa_crit.num_states, dfa_crit_igc.num_states), &mut vlog);

	//3. generate all bag of words 
	let (pats, pats_igc) = if !b_read_cache{
		let pats = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let s_pats= serde_json::to_string(&pats).unwrap();

		let pats_igc = (&v_sigs).into_iter().map(|s| 
			s.collect_all_bagwords(true)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		let s_pats_igc= serde_json::to_string(&pats_igc).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_pats.txt", 
			fname_prefix, sigtype), &s_pats);
		write_to_file(&format!("data/cache/{}_{:?}_pats_igc.txt", 
			fname_prefix, sigtype), &s_pats_igc);
		if b_perf {flog_perf(LOG1, 
			&format!("Build Bag-of-Words."), 
			&mut timer, &mut vlog);}

		(pats, pats_igc)
	}else{
		let s_pats= read(&format!("data/cache/{}_{:?}_pats.txt", fname_prefix, sigtype));
		let s_pats_igc= read(&format!("data/cache/{}_{:?}_pats_igc.txt", fname_prefix, sigtype));
		let pats:Vec<String> = serde_json::from_str(&s_pats).unwrap();
		let pats_igc:Vec<String> = serde_json::from_str(&s_pats_igc).unwrap();
		if b_perf {flog_perf(LOG1, 
			&format!("Read Bag of Words."), 
			&mut timer, &mut vlog);}

		(pats, pats_igc)
	};
	flog(LOG1, &format!("Signatures:{}, Fixed Patterns: {}",
		v_sigs.len(), pats.len()), &mut vlog);

	//3. collect all patterns and build dfa for match stats
	let (dfa_patterns, dfa_patterns_igc) = if !b_read_cache{	
		let dfa = HexACDFA::new(0, &pats);
		let s_dfa = serde_json::to_string(&dfa).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_dfa.txt", 
			fname_prefix, sigtype), &s_dfa);

		let dfa_igc = HexACDFA::new_adv(0, &pats_igc, true);
		let s_dfa_igc = serde_json::to_string(&dfa_igc).unwrap();
		write_to_file(&format!("data/cache/{}_{:?}_dfa_igc.txt", 
			fname_prefix, sigtype), &s_dfa_igc);
		if b_perf {flog_perf(LOG1, 
			&format!("Build ACDFA of Bag Of Words."), 
			&mut timer, &mut vlog);}

		(dfa, dfa_igc)
	}else{
		let s_dfa = read(&format!("data/cache/{}_{:?}_dfa.txt", fname_prefix, 
			sigtype));
		let dfa: HexACDFA = serde_json::from_str(&s_dfa)
			.expect("Convert ACDFA_BagWords fails");
		let s_dfa_igc = read(&format!("data/cache/{}_{:?}_dfa_igc.txt", fname_prefix, sigtype));
		let dfa_igc: HexACDFA = serde_json::from_str(&s_dfa_igc)
			.expect("Convert ACDFA_BagWords fails");
		if b_perf {flog_perf(LOG1, 
			&format!("Read ACDFA of BagWords."), 
			&mut timer, &mut vlog);}

		(dfa, dfa_igc)
	};
	flog(LOG1, &format!("ACDFA for BagWords: states (cs): {}, states (igc): {}", dfa_patterns.num_states, dfa_patterns_igc.num_states), &mut vlog);
	write_lines(logfile, &vlog, false);

	(v_sigs, map_crit_pat, map_crit_pat_igc, dfa_crit, dfa_patterns, dfa_crit_igc, dfa_patterns_igc)

}


/// report all three approaches stats
pub fn gen_report_all_discharge_approach_stats(job_id: usize, sig_file: &str, 
	sigtype: ClamSigType, exec_list_file: &str, logfile: &str,
	b_read_cache: bool, cache_prefix: &str, setsigs_needs_dfa: &HashSet<String>) 
-> Vec<FailDischargeRecord>{

	let (v_sigs, map_crit_pat, map_crit_pat_igc,
		dfa_crit, dfa_bag, dfa_crit_igc, dfa_bag_igc)
		= load_discharge_data(sig_file, sigtype, exec_list_file,
			logfile, b_read_cache, cache_prefix, setsigs_needs_dfa);

	let file_names = &read_lines(exec_list_file);
	let final_data = file_names.into_par_iter().map(|fpath|
	{
		let nibbles = read_nibbles(fpath);
		discharge_file_by_crit_bag_pm(fpath, &nibbles, &v_sigs,
			&map_crit_pat, &map_crit_pat_igc,
			&dfa_crit, &dfa_bag, &dfa_crit_igc, &dfa_bag_igc, true)
	}).collect::<Vec<FailDischargeRecord>>();// for each file

	final_data
}

/// print out the zero_access dfa_data when turning the repetition
/// numbers
pub fn report_zero_access_dfa_data(){
	let run_size = |size: usize| -> (String, bool, Vec<usize>){
		let src = "Win.Trojan.Zeroaccess-6932503-0;Engine:81-255,Target:1;0&1&2;4d535642564d{2}2e444c4c::i;56423521f01f{28}0a00{16}00f0300000ffffff08000000010000000000;61d5893c82478645bf6059f9d3408757";
		let src = src.replace("28", &format!("{}", size));
		let mut s = gen_clamav_sig(&src, ClamSigType::General);
		s.gen_approx_bagwords(MIN_BAG_WORD_LEN);
		s.gen_approx_pm_bounds(MIN_BAG_WORD_LEN);
		let res = s.measure_dfa_size(10);
        res
	};
	let mut vec_sizes = vec![];
	let n = 10;
	for i in 1..n{
		let res = run_size(i);
		let real_size = res.2[1];
		vec_sizes.push(real_size);
		println!("i: {}, res: {:?}", i, res);
	}
	println!("--- SUMMARY ---");
	for i in 1..n{
		println!("length: {} => {}", i, vec_sizes[i-1]);
	}
}


