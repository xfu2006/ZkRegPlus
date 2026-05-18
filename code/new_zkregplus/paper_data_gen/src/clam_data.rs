/// Generate paper data related for clamav signature related
/*
	Created: 07/26/2024. Ported from driver.rs in old zkregplus project
*/
extern crate rayon;

use rayon::prelude::*;
use std::collections::{HashSet, HashMap};
use ark_ff::PrimeField;
use utils::{
	data::{ceil_log2},
	logger::{flog,LOG1,LOG3},
	os::{proj_root,read_lines,write_lines},
};
use data_processor::{
	discharge_proof::{FailDischargeRecord},
	discharge_prover::{quick_discharge_file, discharge_file},
	clamav::{default_clamav_cfg},
	clam_db::{ClamavDB},
};

/// Display the stats related to signatures that goes to 
/// SED and ISED.
pub fn print_sed_stats<F:PrimeField>(
vdata: &Vec<FailDischargeRecord>, db: ClamavDB<F>, vlog: &mut Vec<String>){
	//1. collect the sigs that needs SED and ISED and DFA separately
	let mut set_sed = HashSet::<String>::new();
	let mut set_ised = HashSet::<String>::new();
	let mut set_dfa = HashSet::<String>::new();
	for rec in vdata{
		//1. collect the set to be discharged by sed, ised, dfa
		assert!(rec.bag.is_subset(&rec.crit));
		assert!(rec.pm.is_subset(&rec.bag));
		assert!(rec.ind_pm_reg.is_subset(&rec.pm));
		let s_sed:HashSet<String>=rec.bag.difference(&rec.pm)
			.cloned().collect();
		let s_ised:HashSet<String>=rec.pm.difference(&rec.ind_pm_reg)
			.cloned().collect();
		let s_dfa = rec.ind_pm_reg.clone();
		set_sed.extend(s_sed);
		set_ised.extend(s_ised);
		set_dfa.extend(s_dfa);
	}

	//2. analyze set_sed and set_ised
	let mut f_analyze = |set: &HashSet::<String>, set_name|{
		let mut total_subsigs = 0usize;
		let mut total_steps= 0usize;
		for sname in set{
			let id = db.sig_to_id.get(sname)
				.expect(&format!("cannot find sig: {}", sname));
			let sig = &db.vec_sigs[*id-1];
			assert!(sig.name==*sname);
			total_subsigs += sig.vec_subsig_obj.len();
			for (_id,subsig_pm) in sig.vec_subsig_pm_bounds.iter().enumerate(){
				total_steps += subsig_pm.len();
			}
		}
		flog(0, LOG1, &format!("=== {} Stats =====", set_name), vlog);
		if set.len()==0{
			flog(0, LOG1, &format!("   sigs: {}, subsigs: {}, total_steps: {}, avg_steps: {}", set.len(), total_subsigs, total_steps, total_steps/set.len()), vlog);
		}else{
			flog(0, LOG1, &format!("   sigs: {}, subsigs: {}, total_steps: {}, avg_steps: {}", set.len(), total_subsigs, total_steps, "N/A"), vlog);
		}
	};

	f_analyze(&set_sed, "SED");
	f_analyze(&set_ised, "ISED");
	println!("-- set_sed: {}, set_ised: {}", set_sed.len(), set_ised.len());
}

/// display file size nicely
fn format_size(bytes: usize) -> String {
    const UNITS: [&str; 5] = ["B", "KB", "MB", "GB", "TB"];
    let mut size = bytes as f64;
    let mut unit = 0;

    while size >= 1000.0 && unit < UNITS.len() - 1 {
        size /= 1000.0;
        unit += 1;
    }

    if unit == 0 {
        format!("{}{}", bytes, UNITS[unit])
    } else {
        format!("{:.0}{}", size, UNITS[unit])
    }
}

/// Display the discharge stats and write the results into vlog
pub fn print_discharge_stats(vdata: &Vec<FailDischargeRecord>,
	vlog: &mut Vec<String>){
	//1. first sort out all by len
	let mut vec_stats: Vec<Vec<FailDischargeRecord>> = vec![vec![]; 32];
	for rec in vdata{ vec_stats[rec.flen].push(rec.clone()); }
	let b_more_details = false;
	let b_include_bs = false;
	let b_show_high_acc = true; //show most_freq patterns
	let b_show_high_pat = true; //show most freq pattersns by pat_ratio

	//2. print details
	if b_more_details{
		flog(0, LOG3, &format!("==== STATS DETAILS ====="), vlog);
		for i in 0..vec_stats.len(){
			for rec in &vec_stats[i]{
				flog(0, LOG3, &format!("{}: \ncrit: {:?}, bag: {:?}, pm: {:?}, after_dfa: {:?}", rec.fname, rec.crit, rec.bag, rec.pm, rec.all_dfa), vlog);
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
	let avg_f64 = |v: &Vec<f64>|->f64 {
		let sum:f64 = v.iter().sum();
		sum/(v.len() as f64)
	};
	let max_f64= |v: &Vec<f64>|->f64 {
		let imax:f64 = v.iter().copied().reduce(f64::max).unwrap();
		imax
	};
	let min_f64= |v: &Vec<f64>|->f64 {
		let imin:f64 = v.iter().copied().reduce(f64::min).unwrap();
		imin
	};
	flog(0, LOG1, &format!("==== WARNING: UNABLE TO DISCHARGE by crit_gab_pm which needs DFA discharge ====="), vlog);
	let mut all_cbp = HashSet::<String>::new();
	for rec in vdata{
		let crit_bag:HashSet<String> = rec.crit.clone().intersection(
			&rec.bag).cloned().collect();
		let crit_bag_pm:HashSet<String> = crit_bag.clone().intersection(
			&rec.pm).cloned().collect();
		if crit_bag_pm.len()>0{
			flog(0, LOG1, &format!("fname: {}, sigs: {:?}", rec.fname, &crit_bag_pm), vlog);
			for x in crit_bag_pm {all_cbp.insert( x.clone() );}
		}
	}
	flog(0, LOG1, &format!("==== Needs to build DFA for the following ===========\n{:?}=========================\n", all_cbp), vlog);
	flog(0, LOG1, &format!("==== WARNING: DFA could also not discharge the following ====="), vlog);
	for rec in vdata{
		if rec.all_dfa.len()>0{
			flog(0, LOG1, &format!("fname: {}, sigs: {:?}", rec.fname, &rec.all_dfa), vlog);
		}
	}
	flog(0, LOG1, &format!("==== WARNING: ISED could not discharge the following ====="), vlog);
	for rec in vdata{
		if rec.ind_pm_reg.len()>0{
			flog(0, LOG1, &format!("fname: {}, filesize: {}, sigs: {:?}", rec.fname, ceil_log2(rec.flen), &rec.ind_pm_reg), vlog);
		}
	}

	flog(0, LOG1, &format!("==== STATS SUMMARY (avg, max, count_non_zero) ========="), vlog);
	flog(0, LOG1, &format!("Note: set b_optimize_pm to false in \ngen_report_all_discharge_approach_stats\n for accurate PM-REG data, otherwise it's filtered by prevoius step \n"), vlog);
	flog(0, LOG1, &format!("-b_include_bs: {}------------------------------------------------------", b_include_bs), vlog);
	if b_include_bs{
		flog(0, LOG1, &format!("log(f)\tfiles\tcrit\tbag\tpm\tc_bag\tc_pm\tc_b_p\tdfa\tind_pm"), vlog);
	}else{
		flog(0, LOG1, &format!("log(f)\tfiles\tcrit\tpm\tc_pm\tdfa\tind_pm"), vlog);
	}
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
		if b_include_bs{
			flog(0, LOG1, &format!("{} \t {} \t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{}\t({},{},{}))", 
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
				vlog);
		}else{
			flog(0, LOG1, &format!("{} \t {} \t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})\t({},{},{})))", 
				i, 
				vec_stats[i].len(),
				avg(&vec_crit),  max(&vec_crit), ct(&vec_crit), 
				avg(&vec_pm), max(&vec_pm), ct(&vec_pm), 
				avg(&vec_crit_pm), max(&vec_crit_pm), ct(&vec_crit_pm),
				avg(&vec_dfa) , max(&vec_dfa), ct(&vec_dfa) , 
				avg(&vec_ind_pm) , max(&vec_ind_pm), ct(&vec_ind_pm) ), 
				vlog);
		}
	}

/* rework later.
	flog(LOG1, &format!("====  Simpler Summary (avg, max, count_non_zero) ====="), vlog);
	if b_include_bs{
		flog(LOG1, &format!("log(f)\tfiles\tcrit\tc_bag\tc_b_p\tdfa\tind_pm"), vlog);
	}else{
		flog(LOG1, &format!("log(f)\tfiles\tcrit\ttc_p\tdfa\tind_pm"), vlog);
	}
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
			vlog);
	}
*/

	flog(0, LOG1, &format!("====  Accepthance Path Stats ======="), vlog);
	let accpath_len:usize=vdata.iter().map(|v| v.total_acc_path_len).sum();
	let hs_len:usize=vdata.iter().map(|v| v.total_hs_size).sum();
	let acc_states:usize=vdata.iter().map(|v| v.total_accepted).sum();
	let acc_ratio = vdata.iter().map(|v| (v.total_accepted as f64)/(v.total_acc_path_len as f64)*100.0).collect::<Vec<f64>>();
	flog(0, LOG1, &format!("hs_len (number of accepted patterns but only counting position once)/acc_path: {}%, hs_len: {}, accpath_len: {}", (hs_len as f64)*100.0/(accpath_len as f64), hs_len, accpath_len), vlog);
	flog(0, LOG1, &format!("accepted states (counting multiple pos for one state, and ALL sigs)/acc_path: {}%, accepted_states: {}, accpath_len: {}", (acc_states as f64)*100.0/(accpath_len as f64), acc_states, accpath_len), vlog);
	flog(0, LOG1, &format!("acc_states/path_len: avg: {}%, max: {}%",
		avg_f64(&acc_ratio),
		max_f64(&acc_ratio)), vlog);

	let vec_unique_state_ratio = vdata.iter().map(|v|
	    //because it includes two automata's data (case sentive and igc)
	    (v.total_unique_states as f64)*100.0/(2.0*accpath_len as f64)
	).collect::<Vec<f64>>();	flog(0, LOG1, &format!("unique states ratio: avg: {}%, max: {}%, min: {}%",
		avg_f64(&vec_unique_state_ratio),	
		max_f64(&vec_unique_state_ratio),	
		min_f64(&vec_unique_state_ratio)
	), vlog);	
	let pm_proj_ratios = vdata.iter().map(|v|
		if v.total_accepted>0 {
		(v.total_pm_witness_len as f64)/(v.flen as f64)} else {0.0f64})
		.collect::<Vec<f64>>();
	let r_max: f64 = pm_proj_ratios.clone().into_iter().max_by(|a,b| a.total_cmp(b)).unwrap();
	let r_sum: f64 = pm_proj_ratios.iter().sum::<f64>();
	let r_avg = r_sum/(pm_proj_ratios.len() as f64);
	flog(0, LOG1, &format!("*** pm_reg pm_witness/total_accepted: (avg: max) -> appearahce of each acpeted states: ({:.2}%,{:.2}%). ", r_avg*100.0, r_max*100.0), vlog);
	let pm_witness_ratio = vdata.iter().map(|v|
		(v.total_pm_witness_len as f64)/(v.total_acc_path_len as f64)).collect::<Vec<f64>>();
	let w_max: f64 = pm_witness_ratio.clone().into_iter().max_by(|a,b| a.total_cmp(b)).unwrap();
	let w_avg: f64 = pm_witness_ratio.iter().sum::<f64>()/(pm_proj_ratios.len() as f64);
	flog(0, LOG1, &format!("pm_reg (sde) total witness_len/file_size: (avg: max): ({}%,{}%). This indicates total cost of discharging one file against ALL bag left sigs", w_avg*100.0, w_max*100.0), vlog);

	let fail_count = vdata.iter().filter(|rec| rec.is_fail()).count();

	// ---- Details --------------
	if b_show_high_acc{
		for i in 0..vdata.len(){
			if acc_ratio[i]>=5.0{
				println!("HIGH acc_states cost files: i: {}, acc_ratio: {}%, flen: {}, fname: {}, patterns: {:#?}", i, 
					acc_ratio[i], vdata[i].total_acc_path_len,
					vdata[i].fname, vdata[i].most_freq_sed_cs_pats);
			}
		}
	}
	let mut total_pat_rate = 0.0;
	let mut max_pat_rate = 0.0;
	for v in vdata{
		if v.max_seg_pat_rate>max_pat_rate{max_pat_rate=v.max_seg_pat_rate;}
		total_pat_rate += v.max_seg_pat_rate;
	}
	flog(0, LOG1, &format!("pat ratio: avg: {}%, max: {}%",
		total_pat_rate/(vdata.len() as f32)*100.0,
		max_pat_rate*100.0), vlog);


	if b_show_high_pat {
	    let bar: f32 = 0.05; // 5% threshold
		let bar_pat: f32 = 0.00000000; //0.5% percent

	    println!("=== High Segment Pattern and Acc States Files ===");
	    let mut high_pat_files: Vec<&FailDischargeRecord> = vdata
	        .iter()
	        .filter(|rec| rec.max_seg_pat_rate >= bar)
	        .collect();

	    high_pat_files.sort_by(|a, b| b.max_seg_pat_rate.partial_cmp(&a.max_seg_pat_rate).unwrap_or(std::cmp::Ordering::Equal));

	    for rec in high_pat_files {
	        println!("File: {}, Size: {}, Max Acc Rate: {:.2}%, Max Pat Rate: {:.2}%",
	            rec.fname,
				format_size(rec.total_acc_path_len/2), //nibble to bytes: /2
	            rec.max_seg_acc_rate * 100.0,
	            rec.max_seg_pat_rate * 100.0
	        );
	    }

	    println!("=== Patterns That Cause High Acc Ratios ===");
	    let mut aggregated_patterns: HashMap<String, (f32, f32)> = HashMap::new(); // (pattern, (max_acc_rate, max_pat_rate))

	    for rec in vdata.iter().filter(|rec| rec.max_seg_pat_rate >= bar_pat) {
			if rec.most_freq_seg_cs_pats.is_none() {continue;}
			let cs_pats = rec.most_freq_seg_cs_pats.clone().unwrap().clone();
	        for (pattern, acc_rate, pat_rate) in &cs_pats{
	            aggregated_patterns
	                .entry(pattern.clone())
	                .and_modify(|(current_acc, current_pat)| {
	                    *current_acc = current_acc.max(*acc_rate);
	                    *current_pat = current_pat.max(*pat_rate);
	                })
	                .or_insert((*acc_rate, *pat_rate));
	        }
	    }

	    let mut sorted_patterns: Vec<(String, f32, f32)> = aggregated_patterns
	        .into_iter()
	        .map(|(pat, (acc_r, pat_r))| (pat, acc_r, pat_r))
	        .collect();

	    sorted_patterns.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap_or(std::cmp::Ordering::Equal));

	    for (pattern, acc_rate, pat_rate) in sorted_patterns {
	        println!("\tRegex::new(r\"^{}+$\").unwrap(), //max acc_rate: {:.0}%, pat_rate: {:.0}%",
	                 pattern, acc_rate * 100.0, pat_rate * 100.0);
	    }
	}
	
	println!(" === failed files: {} =====", fail_count); 
	for rec in vdata{
		if rec.is_fail(){
			println!(" -- file {} fails: {:#?}", rec.fname, 
				rec.all_dfa);
		}
	}
	println!("==== failed files dump complete ==="); 

}




/// report all report approaches stats (all file path should be relative
/// path to project root!). sig_file: the list of signatures, needs_dfa_file:
/// those singatures that need DFA built, exec_list_file: the list of files
/// to discharge, report_file: the file path to write the report,
/// b_read_cache: if to reach cache, cache_dir: name of the cache dir;
/// if b_quick mode use quick_discharge function.
pub fn report_all_discharge_approach_stats<F:PrimeField>(sig_file: &str, needs_dfa_file: &str, needs_ised_file: &str, needs_ised_igc_file: &str,
	discharge_list_file: &str, report_file: &str,
	b_read_cache: bool, cache_dir: &str, b_quick: bool){
	//1. generate the clamav db
	println!("REPORT all discharge approach ...");
	println!("Step 1. generating clam db ...");
	let mut vlog = vec![];
	let cfg = default_clamav_cfg();
	let proot = proj_root();
	let b_write_cache = true;
	let db = ClamavDB::<F>::build_or_load(&cfg, sig_file, needs_dfa_file, needs_ised_file, needs_ised_igc_file, &mut vlog, cache_dir, b_read_cache, b_write_cache).expect("build db err");
	db.print_summary(&mut vlog);

	println!("Step 2. discharging all files ...");
	//2. generate the discharging files
	let file_names = &read_lines(&format!("{}/{}", proot, discharge_list_file));
	let final_data = file_names.into_par_iter().map(|fpath|
	{
		if b_quick{
			// paper_data_gen runs the discharge classifier
			// only — not the ZK circuit — so the F-level pad
			// doesn't affect reported stats. Pass 1 to mean
			// "no F-level pad"; sub-F pad is still applied.
			quick_discharge_file(fpath, &db, &cfg, 1)
		} else {
			discharge_file(fpath, &db, &cfg)
		}
	}).collect::<Vec<FailDischargeRecord>>();// for each file

	//3. write the report
	println!("Step 3. print discharge stats ...");
	print_discharge_stats(&final_data, &mut vlog);

	//4. print specifically the SED and ISED stats
	print_sed_stats::<F>(&final_data, db, &mut vlog);
	write_lines(report_file, &vlog, true);
}
