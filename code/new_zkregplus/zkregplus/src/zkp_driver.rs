/* ZkregPlus Main Driver
	Created: 01/31/2025
*/

//use std::collections::{HashSet};
use utils::{logger::{log,LOG1,log_perf}, timer::Timer as GTimer, consts::read_global_config};
use ark_ff::{Field,PrimeField,ToConstraintField};
use ark_ec::{Group, CurveGroup,
	pairing::{Pairing},
	short_weierstrass::SWCurveConfig
};
use ark_r1cs_std::{
	prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	ToConstraintFieldGadget,
};
use ark_snark::SNARK;
use ark_crypto_primitives::sponge::{
	poseidon::PoseidonConfig,
	Absorb,
};
use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{
	os::{proj_root, read_lines,read_nibbles,
//		read,write_to_file
	},
	data::{pack_nibbles}
};
use data_processor::{
	clamav::{default_clamav_cfg, quick_discharge_file_by_crit_bag_pm},
	clam_db::{ClamavDB},
	type_def::ClamavApproxConfig,
};
use folding_schemes::{
	transcript::poseidon::poseidon_canonical_config,
	commitment::{
		kzg::{Proof as KZGProof },
		pedersen::Params as PedersenParams,
		CommitmentScheme,
	},
	folding::{
		circuits::{CF1, CF2, CF3},
		foldpot::{
			sigma_ir1cs::{LookupTableTwoCol_Inst,SigmaIR1CS_Inst,WordInfo,SigmaIR1CS,LookupTableTwoCol},
			from_field::{AffineFromField},
			driver::{foldpot_main, FoldPotJob},
		}
	}
};
use std::sync::{Arc, Mutex};
use crate::circs::{
	composable_gadget_mapper::{CompositeGadgetMapper},
	cp_mapper::{CpComponentMapper,CpCapacity},
	sed_mapper::{SedComponentMapper,SedCapacity},
	dfa_mapper::{DfaComponentMapper,DfaCapacity},
};
use crate::gadgets::word_extract::LEGS;

use rayon::prelude::*;


// --------- type aliases for zkp_driver below -------------
type LK<F> = LookupTableTwoCol_Inst<F>;
type GM<F> = CompositeGadgetMapper<F,LK<F>>;
type FC<F,C,CS> = SigmaIR1CS_Inst<F,C,CS,LK<F>,GM<F>,false>;
// --------- type aliases for zkp_driver above -------------

/// load the files and pack them as nibbles
/// return (words in packed nibbles, word info, file names)
/// max_word_len is forwarded into the discharge_prover so it can
/// extend its nibble scan to match the circuit's padded view
/// (Step 4 of the pad-invariant rework).
fn load_files<F:PrimeField + ColEle>(_job_id: usize, list_file_path: &str, db: &ClamavDB<F>, cfg:&ClamavApproxConfig, _b_write_cache: bool, _cache_dir: &str, max_word_len: usize)
	->(Vec<Vec<F>>, Vec<WordInfo>, Vec<String>){
	//1. read the list of files
	let _b_debug = false;
	let proot = proj_root();
	let file_names = &read_lines(&format!("{}/{}", proot, list_file_path));
	if file_names.len() > 0 {
		println!("  First file: {}", file_names[0]);
	}

	//2. parallel for each file read its nibbles and convert
	let final_data = file_names.into_par_iter().map(|fpath|
	{
		let nibbles = read_nibbles(&format!("{}/{}", proot, fpath));
		let f_nibbles = nibbles.into_iter().map(|x| F::from(x as u32))
			.collect::<Vec<F>>();
		let packed = pack_nibbles(&f_nibbles);
		packed
	}).collect::<Vec<Vec<F>>>();

	//let sdir = format!("{}/data/cache/{}/", &proj_root(), cache_dir);
	/* DON'T - as each new bin-exec pack will cause loading outdated
	let vec_word_info= 
		cache
		if b_read_cache{
		let s_wi= read(&format!("{}/vec_word_info.txt", sdir));
		let vec_word_info:Vec<WordInfo> = serde_json::from_str(&s_wi)
				.expect("Convert vec_sigs fails");
		if b_debug{
			println!("DEBUG USE 2001: loaded vec_word_info: {:?}", 
				vec_word_info);
		}
		vec_word_info
	}else{
	*/
	let vec_word_info = file_names.into_par_iter().map(|fpath|
		{
			let abspath = format!("{}/{}", &proj_root(), fpath);
			let nibbles = read_nibbles(&abspath);
			let (fail_info, rec) = quick_discharge_file_by_crit_bag_pm(
				fpath,
				&nibbles,
				&db.vec_sigs,
				&db.vec_sigs_no_critical_pat,
				&db.map_crit_pat,
				&db.map_crit_pat_igc,
				&db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], //dfa_patterns,
				&db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
				true, cfg,
				&db.sig_to_id, max_word_len); //use optimize mode
			if !rec.is_success(){
				println!("FAILED discharging file: {} on sigs: {:?}",
					fail_info.fname,
					fail_info.all_dfa);
				println!(" -- word_info: {:?}", rec.vec_ised_sigs);
			}
			assert!(rec.is_success());
			assert!(!fail_info.is_fail());
			rec
		}).collect::<Vec<WordInfo>>();

		/*
		if b_write_cache{
			let s_wi = serde_json::to_string(&vec_word_info).unwrap();
			write_to_file(&format!("{}/vec_word_info.txt", &sdir), &s_wi);
			if b_debug{
				println!("DEBUG USE 2002: SAVED vec_word_info: {:?}", 
					vec_word_info);
			}
		}
		vec_word_info
	};
	*/

	(final_data, vec_word_info, file_names.clone())
}


/// build the circuits. Notice that we keep the legacy layered circuit
/// model (see driver.rs in foldpot module). However, we make the
/// simplication that 
/// *** EACH LAYER has ONE CIRC ***
///
/// Return: 2d layer of circs, but each layer has 1 circ. (2d is just
///  for legacy reason)
/// It's arranged from low cost to high cost so that the first
/// circ satisfying a certain capacity will be the best one.
/// vec_decrease_level allows 1, or 2, to be passed,
/// its length should be num_circs - 1 (we use these levels)
/// to call decrease_copy of capacity for the next circ
/// Eventually list of circs will be sorted in ascending order
#[allow(dead_code)]
fn build_circs_adv<F,C,CS>(
	poseidon_config: &PoseidonConfig<F>,
	total_word_n: usize, //sum of word length, each word is packed,
						//e.g., every 62 nibbles count as 1 in length (packed)
						//e.g., two words each 124 bytes means total_word_n
						// is 8 because each word has 248 nibbles, and
						// they are packed into 4 Fr each (containing 62 
						// nibbles)
	chunk_len: usize, //it's also counted in packed length (62 nibbles per
					  //1 char in word).
					  //e.g., given LEGS = 62 for bn254, it means 
					  //chunk length is 62 nibbles * 4-bits.
					  //e.g., chunk_len:1024 means 31kb actual chunk length.
					  //for 128kb chunk length it's chunk_len is 4130.
	lkup_len: usize,
	db: Arc<ClamavDB<F>>,
	init_cp_capacity_cs: &CpCapacity,
	init_sed_capacity_cs: &SedCapacity,
	init_dfa_capacity: &DfaCapacity, //no cs/igc distinction
	init_cp_capacity_igc: &CpCapacity,
	init_sed_capacity_igc: &SedCapacity,
	vec_decrease_level: &Vec<usize>, //decrease levels
	n_circs: usize,
	b_check_lkup: bool
)->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle + ColEle,
{
	//1. check the seed capacity consistency with the info
	assert!(init_cp_capacity_cs.max_word_len == chunk_len);
	assert!(init_cp_capacity_igc.max_word_len == chunk_len);
	assert!(init_sed_capacity_cs.wea_capacity().max_word_len == chunk_len);
	assert!(init_sed_capacity_igc.wea_capacity().max_word_len == chunk_len);
	assert!(init_dfa_capacity.wea_capacity().max_word_len == chunk_len);

	//2. given fixed chunk_len and total_word_len computes the
	//lkup_share needed to build up circuit
	//HERE: we use the global_config.perc_share_size to determine
	//the lkup size. if b_check_lkup is true, we make sure that it's large
	//enough (and later in circuit, it WILL perform the check in circ,
	//if malicious prover fake here, it will fail the circ eventually).
	let max_nibble_len = chunk_len * LEGS; //31 nibbles per 
	let total_nibbles = total_word_n * LEGS;
	let chunks = total_nibbles/max_nibble_len;
	let lk_share = read_global_config().perc_lkup_share* max_nibble_len/100;
	let lk_share = if lk_share == 0 {1} else {lk_share};
	println!("DEBUG USE 68911: lkup_len: {}, max_nibble_len: {}, total_nibble_len: {}, lk_share: {}, config.perc_lkup_share: {}, chunks: {}", lkup_len, max_nibble_len, total_nibbles, lk_share, read_global_config().perc_lkup_share, chunks);
	if b_check_lkup && lk_share*chunks < lkup_len{
		panic!("ERROR: lk_share: {} *chunks: {}  < lkup_len: {}",
			lk_share, chunks, lkup_len);

	}

	//3. build up each category
	let mut layer_circs = vec![];
	let mut cp_cap_cs= init_cp_capacity_cs.clone();
	let mut cp_cap_igc= init_cp_capacity_igc.clone();
	let mut sed_cap_cs = init_sed_capacity_cs.clone();
	let mut sed_cap_igc = init_sed_capacity_igc.clone();
	let mut dfa_cap= init_dfa_capacity.clone();


	//3.4 build the circs
	for i in 0..n_circs{
		//3.4.1 create cp (cs and igc)
		let cp_cs = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_cs.clone(), db.clone(), false);
		let cp_igc = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_igc.clone(), db.clone(), true);

		//3.4.2 create sed (it has both cs and igc built in)
		let sed = SedComponentMapper::<F,LK<F>>::new(
			sed_cap_cs.clone(), 
			sed_cap_igc.clone(), 
			db.clone());

		//3.4.3 dfa is optional depending if config supports 0 subsigs
		//which enforces dfa to be nil.
		let dfa = if dfa_cap.subsigs==0{ None }else{
			Some(
				DfaComponentMapper::<F,LK<F>>::new(dfa_cap.clone(), 
					db.clone())
			)
		};
		//3.4.4 construct the circuit
		let hybrid_cgm1 =if dfa_cap.subsigs==0{
			CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
				vec![
					Arc::new(Mutex::new(cp_cs)),
					Arc::new(Mutex::new(cp_igc)),
					Arc::new(Mutex::new(sed)),
				]
			)
		}else{//including the dfa
			CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
				vec![
					Arc::new(Mutex::new(cp_cs)),
					Arc::new(Mutex::new(cp_igc)),
					Arc::new(Mutex::new(sed)),
					Arc::new(Mutex::new(dfa.unwrap())),
				]
			)
		};
		let b_cyclepair = false;	
		let circ= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>> ,false> ::new_adv(
			format!("circ_cat_{}_circ_{}", i, 0), 
			poseidon_config.clone(), 
			Arc::new(Mutex::new(hybrid_cgm1)), 
			false, //b_full_mode (whether supporting cyclepair - no for 
					//regular circuit) 
			lk_share,
			b_cyclepair, b_check_lkup
		).expect("error building circ");
		layer_circs.push( vec![circ] ); //legacy to keep 2d layer

		//3.4.5 update the capacities.
		if i<vec_decrease_level.len(){
			let level = vec_decrease_level[i];
			cp_cap_cs = cp_cap_cs.decreased_copy(level); 
			sed_cap_cs = sed_cap_cs.decreased_copy(level); 
			cp_cap_igc = cp_cap_igc.decreased_copy(level); 
			sed_cap_igc = sed_cap_igc.decreased_copy(level); 
			dfa_cap= dfa_cap.decreased_copy(level); 
		}
	}//for category

	//return
	layer_circs.reverse();

	// DEBUG MESSAGE 1001: Print config of each circ before returning
	println!("DEBUG USE 1001 ========================= build_circs_adv generates =================");
	for (l1_idx, layer) in layer_circs.iter().enumerate() {
		for (l2_idx, circ) in layer.iter().enumerate() {
			println!("DEBUG MESSAGE 1001: Category {} Layer {} Circuit Name: {}\nCapacity: {:#?}", l1_idx, l2_idx, circ.get_name(), circ);
		}
	}
	layer_circs
}

/// build the list of circs. Note: for convenience of implementation,
/// we put the circ config hard coded in this function. To change
/// config, modify the local variables at the beginning of this function.
/// DEPRECATED
#[allow(dead_code)]
fn build_circs<F,C,CS>(poseidon_config: &PoseidonConfig<F>, total_word_n: usize, lkup_len: usize, db: Arc<ClamavDB<F>>, b_check_lkup: bool ) 
->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle + ColEle,
{

	// TEMP PLAN: remove later
	// each circ has one composite mapper which consists of one component 
	// mapper which has fixed length. Two circs, one handling length 8,
	// one handling length 4.

	//1. create cp_components
	if 1>0 {panic!("this function is depcrecated");}
	let avg_lk_wd = lkup_len/total_word_n + 1;
	let avg_lk_wd = if avg_lk_wd<1 {1} else {avg_lk_wd};
	let max_word = 1;
	let sigs = 3;
	let subsigs = 6;
	let avg_pats_per_subsig = 8;
	let avg_active_pats_per_subsig = 3;
	let basis_pats_in_trace = 6*100;
	let perc_comp_subsigs = 50;
	let basis_unique_states = 100; //1 percent
	let basis_acc_states = 500; //5 percent
	let perc_pats_expansion_rate = 100;
 
	//let avg_subsig_per_sig = 2;
	let cap1 = CpCapacity{
		max_word_len: max_word, 
		basis_unique_states,
		subsigs,
		avg_pats_per_subsig,
	};
	let comp1 = CpComponentMapper::<F,LK<F>>::new(cap1.clone(), 
		db.clone(), false);
	let comp1_igc = CpComponentMapper::<F,LK<F>>::new(cap1, db.clone(), true);
	/*
	let cap2 = CpCapacity{max_word_len: 2, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 2};
	let cap3 = CpCapacity{max_word_len: 3, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let cap4 = CpCapacity{max_word_len: 4, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let b_igc = false;
	let comp2 = CpComponentMapper::<F,LK<F>>::new(cap2, db.clone(), b_igc);
	let comp3 = CpComponentMapper::<F,LK<F>>::new(cap3, db.clone(), b_igc);
	let comp4 = CpComponentMapper::<F,LK<F>>::new(cap4, db.clone(), b_igc);
	let _cg4 = CompositeGadgetMapper::<F,LK<F>>::new("w4",vec![Arc::new(Mutex::new(comp4))]); 
	let _cg3 = CompositeGadgetMapper::<F,LK<F>>::new("w3",vec![Arc::new(Mutex::new(comp3))]); 
	let _cg2 = CompositeGadgetMapper::<F,LK<F>>::new("w2",vec![Arc::new(Mutex::new(comp2))]); 
	*/
	let cg1 = CompositeGadgetMapper::<F,LK<F>>::new("cp1",vec![
		Arc::new(Mutex::new(comp1.clone())), 
		Arc::new(Mutex::new(comp1_igc.clone())), 
	]); 
	//println!("DEBUG USE 1001: lkup_len: {}, avg_lk_wd: {}, comp1 share size: {}", lkup_len, avg_lk_wd, cg1.max_word_len()*avg_lk_wd);

	//2. create sed components
	let scap1= SedCapacity::new(max_word, db.dfa_crit.state_part_bits, subsigs, 
		avg_pats_per_subsig, avg_active_pats_per_subsig, basis_pats_in_trace, perc_pats_expansion_rate, sigs, perc_comp_subsigs, basis_unique_states, basis_acc_states);
	let scomp1 = SedComponentMapper::<F,LK<F>>::new(scap1.clone(), scap1, db.clone());
	//let scg1 = CompositeGadgetMapper::<F,LK<F>>::new("sed1",vec![Arc::new(Mutex::new(scomp1))]); 


	let lk_share1 = max_word*avg_lk_wd;
	let b_cyclepair = false;
	//let lk_share2 = max_word*2*avg_lk_wd;
	let _c1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c1"), poseidon_config.clone(), 
			Arc::new(Mutex::new(cg1)), false, lk_share1,
			b_cyclepair, b_check_lkup).expect("c1");
	/*
	let _c2 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c2"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg2)), false, lk_share2).expect("c2");
	let _c3 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c3"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg3)), false, lk_share2).expect("c3");
	let _c4 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c4"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg4)), false, lk_share2).expect("c4");
	*/

	//4. create sed instances
	//let sc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("sc1"), poseidon_config.clone(), 
	//		Arc::new(Mutex::new(scg1)), false, lk_share1).expect("sc1");

	//5. create dfa components and instances
	let sigs=3;
	let subsigs=6;
	let d_cap1 = DfaCapacity::new(max_word, sigs, subsigs);
	let dcomp1 = DfaComponentMapper::<F,LK<F>>::new(d_cap1, db.clone());
	//let dcg1 = CompositeGadgetMapper::<F,LK<F>>::new("d1",
	//	vec![Arc::new(Mutex::new(dcomp1))]);
	//let dc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("dfa1"), poseidon_config.clone(), 
	//		Arc::new(Mutex::new(dcg1)), false, lk_share1).expect("dc1");

	let hybrid_cgm1 = CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
		vec![
			Arc::new(Mutex::new(comp1)),
			Arc::new(Mutex::new(comp1_igc)),
			Arc::new(Mutex::new(scomp1)),
			Arc::new(Mutex::new(dcomp1)),
		]);
	let _hc1= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("hc1"), poseidon_config.clone(), 
			Arc::new(Mutex::new(hybrid_cgm1)), false, lk_share1,
			b_cyclepair, b_check_lkup).expect("hc1");

	//vec![ vec![c4,c3], vec![c2,c1] ]
	//vec![ vec![_c2,_c1] ] //for saving cost
	//vec![ vec![_c1] ] //for saving cost
	//vec![ vec![sc1] ] //for saving cost
	//vec![ vec![dc1] ] //for saving cost
	vec![ vec![_hc1] ] //compsite of cg, sed, and dfa
}


/// This is the main function of ZkregPlus framework.
/// Given a signature file, the list of data file to discharge,
/// It generates the entire workflow to discharge them first via
/// folding and then a decider proof.
///
/// * `sig_file`: the virus signature file (see examples/small_dataset for example).
/// * `list_files_to_scan`:  the file which contains the list of data files to be scanned using the virus signature
/// * `b_read_cahe`: if to read cache for pre-processed DFAs
/// * `cache_prefix`: the cache file prefix to determine which cache to read or write
/// * `list_of_dfa_sigs`: the file contains the list of signatures that to build into DFA
/// * `list_of_ised:`: the list of signatures that need ISED ACDFA to be constructed
/// * `job_id`: The ID of the job being processed.
pub fn zkp_driver<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S> 
(
	job_id: usize,
	sig_file: &str, 
	list_file_to_scan: &str, 
	_logfile: &str, 
	b_write_cache: bool, 
	cache_dir: &str, 
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize, //see the definition of params for build_circs for below
	init_cp_capacity: &CpCapacity, 
	init_sed_capacity: &SedCapacity,
	init_dfa_capacity: &DfaCapacity,
	vec_decrease_levels: &Vec<usize>,
	num_circs: usize,
	b_check_lkup: bool,
)
where
	GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
	GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	// CS1E is a KZG commitment, where challenge is C1::Fr elem
	CS1E: CommitmentScheme<
		C1,
		ProverChallenge = C1::ScalarField,
		Challenge = C1::ScalarField,
		Proof = KZGProof<C1>,
	>,
	<CS1E as CommitmentScheme<C1>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	// enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
	CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2>>::VerifierParams: Send + Sync,
	S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<C2 as CurveGroup>::BaseField: PrimeField,
	<C1 as Group>::ScalarField: Absorb,
	<C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
	for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
	for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	//C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	<C2 as CurveGroup>::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	<E as Pairing>::ScalarField: ColEle,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
	// re-use the capacity for BOTH cs and ignore_case
	// this is usaully inefficient for ignore_case (but
	// we do this for small samples for convenience)
	zkp_driver_adv::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(job_id, sig_file, vec![list_file_to_scan.to_string()], _logfile,
		b_write_cache, cache_dir,
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		chunk_len,
		init_cp_capacity, init_sed_capacity, init_dfa_capacity,
		init_cp_capacity, init_sed_capacity, 
		vec_decrease_levels, num_circs, b_check_lkup
	);
}
/// `job_id`: The ID of the job being processed.
pub fn zkp_driver_adv<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S> 
(
	job_id: usize,
	sig_file: &str, 
	list_files_to_scan: Vec<String>, 
	_logfile: &str, 
	b_write_cache: bool, 
	cache_dir: &str, 
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize, //see the definition of params for build_circs for below
	init_cp_capacity_cs: &CpCapacity, 
	init_sed_capacity_cs: &SedCapacity,
	init_dfa_capacity: &DfaCapacity, //only one DFA (no cs/igc distinction)
	init_cp_capacity_igc: &CpCapacity, 
	init_sed_capacity_igc: &SedCapacity,
	vec_decrease_level: &Vec<usize>,
	num_circs: usize, 
	b_check_lkup: bool,
)
where
	GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
	GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	// CS1E is a KZG commitment, where challenge is C1::Fr elem
	CS1E: CommitmentScheme<
		C1,
		ProverChallenge = C1::ScalarField,
		Challenge = C1::ScalarField,
		Proof = KZGProof<C1>,
	>,
	<CS1E as CommitmentScheme<C1>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	// enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
	CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2>>::VerifierParams: Send + Sync,
	S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<C2 as CurveGroup>::BaseField: PrimeField,
	<C1 as Group>::ScalarField: Absorb,
	<C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
	for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
	for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	//C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	<C2 as CurveGroup>::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	<E as Pairing>::ScalarField: ColEle,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
	//1. build or load the clamdb
	let log_level = LOG1;
	let mut gt1 = GTimer::new();
	log(0, log_level, &format!("=== ZKP driver starts ===="));
	let poseidon_config = poseidon_canonical_config::<CF1<C1>>();
	let mut vlog = vec![];
	let cfg = default_clamav_cfg();
	let db = ClamavDB::<CF1<C1>>::build_or_load(&cfg, sig_file, 
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		&mut vlog, cache_dir, read_global_config().b_read_cache, b_write_cache)
		.expect("build db err");
	if log_level>=LOG1+1{
		db.print_summary(&mut vlog);
	}
	log_perf(0, log_level, &format!("ZIP driver step 1: build DB."), &mut gt1);
	
	//2. load the files as vec of words
	let mut max_total_word_len = 0;
	let mut jobs = vec![];
	for list_file_to_scan in list_files_to_scan{
		let (vec_words, vec_word_info, vec_word_fnames) = load_files::<CF1<C1>>(job_id, &list_file_to_scan, &db, &cfg, b_write_cache, cache_dir, chunk_len);
		let total_word_len:usize = vec_words.iter().map(|w| w.len()).sum();
		if total_word_len > max_total_word_len{
			max_total_word_len = total_word_len;
		}
		jobs.push(FoldPotJob{
			vec_words,
			vec_word_info,
			vec_word_fnames,
			idx_individual_prf: 0,
		});
	}
	let lkup_len = db.lkup.get_size();
	log_perf(0, log_level, &format!("ZIP driver step 2: load words and prepare {} jobs.", jobs.len()), &mut gt1);

	//3. build the circuits
	let rc_db = Arc::new(db.clone());
	let vec_circs = build_circs_adv::<CF1<C1>,C1,CS1>(
		&poseidon_config, 
		max_total_word_len, 
		chunk_len,
		lkup_len, 
		rc_db,
		init_cp_capacity_cs,
		init_sed_capacity_cs,
		init_dfa_capacity,
		init_cp_capacity_igc,
		init_sed_capacity_igc,
		vec_decrease_level,
		num_circs,
		b_check_lkup
	);
	log_perf(0, log_level, &format!("ZIP driver step 2: build circs."), &mut gt1);

	//4. run the foldpot_main
	let lkup = Arc::new(db.lkup);
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
		lkup, vec_circs, &mut jobs, cache_dir).expect("main err");

}

/// Discharge a bundle of files against a ClamavDB and report the
/// per-approach (CP/SED/ISED/DFA) stats. Ported from the old
/// paper_data_gen main (gen_clamav_data). Standard file names are
/// assumed under config_dir (main.dat, main_dfa.dat, needs_ised.dat,
/// needs_ised_igc.dat, binexec.dat); the report is written under
/// report_dir as discharge_main_binexec.dat.
pub fn run_db_bundle<F:PrimeField>(config_dir: &str, report_dir: &str,
	b_cache: bool, b_quick: bool, range_bits: usize){
	utils::os::print_computer_config(Some("run_db_bundle"));
	utils::consts::get_global_config().range2_bit = range_bits;
	crate::stats_helper::report_all_discharge_approach_stats::<F>(
		&format!("{}/main.dat", config_dir), //src sig
		&format!("{}/main_dfa.dat", config_dir), //need_dfa
		&format!("{}/needs_ised.dat", config_dir), //need_ised
		&format!("{}/needs_ised_igc.dat", config_dir), //ised_igc
		&format!("{}/binexec.dat", config_dir), //files to discharge
		&format!("{}/discharge_main_binexec.dat", report_dir), //report
		b_cache, //read cache
		"main", //cache name
		b_quick);
}

#[cfg(test)]
pub mod tests_zkp_driver{
	use ark_ff::{PrimeField};
	use utils::consts::{read_global_config, get_global_config};
	//use folding_schemes::folding::foldpot::container_config::ColEle;
	use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
	use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
	use ark_groth16::Groth16;
	use folding_schemes::{commitment::{pedersen::Pedersen, kzg::KZG}};
	use crate::zkp_driver::{zkp_driver, zkp_driver_adv};
	use crate::circs::{
		cp_mapper::{CpCapacity},
		sed_mapper::{SedCapacity},
		dfa_mapper::{DfaCapacity},
	};

	type CS1 = Pedersen<Projective>;
	//EXTERNAL commitment KZG for decider
	type CS1E = KZG<'static, Bn254>;
	type CS2 = Pedersen<Projective2>;
	type C1 = Projective;
	type C2 = Projective2;
	type GC1 = GVar;
	type GC2 = GVar2;
	//type FC = SigmaIR1CS_Inst<Fr,Projective,KZG<'static,Bn254>,LK>;
	type S = Groth16<Bn254>;
	type C2G2 = ProjectiveG2;

	/// small data: each cat of signatures got one sample, one 2-Fr word
	/// read the READ me in data/small_data_set/README for the design of sigs
	/// COST: 7GB and 36 sec.
	#[allow(dead_code)]
	fn small_data<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 8;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1} 
			else {8320}; //needed for 96k lkup entries for 4 chunks
					//twice larger than what's really needed to
					//leave out room to test the empty entries
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; //for dfa 
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;  
		let avg_pats_per_subsig = 3;  
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 23*100; 
		let basis_acc_states = 646;  //6.46 percent
		let basis_pats_in_trace = 1291;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 171;

		let vec_decrease_level = vec![];
		let num_circs = 1; 

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}
	/// small dna: used for debugging the comparison set with reef on
	/// Chromosome 17 dna set. 
	/// COST: 7GB and 34 sec.
	#[allow(dead_code)]
	fn small_dna<F:PrimeField>(){
		utils::os::print_computer_config(Some("small_dna"));
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 8;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {8320}; //needed for 96k lkup entries for 4 chunks
					//twice larger than what's really needed to
					//leave out room to test the empty entries
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_dna/config"; //for dfa 
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;  
		let avg_pats_per_subsig = 3;  
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 33*100; //needs >=3226 for this dataset
		let basis_acc_states = 646;  //6.46 percent
		let basis_pats_in_trace = 1291;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 171;

		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0,
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_nda/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}


	/// small_debug (Plan D): single-job local reproducer for the
	/// compute_sig_adv.rs:1269 panic. Uses the CACHED full_clamav DFA
	/// (data/cache/full_data/, ~4.1GB) so the AC-DFA over-approximation
	/// is identical to the server's; scans ONE file (merged_217); sets
	/// b_folding_only=true so the heavy SNARK preprocess is skipped
	/// (bug fires during gen_nd_advice / pass_all anyway). Capacities
	/// mirror full_debug — already validated. Prerequisite: a prior
	/// full_clamav run must have populated data/cache/full_data/.
	#[allow(dead_code)]
	fn small_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_debug"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_folding_only = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = true;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1_cfg  = "data/debug/full_clamav/config/";
		// All 4 files — matches server's binexec_debug.dat exactly.
		let set1_scan = "data/debug/full_debug/config";
		let max_word = 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs = 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap = DfaCapacity::new(
			max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let scan_files: Vec<String> = vec![
			format!("{}/binexec_debug.dat", set1_scan),
		];

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,
			CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1_cfg),
			scan_files,
			"data/debug/full_debug/reports/report.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1_cfg),
			&format!("{}/needs_ised.dat", set1_cfg),
			&format!("{}/needs_ised_igc.dat", set1_cfg),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// small data: multiple parallel jobs.
	/// COST  4 jobs: 14 GB and 228 sec (reason: folding doesn't take much time)
	#[allow(dead_code)]
	fn small_data_par<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data_par"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {10000}; //enough lkup coverage for binexec_p* (4 files)
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; //for dfa
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;
		let avg_pats_per_subsig = 3;
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 25*100;
		let basis_acc_states = 807;  //6.46 percent
		let basis_pats_in_trace = 1500;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 200;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		let scan_files: Vec<String> = (1..=4).map(|i|
			format!("{}/binexec_p{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(0,
			&format!("{}/sigs.dat",set1), //src sig
			scan_files, //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap, //as igc
			&init_sed_cap, //as igc
			&vec![],
			1,
			b_check_lkup
		);
	}


	/// the sigs are the same as small data
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// COST: 18GB and 160 sec
	#[allow(dead_code)]
	fn small_data2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data2"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 2; 
		let subsigs = 4; 
		let avg_pats_per_subsig = 4; 
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_pats_in_trace = 6; 
		let perc_comp_subsigs = 26; 
		let basis_unique_states = 5; 
		let basis_acc_states = 2; 
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);

		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states: basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig: avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, 
			subsigs, 
			 avg_pats_per_subsig, 
			 avg_active_pats_per_subsig, 
			 basis_pats_in_trace-1, 
			 perc_pats_expansion_rate,

			 sigs, 
			 perc_comp_subsigs,
			 basis_unique_states,
			 basis_acc_states,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			vec![format!("{}/binexec.dat",set1)], //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec![],
			1,
			b_check_lkup
		);
	}

	/// This function is used for debugging
	#[allow(dead_code)]
	fn small_data_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data_debug"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 24;
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512*4; 
		let sigs = 2; 
		let subsigs = 4; 
		let avg_pats_per_subsig = 4; 
		let avg_active_pats_per_subsig = 0; //good value 0, actually does
			//not matter?
		let perc_comp_subsigs = 26; 
		let basis_unique_states = 5; 
		let basis_acc_states = 400; 
		let basis_pats_in_trace = 450; 
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs_debug2.dat",set1), //src sig
			&format!("{}/binexec_debug2.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec![],
			1,
			b_check_lkup
		);
	}


	/// the sigs are the same as small data2
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// has 2 second long word (eady and almost no match)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// Difference: 2 categories and 2 circs each (multiple circs) -> 4 circs
	/// for testing circ selection
	/// WARNING: you need 128GB RAM for small_data3 as it has 4 circs
	/// at the last stage of snark generation it's costly.
	#[allow(dead_code)]
	fn small_data3<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data3"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().min_subsigs = 3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 8;  //good value 2
		let subsigs = 8;  //good value 4
		let avg_pats_per_subsig = 3;  //good value 4
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_acc_states = 10;  //good value 2
		let basis_pats_in_trace = 22;  //good value 4
		let perc_comp_subsigs = 104;  //good value 34 
		let basis_unique_states = 20;  //good value 5 * 4 and similar for all others
		let dfa_sigs = 4;
		let dfa_subsigs= 2*dfa_sigs;
		let perc_pats_expansion_rate = 160;

		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let perc_pats_expansion_rate_igc = 136 ;
		let basis_pats_in_trace_igc = 20;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			vec![format!("{}/binexec2.dat",set1)], //list of files to discharge
			"data/small_data_set/reports/small_data3.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// This allows to try 4 circ on variety of small files
	/// setting min_idx and max_idx to try 1M, 2M, 4M files.
	#[allow(dead_code)]
	fn small_data4<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data4"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 4;  //good value 2
		let subsigs = 4;  //good value 4
		let avg_pats_per_subsig = 3;  //good value 4
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_acc_states = 5;  //good value 10 
		let basis_pats_in_trace = 11;  //good value 22 
		let perc_comp_subsigs = 40;  //good value 104 
		let basis_unique_states = 16;  //good value 20
		let dfa_sigs = 2;
		let dfa_subsigs= 2*dfa_sigs;
		let perc_pats_expansion_rate = 40; //good value 160

		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let perc_pats_expansion_rate_igc = 78; //good value 136
		let basis_pats_in_trace_igc = 30; //good value 20

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let files = vec![
			vec![format!("{}/sample_1M.dat",set1)], 
			vec![format!("{}/sample_2M.dat",set1)], 
			vec![format!("{}/sample_4M.dat",set1)], 
		];
		let idx = 1; //max 2
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs2.dat",set1), //src sig
			files[idx].clone(),
			"data/small_data_set/reports/small_data4.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// the sigs are the FULL SET of sigs
	/// However, just run a small file
	#[allow(dead_code)]
	fn full_data1<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data1"));
		get_global_config().snark_cache_dir = "full_data".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa 
		//let max_word= 512; 
		let max_word= 512 * 4; 
		let sigs = 320;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 500; //last known good vlaue: 1900
		let basis_acc_states = 1000; //9 cpercent
		let basis_pats_in_trace = 1200; //10 percent
		let perc_pats_expansion_rate = 200;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_1.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}
	/// the sigs are the FULL SET of sigs
	/// It runs a small but challenging file _codecs_hk.so (158kb)
	#[allow(dead_code)]
	fn full_data2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data2"));
		get_global_config().snark_cache_dir = "full_data".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		//let max_word= 512;
		let max_word= 512 * 4;
		let sigs = 320;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 1000; //ld vlaue 19 cpercent
	//	let basis_acc_states = 200; //old value 9 cpercent --> GOOD setting
	 //   let basis_pats_in_trace = 250 ; //1.2 * basis_acc_states
		let basis_acc_states = 1200; //old value 9 cpercent --> GOOD setting
		let basis_pats_in_trace = 1440 ; //1.2 * basis_acc_states
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_2.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// the sigs are the FULL SET of sigs
	/// It runs a large but difficult file: gdb (6.6M)
	/// COST: stmt_len: 12.7M => all_w_e = 42M => circ1 100M R1CS
	/// prove_step: 39 sec
	/// if using max_word 512 *8 (128kb) => it's 21M. prove_step: 60 sec
	/// IMPROVEC COST: after applying the tricks of separating
	///	igc and cs. stmt_len: 10M, all_w_e: 33M => circ1 72M R1CS
	#[allow(dead_code)]
	fn full_data3<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data3"));
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		let max_word= 512 * 4;
		let sigs = 350;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 1600; //15 cpercent
		let basis_acc_states = 1200; //9 cpercent
		let basis_pats_in_trace = 2200; //old value 100 cur value 1/1000.
		let dfa_sigs = 3;
		let dfa_subsigs= 4;
		let perc_pats_expansion_rate = 100;
		//let avg_subsig_per_sig = 3;

		let shrink=8;
		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
	   let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs/2,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace/shrink,
			perc_pats_expansion_rate,

			sigs/shrink,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states/shrink,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			vec![format!("{}/binexec_3.dat",set1)], //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// This runs the full signature set on the most difficult files
	/// each is 15-32MB file
	/// details:
	/// 1: -rw-rw-r-- 1 xiang xiang 33554416 Jun  8  2025 anthoscli__00
	/// 2: -rw-rw-r-- 1 xiang xiang 33554416 Jun  8  2025 anthoscli__01
	/// 3: -rwxrwxr-x 1 xiang xiang 22720144 Jun  8  2025 libpython3.9.so (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 4: -rwxrwxr-x 1 xiang xiang 22720144 Jun  8  2025 libpython3.9.so.1.0 (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 5: -rwxrwxr-x 1 xiang xiang 20785824 Jun  8  2025 libicudata.so.50.2 (Max Acc Rate: 5.32%, Max Pat Rate: 5.38%)
	/// 6: -rwxrwxr-x 1 xiang xiang 15603008 Jun  8  2025 cc1plus (Max Acc Rate: 12.33%, Max Pat Rate: 12.36%)
	/// 7: -rwxrwxr-x 1 xiang xiang 15022144 Jun  8  2025 data/samples/binexec_merged128k/f951 (Max Acc Rate: 12.42%, Max Pat Rate: 12.45%)
	/// 8: -rwxrwxr-x 1 xiang xiang 13676928 Jun  8  2025 data/samples/binexec_merged128k/lto1 (Max Acc Rate: 11.57%, Max Pat Rate: 11.63%)
	/// Total: 173MB. 
	#[allow(dead_code)]
	fn full_data4<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data4"));
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = true;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 361; // OLD value: 150
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().min_basis_unique_states= 600; //OLD value 20
		get_global_config().min_basis_acc_states =  113; // OLD value: 100
		get_global_config().min_basis_pats_in_trace=  134; // OLD value: 110
		get_global_config().min_dfa_subsigs =  3; //OLD val 2
		get_global_config().min_avg_pats_per_subsig= 8; // OLD value: 6
		get_global_config().min_dfa_sigs = 2; // OLD value: 0 (default)
		get_global_config().b_read_cache = true;
		get_global_config().perc_lkup_share = 143; //this is for
			//full_clam() setting (700MB linux data for 38k clamav) in 8 jobs
			//see full_clam

		let b_write_cache = !read_global_config().b_read_cache;
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 1300; //15 cpercent
		let vec_decrease_level = vec![2];
		let num_circs = 2; 
		let basis_acc_states = 750; // 1260; //last good value 1800
		let basis_pats_in_trace = 820; //1400; //last good value 3000
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = 6;
		let dfa_subsigs= 6;
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		//just ranges allowed 0 to 8test one at a time
		//APPROACH 1:
		let min = 0; //starting: 0
		let max = 1; //max possible: 8

		//APPROACH 2:
		//IF using min = 8, max=9 it uses binexec_4_9.dat (which
		//has ALL the files listed (about 87MB)
		//let min = 8;
		//let max = 9;
				//
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		//let num_jobs:usize = 1;
		//let num_jobs:usize = 16;
		let data_files = vec![format!("{}/sample_1M.dat",set1)];

		for _id in min..max{
			zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
	0, 
				&format!("{}/main.dat",set1), //src sig
				//vec![format!("{}/binexec_4_{}.dat",set1, id+1)], //list of files to discharge
								data_files.clone(),
				"data/debug/full_data_set/reports/report2.dat", //report
				b_write_cache,
				"full_data", //cache name
				&format!("{}/main_dfa.dat", set1), //signs that need dfa
				&format!("{}/needs_ised.dat", set1), //signs that need ised 
				&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
				max_word, //this is the chunk len
				&init_cp_cap,
				&init_sed_cap,
				&init_dfa_cap,
				&init_cp_cap_igc,
				&init_sed_cap_igc,
				&vec_decrease_level,
				num_circs,
				b_check_lkup
			);
		}
	}
	
	
	/// Used for explorting parallel execution efficiency.
	/// For b_small = true, can run with 16 GB
	/// For b_small = false,needs 128GB. 4 jobs fills 50% cpu.
	#[allow(dead_code)]
	fn full_par<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_par"));
		let b_small = true;
		get_global_config().b_read_cache = true;

		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 148;
		get_global_config().b_light_test = true;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().b_folding_only = true;
		let b_write_cache = !read_global_config().b_read_cache;


		let set1 = "data/debug/full_par_set/config/"; //for dfa
		let max_word= if b_small {512} else {512 * 4};
		let sigs = if b_small {20} else {400};
		let subsigs = if b_small {142} else {580}; 
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = if b_small {500} else {2000}; //15 cpercent
		let vec_decrease_level = if b_small {vec![]}
			else { vec![2,1] };
		let num_circs = if b_small {1} else {3}; 
		let basis_acc_states = if b_small {200} else {1260}; 
		let basis_pats_in_trace = if b_small {220} else {1400}; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = if b_small {1} else {6};
		let dfa_subsigs= if b_small {1} else {6};
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let num_jobs:usize = 1;
		//let num_jobs:usize = 16;

		let data_files = (0..num_jobs).map(|i|
			format!("{}/sample_1M_{}.dat",set1,i)
		).collect::<Vec<String>>();

		let suffix = if b_small { "_small" } else { "" };
		let [main_file, main_dfa_file, needs_ised_file,
			needs_ised_igc_file] =
			["main", "main_dfa", "needs_ised", "needs_ised_igc"]
			.map(|n| format!("{}/{}{}.dat", set1, n, suffix));

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&main_file,
			data_files,
			"data/debug/full_par_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&main_dfa_file, //signs that need dfa
			&needs_ised_file, //signs that need ised
			&needs_ised_igc_file, //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// Like `full_data4`, but feeds binexec_4_1..binexec_4_8 (8 files,
	/// excluding the merged binexec_4_9) into a single `zkp_driver_adv`
	/// call so foldpot runs them as parallel jobs. Capacities and the
	/// config dir are taken from `full_data4`; parallel/snark knobs
	/// come from `full_par`. Total 173MB. do not generate snark proof.
	/// This function is used to figure out the optimized circ setting
	/// for clamav data (with the most difficult files).
	#[allow(dead_code)]
	fn full_par2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_par2"));
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 148;
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().b_light_test = true;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().b_folding_only = true;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		let max_word= 512 * 8; //compared with full4, we are doing 128k seg 
		let sigs = 400;
		let subsigs = 562;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 1300; //OLD VLAUE: 2000
		let vec_decrease_level = vec![];
		let num_circs = 1;
		let basis_acc_states = 750; //OLD VALUE: 1260;
		let basis_pats_in_trace = 820; //OLD VALUE: 1400;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 6;
		let dfa_subsigs= 6;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs/2,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let data_files = (1..=8).map(|i|
			format!("{}/binexec_4_{}.dat", set1, i)
		).collect::<Vec<String>>();

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1),
			data_files,
			"data/debug/full_data_set/reports/report2.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}


	/// This tests the full clamav signatures against linux executables
	/// There are 756MB Linux binary executable
	/// We split them into 8 jobs.
	/// E.g., run on m3m machine with 2TB (xx cpu)
	/// Can finish in xxx hrs.
	#[allow(dead_code)]
	fn full_clamav<F:PrimeField>(b_check_lkup: bool, b_light_test: bool,
		b_setup: bool){
		utils::os::print_computer_config(Some("full_clamav"));
		//extra setting
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = b_setup;
		get_global_config().b_read_snark_cache = !b_setup;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = b_light_test;
		get_global_config().min_subsigs = 368; // OLD value: 361
		get_global_config().min_basis_unique_states= 1054; // OLD value: 600
		get_global_config().min_basis_acc_states =  268; // OLD value: 113
		get_global_config().min_basis_pats_in_trace=  295; // OLD value: 134
		get_global_config().min_avg_pats_per_subsig= 8; // OLD value: 6
		get_global_config().min_dfa_sigs = 3; // OLD value: 2
		get_global_config().min_dfa_subsigs =  3; //OLD val 2
		get_global_config().n_par_snark = if b_setup {1} else {2};
		get_global_config().n_par_snark_cp = if b_setup {1} else {2};
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143; //this is for
			//700MB data in 8 jobs and 256M lkup entries
			//so we have per job: 90MB data = 180M nibbles
			// then: 256/180 * 100 = 142.2% that's 142


		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_clamav/config/"; //for dfa
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2; 
		let basis_unique_states = 1300; //2000; //15 cpercent
		let basis_acc_states = 750; //1260; //last good value 1800
		let basis_pats_in_trace = 820; //last good value 3000
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = 8;
		let dfa_subsigs= 8;
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let num_jobs = if b_setup {1} else {8};
		let scan_files: Vec<String> = if b_setup {
			(0..num_jobs).map(|i|
				format!("{}/sample_1M_{}.dat", set1, i)).collect()
		} else {
			(0..num_jobs).map(|i|
				format!("{}/binexec_p{}.dat", set1, i)).collect()
		};
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1), //src sig
			scan_files, //list of files to discharge
			"data/debug/full_clamav/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
					//actually not used
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
					//actually not used
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// full_dna: ZK discharge of the full clean chr17 sample
	/// (NC_000017.11.reef.bin, 41.6MB) against the 27,501-sig DNA DB.
	/// Light-test, no prior snark setup. Single job (the file is
	/// offset-anchored, so it can't be split across jobs). Capacities
	/// inferred from test_db_bundle's discharge stats on the same
	/// sample; basis_unique_states and perc_pats_expansion_rate are
	/// starting values that the capacity self-check (CapErr back-solve
	/// in discharge_adv / fsm_adv) refines on the first run.
	#[allow(dead_code)]
	fn full_dna<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_dna"));
		get_global_config().snark_cache_dir = "dna_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 27; //80.09M-nibble max offset
		//min_* floors set LOW (DNA workload is tiny vs clamav)
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		//~200 needed when b_check_lkup (164M lkup / ~328 chunks);
		//1 when not checking (panic guard is gated on b_check_lkup).
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200};

		get_global_config().b_read_cache = true; //reuse cached DNA DB
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/paper_data/dna/config";
		let max_word = 512 * 8; //4096 -> ~328 folding steps
		let sigs = 20; //crit/SED peak = 17 (clean sample) + headroom
		let subsigs = 20; //1 subsig/sig
		let avg_pats_per_subsig = 1; //single literal pattern
		let avg_active_pats_per_subsig = 1;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 6500; //CapErr crept 1837->1906; +hdrm
		let basis_acc_states = 2; //max_seg acc rate ~0.39 bp
		let basis_pats_in_trace = 4; //max_seg_pat_rate ~0.39 bp +hdrm
		let perc_pats_expansion_rate = 200; //START; CapErr back-solves
		let dfa_sigs = 0; //0 reached DFA + margin
		let dfa_subsigs = 0;
		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);
		let init_dfa_cap = DfaCapacity::new(max_word, dfa_sigs,
			dfa_subsigs);

		//IGC: 0 ignore-case patterns, BUT compute_sig_adv merges cs+igc
		//and asserts subsigs_cs==subsigs_igc and inp_sigs==capacity.sigs
		//(compute_sig_adv.rs:368,1160), so IGC must mirror CS on
		//subsigs/sigs. Only perc_pats_expansion_rate_igc is shrunk (igc
		//trace is empty). Mirrors full_clamav's cs/igc symmetry.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, 4, //perc_pats_expansion_rate_igc small
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);

		let scan_files: Vec<String> = vec![
			format!("{}/binexec.dat", set1)]; //single job

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main.dat", set1), //src sig
			scan_files, //list of files to discharge
			"data/paper_data/dna/reports/report_zk.dat", //report
			b_write_cache,
			"dna_data", //cache name
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// 2026-05-21: full_clam_short_file — mirrors full_clamav with
	/// b_light_test=false and b_setup=false hardcoded, and scan
	/// targets swapped to 8x ~1MB sample_1M_*.dat files. Goal:
	/// measure SNARK time (Phase 1 main + Phase 2 cp) in isolation
	/// from folding cost. Snark keys are READ from cache; setup is
	/// skipped. All other config knobs (capacities, range2_bit,
	/// n_par_snark*, min_*) are byte-identical to full_clamav —
	/// keep them in sync if you tune full_clamav.
	#[allow(dead_code)]
	fn full_clam_short_file<F:PrimeField>(){
		utils::os::print_computer_config(Some("full_clam_short_file"));
		//extra setting
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = false;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states= 1054;
		get_global_config().min_basis_acc_states =  268;
		get_global_config().min_basis_pats_in_trace=  295;
		get_global_config().min_avg_pats_per_subsig= 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs =  3;
		get_global_config().n_par_snark = 1;
		get_global_config().n_par_snark_cp = 1;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_clamav/config/";
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs= 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let num_jobs = 8;
		let scan_files: Vec<String> = (0..num_jobs).map(|i|
			format!("{}/sample_1M_{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1),
			scan_files,
			"data/debug/full_clamav/reports/report2.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// 2026-05-16: full_debug — mirrors full_clamav (test-mod
	/// capacities) but with a SINGLE list file (n_jobs=1) of 4
	/// server-failing samples. Reuses data/cache/full_clamav snark
	/// keys + data/cache/full_data DB cache. Used by
	/// test_full_debug_main below, which full_debug_watch.py
	/// invokes via `cargo test`. All capacities here are
	/// byte-identical to the full_clamav() above — keep them in
	/// sync if you tune full_clamav.
	fn full_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_debug"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		// 2026-05-16: full_debug intentionally does NOT load or
		// generate Groth16 keys. The check_logup panic we're trying
		// to reproduce fires inside pass_all/gen_step_cs, which is
		// reached before the post-pass_all SNARK step. Combined
		// with b_folding_only=true (which returns Ok(()) right
		// after pass_all), the prover never touches g16_main.key /
		// g16_cp.key — so the user doesn't need to have run
		// full_clamav_setup. See driver.rs:2497 (key load) and
		// driver.rs:2845 (b_folding_only early return).
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_folding_only = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = true;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1_cfg  = "data/debug/full_clamav/config/";
		let set1_scan = "data/debug/full_debug/config/";
		let max_word = 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs = 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap = DfaCapacity::new(
			max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		// Single list file => n_jobs = 1, 4 words inside.
		let scan_files: Vec<String> = vec![
			format!("{}/binexec_debug.dat", set1_scan),
		];

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,
			CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1_cfg),
			scan_files,
			"data/debug/full_debug/reports/report.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1_cfg),
			&format!("{}/needs_ised.dat", set1_cfg),
			&format!("{}/needs_ised_igc.dat", set1_cfg),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// 2026-05-16: dedicated test entry for full_debug_watch.py.
	/// Invoked via `cargo test ... test_full_debug_main`.
	#[test]
	pub fn test_full_debug_main(){
		full_debug::<Fr>(false);
		utils::logger::flush_logger();
		let sentinel = format!(
			"{}/data/cache/run_complete.sentinel",
			utils::os::proj_root());
		let _ = std::fs::write(&sentinel, "ok\n");
	}

	/// 2026-05-18 (Plan D): test entry for the compute_sig_adv:1269
	/// repro via cached full_clamav DFA + single-file scan. Passes
	/// b_check_lkup=false (matching test_full_debug_main) so the
	/// pre-check_logup lk_share*chunks>=lkup_len guard doesn't fire
	/// — the panic we're chasing is host-side in gen_nd_advice,
	/// well before check_logup gets to run.
	#[test]
	pub fn test_small_debug_main(){
		let b_check_lkup = false;
		small_debug::<Fr>(b_check_lkup);
	}


	#[test]
	pub fn test_zkreg_main(){//test zkreg.main
		let b_check_lkup = true;
		let _b_light_test = false;
		let _b_setup = false;
		small_data::<Fr>(b_check_lkup); //small data
		//small_dna::<Fr>(); //small data dna set
		//full_dna::<Fr>(b_check_lkup);
		//small_debug::<Fr>(b_check_lkup); //small_data + max_word=2
		//small_data2::<Fr>(b_check_lkup);  //10k data
		//small_data3::<Fr>(b_check_lkup); //multi circ of 10k data -> fails
		//small_data_par::<Fr>(b_check_lkup); //small data (parallel jobs)
		//small_data_debug::<Fr>(b_check_lkup);  //for debug
		//small_data4::<Fr>(b_check_lkup); //multi circ of 1M, 2M, 4M data
		//full_data1::<Fr>(b_check_lkup);
		//full_data2::<Fr>(b_check_lkup); //full data high acc state
		//full_data3::<Fr>(b_check_lkup); //full data large file
		//full_data4::<Fr>(b_check_lkup); //full data large file
		//full_par::<Fr>(b_check_lkup); //full data large file
		//full_par2::<Fr>(b_check_lkup); //full_data4 files, 8 parallel jobs
		//full_clam_short_file::<Fr>();
		//full_clamav::<Fr>(b_check_lkup, _b_light_test, _b_setup); //full data large file

		// Drain any in-flight log lines on the stdout drainer before
		// declaring success, so the sentinel is never written ahead of
		// the final lines that prove "ok".
		utils::logger::flush_logger();

		// Completion sentinel for run_checkpoints.py. Not reached if
		// full_par panics -- panic aborts the test, no sentinel written.
		let sentinel = format!(
			"{}/data/cache/run_complete.sentinel",
			utils::os::proj_root());
		let _ = std::fs::write(&sentinel, "ok\n");
	}

	/// Discharge-approach stats over the paper_data debug bundle.
	/// Invoke via:
	/// `cargo test -p zkregplus -- test_db_bundle --show-output --nocapture`
	#[test]
	pub fn test_db_bundle(){
		let b_cache = false;
		let b_quick = true;
		/*
		let range_bits = 26;
		super::run_db_bundle::<Fr>(
			"data/paper_data/debug_config", //config dir
			"data/paper_data/reports", //report dir
			b_cache, b_quick, range_bits);
		*/
		let range_bits = 27; 
		super::run_db_bundle::<Fr>(
			"data/paper_data/dna/config", //config dir
			"data/paper_data/dna/reports", //report dir
			b_cache, b_quick, range_bits);
	}

	/// ZK discharge of the full clean chr17 sample (light-test,
	/// single job). HEAVY — expect hours / large RAM. Invoke via:
	/// `cargo test -p zkregplus -- test_full_dna --show-output --nocapture`
	#[test]
	pub fn test_full_dna(){
		full_dna::<Fr>(false);
	}
}
