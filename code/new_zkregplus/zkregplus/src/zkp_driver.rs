/* ZkregPlus Main Driver
	Created: 01/31/2025
*/

//use std::collections::{HashSet};
use utils::{logger::{log,LOG1,log_perf}, timer::Timer as GTimer};
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
			driver::{foldpot_main},
		}
	}
};
use std::{rc::Rc, cell::RefCell};
use crate::circs::{
	composable_gadget_mapper::{CompositeGadgetMapper},
	cp_mapper::{CpComponentMapper,CpCapacity},
	sed_mapper::{SedComponentMapper,SedCapacity},
	dfa_mapper::{DfaComponentMapper,DfaCapacity},
};

use rayon::prelude::*;


// --------- type aliases for zkp_driver below -------------
type LK<F> = LookupTableTwoCol_Inst<F>;
type GM<F> = CompositeGadgetMapper<F,LK<F>>;
type FC<F,C,CS> = SigmaIR1CS_Inst<F,C,CS,LK<F>,GM<F>,false>;
// --------- type aliases for zkp_driver above -------------

/// load the files and pack them as nibbles
/// return (words in packed nibbles, word info, file names)
fn load_files<F:PrimeField + ColEle>(list_file_path: &str, db: &ClamavDB<F>, cfg:&ClamavApproxConfig, _b_read_cache: bool, _b_write_cache: bool, _cache_dir: &str)
	->(Vec<Vec<F>>, Vec<WordInfo>, Vec<String>){
	//1. read the list of files
	let _b_debug = false;
	let proot = proj_root();
	let file_names = &read_lines(&format!("{}/{}", proot, list_file_path));

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
				&db.sig_to_id); //use optimize mode
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
/// The reason is that we need to avoid complex calculation of capacity
///   to satisfy the requirement that inp_buf = oup_buf for each circuit.
/// The layers of circuit as onstructed as following: each layer
/// has 1 circuit. These layers are organized as several
///    categories, and each category has a group of circuits
///    with different capacities.
/// e.g., the following is a structure of 3 categories where category 
/// (1) [cp, sed] and (2) [cp, sed, dfa_1], (3) [cp, sed, dfa_4]
/// where for (3), the number of DFAs is 4.
/// To reduce the number of circs needed which impacts final decider
/// circuit, we assume the SAME word chunk length for all the
/// circuits. Thus for circs in the SAME category, they differ
/// in the capacity of internal buffer.
///
/// When we increase capacities, we do this in two levels:
/// level1 (between category) : increase subsigs, sigs supported, and DFAs.
/// level2 (inside each category): increase the internal buffer.
///
/// Return: 2d layer of circs, but each layer has 1 circ.
/// It's arranged from low cost to high cost so that the first
/// circ satisfying a certain capacity will be the best one.
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
	db: Rc<ClamavDB<F>>,
	init_cp_capacity_cs: &CpCapacity,
	init_sed_capacity_cs: &SedCapacity,
	init_dfa_capacity: &DfaCapacity, //no cs/igc distinction
	init_cp_capacity_igc: &CpCapacity,
	init_sed_capacity_igc: &SedCapacity,
	num_category: usize, 
	num_circs_per_category: usize,
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
	let avg_lk_wd = lkup_len/total_word_n + 1;
	let avg_lk_wd = if avg_lk_wd<1 {1} else {avg_lk_wd};
	let lk_share = if b_check_lkup {chunk_len*avg_lk_wd} else{
		16 }; //give a SMALLER lkup_share if we do not check lkup

	//3. build up each category
	let mut layer_circs = vec![];
	let mut cp_cap_cs= init_cp_capacity_cs.clone();
	let mut cp_cap_igc= init_cp_capacity_igc.clone();
	let mut sed_cap_cs = init_sed_capacity_cs.clone();
	let mut sed_cap_igc = init_sed_capacity_igc.clone();
	let mut dfa_cap= init_dfa_capacity.clone();

	for l1 in 0..num_category{
		for l2 in 0..num_circs_per_category{
			//3.1 create cp (cs and igc)
			let cp_cs = CpComponentMapper::<F,LK<F>>::new(
				cp_cap_cs.clone(), db.clone(), false);
			let cp_igc = CpComponentMapper::<F,LK<F>>::new(
				cp_cap_igc.clone(), db.clone(), true);

			//3.2 create sed (it has both cs and igc built in)
			let sed = SedComponentMapper::<F,LK<F>>::new(
				sed_cap_cs.clone(), 
				sed_cap_igc.clone(), 
				db.clone());

			//3.3 dfa is optional depending if config supports 0 subsigs
			//which enforces dfa to be nil.
			let dfa = if dfa_cap.subsigs==0{ None }else{
				Some(
					DfaComponentMapper::<F,LK<F>>::new(dfa_cap.clone(), 
						db.clone())
				)
			};

			//3.4 construct the circuit
			let hybrid_cgm1 =if dfa_cap.subsigs==0{
				CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
					vec![
						Rc::new(RefCell::new(cp_cs)),
						Rc::new(RefCell::new(cp_igc)),
						Rc::new(RefCell::new(sed)),
					]
				)
			}else{//including the dfa
				CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
					vec![
						Rc::new(RefCell::new(cp_cs)),
						Rc::new(RefCell::new(cp_igc)),
						Rc::new(RefCell::new(sed)),
						Rc::new(RefCell::new(dfa.unwrap())),
					]
				)
			};
			let b_cyclepair = false;	
			let circ= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
			CompositeGadgetMapper<F,LK<F>> ,false> ::new_adv(
				format!("circ_cat_{}_circ_{}", l1, l2), 
				poseidon_config.clone(), 
				Rc::new(RefCell::new(hybrid_cgm1)), 
				false, //b_full_mode (whether supporting cyclepair - no for 
						//regular circuit) 
				lk_share,
				b_cyclepair, b_check_lkup
			).expect("error building circ");
			layer_circs.push( vec![circ] ); //legacy to keep 2d layer

			//3.5 update the capacities.
			cp_cap_cs = cp_cap_cs.increased_copy(2); //increase by level 2
			sed_cap_cs = sed_cap_cs.increased_copy(2); 
			cp_cap_igc = cp_cap_igc.increased_copy(2); //increase by level 2
			sed_cap_igc = sed_cap_igc.increased_copy(2); 
			dfa_cap= dfa_cap.increased_copy(2); 
		}//for loop level2
		//update level 1 capacity
		cp_cap_cs = cp_cap_cs.increased_copy(1); //increase by level 1
		sed_cap_cs = sed_cap_cs.increased_copy(1); 
		cp_cap_igc = cp_cap_igc.increased_copy(1); //increase by level 1
		sed_cap_igc = sed_cap_igc.increased_copy(1); 
		dfa_cap= dfa_cap.increased_copy(1); 
	}//for category

	//return
	layer_circs
}

/// build the list of circs. Note: for convenience of implementation,
/// we put the circ config hard coded in this function. To change
/// config, modify the local variables at the beginning of this function.
/// DEPRECATED
#[allow(dead_code)]
fn build_circs<F,C,CS>(poseidon_config: &PoseidonConfig<F>, total_word_n: usize, lkup_len: usize, db: Rc<ClamavDB<F>>, b_check_lkup: bool ) 
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
	let _cg4 = CompositeGadgetMapper::<F,LK<F>>::new("w4",vec![Rc::new(RefCell::new(comp4))]); 
	let _cg3 = CompositeGadgetMapper::<F,LK<F>>::new("w3",vec![Rc::new(RefCell::new(comp3))]); 
	let _cg2 = CompositeGadgetMapper::<F,LK<F>>::new("w2",vec![Rc::new(RefCell::new(comp2))]); 
	*/
	let cg1 = CompositeGadgetMapper::<F,LK<F>>::new("cp1",vec![
		Rc::new(RefCell::new(comp1.clone())), 
		Rc::new(RefCell::new(comp1_igc.clone())), 
	]); 
	//println!("DEBUG USE 1001: lkup_len: {}, avg_lk_wd: {}, comp1 share size: {}", lkup_len, avg_lk_wd, cg1.max_word_len()*avg_lk_wd);

	//2. create sed components
	let scap1= SedCapacity::new(max_word, db.dfa_crit.state_part_bits, subsigs, 
		avg_pats_per_subsig, avg_active_pats_per_subsig, basis_pats_in_trace, perc_pats_expansion_rate, sigs, perc_comp_subsigs, basis_unique_states, basis_acc_states);
	let scomp1 = SedComponentMapper::<F,LK<F>>::new(scap1.clone(), scap1, db.clone());
	//let scg1 = CompositeGadgetMapper::<F,LK<F>>::new("sed1",vec![Rc::new(RefCell::new(scomp1))]); 


	let lk_share1 = max_word*avg_lk_wd;
	let b_cyclepair = false;
	//let lk_share2 = max_word*2*avg_lk_wd;
	let _c1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c1"), poseidon_config.clone(), 
			Rc::new(RefCell::new(cg1)), false, lk_share1,
			b_cyclepair, b_check_lkup).expect("c1");
	/*
	let _c2 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c2"), poseidon_config.clone(), 
			Rc::new(RefCell::new(_cg2)), false, lk_share2).expect("c2");
	let _c3 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c3"), poseidon_config.clone(), 
			Rc::new(RefCell::new(_cg3)), false, lk_share2).expect("c3");
	let _c4 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c4"), poseidon_config.clone(), 
			Rc::new(RefCell::new(_cg4)), false, lk_share2).expect("c4");
	*/

	//4. create sed instances
	//let sc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("sc1"), poseidon_config.clone(), 
	//		Rc::new(RefCell::new(scg1)), false, lk_share1).expect("sc1");

	//5. create dfa components and instances
	let sigs=3;
	let subsigs=6;
	let d_cap1 = DfaCapacity::new(max_word, sigs, subsigs);
	let dcomp1 = DfaComponentMapper::<F,LK<F>>::new(d_cap1, db.clone());
	//let dcg1 = CompositeGadgetMapper::<F,LK<F>>::new("d1",
	//	vec![Rc::new(RefCell::new(dcomp1))]);
	//let dc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("dfa1"), poseidon_config.clone(), 
	//		Rc::new(RefCell::new(dcg1)), false, lk_share1).expect("dc1");

	let hybrid_cgm1 = CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
		vec![
			Rc::new(RefCell::new(comp1)),
			Rc::new(RefCell::new(comp1_igc)),
			Rc::new(RefCell::new(scomp1)),
			Rc::new(RefCell::new(dcomp1)),
		]);
	let _hc1= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("hc1"), poseidon_config.clone(), 
			Rc::new(RefCell::new(hybrid_cgm1)), false, lk_share1,
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
pub fn zkp_driver<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S> 
(
	sig_file: &str, 
	list_file_to_scan: &str, 
	_logfile: &str, 
	b_read_cache: bool, 
	b_write_cache: bool, 
	cache_dir: &str, 
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize, //see the definition of params for build_circs for below
	init_cp_capacity: &CpCapacity, 
	init_sed_capacity: &SedCapacity,
	init_dfa_capacity: &DfaCapacity,
	num_category: usize,
	num_circs_per_category: usize,
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
    CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
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
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
    <E as Pairing>::ScalarField: ColEle,
{
	// re-use the capacity for BOTH cs and ignore_case
	// this is usaully inefficient for ignore_case (but
	// we do this for small samples for convenience)
	zkp_driver_adv::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(sig_file, list_file_to_scan, _logfile,
		b_read_cache, b_write_cache, cache_dir,
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		chunk_len,
		init_cp_capacity, init_sed_capacity, init_dfa_capacity,
		init_cp_capacity, init_sed_capacity, 
		num_category, num_circs_per_category, b_check_lkup
	);
}
pub fn zkp_driver_adv<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S> 
(
	sig_file: &str, 
	list_file_to_scan: &str, 
	_logfile: &str, 
	b_read_cache: bool, 
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
	num_category: usize,
	num_circs_per_category: usize,
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
    CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
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
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
    <E as Pairing>::ScalarField: ColEle,
{
	//1. build or load the clamdb
	let log_level = LOG1;
	let mut gt1 = GTimer::new();
	log(log_level, &format!("=== ZKP driver starts ===="));
	let poseidon_config = poseidon_canonical_config::<CF1<C1>>();
	let mut vlog = vec![];
    let cfg = default_clamav_cfg();
    let db = ClamavDB::<CF1<C1>>::build_or_load(&cfg, sig_file, 
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		&mut vlog, cache_dir, b_read_cache, b_write_cache)
		.expect("db creation error");
	if log_level>=LOG1+1{
    	db.print_summary(&mut vlog);
	}
	log_perf(log_level, &format!("ZIP driver step 1: build DB."), &mut gt1);
	
	//2. load the files as vec of words
	let (vec_words, vec_word_info, vec_word_fnames) = load_files::<CF1<C1>>(list_file_to_scan, &db, &cfg, b_read_cache, b_write_cache, cache_dir);
	let total_word_len:usize = vec_words.iter().map(|w| w.len()).sum();
	let lkup_len = db.lkup.get_size();
	log_perf(log_level, &format!("ZIP driver step 2: load words."), &mut gt1);

	//3. build the circuits
	let rc_db = Rc::new(db.clone());
	let vec_circs = build_circs_adv::<CF1<C1>,C1,CS1>(
		&poseidon_config, 
		total_word_len, 
		chunk_len,
		lkup_len, 
		rc_db,
		init_cp_capacity_cs,
		init_sed_capacity_cs,
		init_dfa_capacity,
		init_cp_capacity_igc,
		init_sed_capacity_igc,
		num_category,
		num_circs_per_category,
		b_check_lkup
	);
	log_perf(log_level, &format!("ZIP driver step 2: build circs."), &mut gt1);

	//4. run the foldpot_main
	let sample_individual_prf = 0; //generate individual proof 1 (idx is 0)
	let lkup = Rc::new(RefCell::new(db.lkup));
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
		lkup, vec_circs, vec_words, vec_word_info, sample_individual_prf,vec_word_fnames).expect("main err");

}

#[cfg(test)]
pub mod tests_zkp_driver{
	use ark_ff::{PrimeField};
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
	use data_processor::{
		clam_db::{RANGE2_BIT},
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
		assert!(RANGE2_BIT==8, "set RANGE2_BIT to 8");
		let b_read_cache = false;
		let b_write_cache = !b_read_cache;
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
		let perc_pats_expansion_rate = 100;

		let num_category = 1;
		let num_circs_per_category= 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, RANGE2_BIT, subsigs, 
			avg_pats_per_subsig, avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_read_cache,
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}

	/// the sigs are the same as small data
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// COST: 18GB and 160 sec
	#[allow(dead_code)]
	fn small_data2<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==18, "set RANGE2_BIT to 18");
		let b_read_cache = false;
		let b_write_cache = !b_read_cache;
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

		let num_category = 1;
		let num_circs_per_category= 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, RANGE2_BIT, subsigs, 
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
			max_word, RANGE2_BIT, 
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
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_read_cache,
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
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}

	/// This function is used for debugging
	#[allow(dead_code)]
	fn small_data_debug<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==24, "set RANGE2_BIT to 24");
		let b_read_cache = false;
		let b_write_cache = !b_read_cache;
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

		let num_category = 1;
		let num_circs_per_category= 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, RANGE2_BIT, subsigs, 
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
			&format!("{}/sigs_debug2.dat",set1), //src sig
			&format!("{}/binexec_debug2.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_read_cache,
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}


	/// the sigs are the same as small data2
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// has 2 second long word (eady and almost no match)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// Difference: 2 categories and 2 circs each (multiple circs) -> 4 circs
	/// for testing circ selection
	#[allow(dead_code)]
	fn small_data3<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==18, "set RANGE2_BIT to 18");
		let b_read_cache = false;
		let b_write_cache = !b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 1;  //good value 2
		let subsigs = 3;  //good value 4
		let avg_pats_per_subsig = 3;  //good value 4
		let avg_active_pats_per_subsig = 0; //good value 0, actually does
			//not matter?
		let basis_pats_in_trace = 2;  //good value 4
		let perc_comp_subsigs = 34;  //good value 34 
		let basis_unique_states = 2;  //good value 5
		let basis_acc_states = 1;  //good value 2
		let dfa_sigs = 1;
		let dfa_subsigs= 2*dfa_sigs;
		let perc_pats_expansion_rate = 100;

		let num_category = 2;
		let num_circs_per_category= 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, RANGE2_BIT, subsigs, 
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


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec2.dat",set1), //list of files to discharge
			"data/small_data_set/reports/small_data3.dat", //report
			b_read_cache,
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}

	/// the sigs are the FULL SET of sigs
	/// However, just run a small file
	#[allow(dead_code)]
	fn full_data1<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==26, "set RANGE2_BIT to 26");
		let b_read_cache = true;
		let b_write_cache = ! b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa 
		//let max_word= 512; 
		let max_word= 512 * 4; 
		let sigs = 320;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let num_category = 1;
		let num_circs_per_category= 1;
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
			max_word, RANGE2_BIT, subsigs, 
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
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_1.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report.dat", //report
			b_read_cache,
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}
	/// the sigs are the FULL SET of sigs
	/// It runs a small but challenging file _codecs_hk.so (158kb)
	#[allow(dead_code)]
	fn full_data2<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==26, "set RANGE2_BIT to 26");
		assert!(RANGE2_BIT==26, "set RANGE2_BIT to 26");
        let b_read_cache = true;
        let b_write_cache = ! b_read_cache;
        let set1 = "data/debug/full_data_set/config/"; //for dfa
        //let max_word= 512;
        let max_word= 512 * 4;
        let sigs = 320;
        let subsigs = 500; //220 for prev db
        let avg_pats_per_subsig = 8; //old value 8
        let avg_active_pats_per_subsig = 3;
        let perc_comp_subsigs = 20;
        let num_category = 1;
        let num_circs_per_category= 1;
        let basis_unique_states = 1000; //ld vlaue 19 cpercent
    //    let basis_acc_states = 200; //old value 9 cpercent --> GOOD setting
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
			max_word, RANGE2_BIT, subsigs, 
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
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_2.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_read_cache,
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			num_category,
			num_circs_per_category,
			b_check_lkup
		);
	}

	/// the sigs are the FULL SET of sigs
	/// It runs a large but difficult file: gdb (6.6M)
	/// COST: stmt_len: 12.7M => all_w_e = 42M => circ1 100M R1CS
	/// prove_step: 39 sec
	/// if using max_word 512 *8 (128kb) => it's 21M. prove_step: 60 sec
	/// IMPROVEC COST: after applying the tricks of separating
	///    igc and cs. stmt_len: 10M, all_w_e: 33M => circ1 72M R1CS
	#[allow(dead_code)]
	fn full_data3<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==26, "set RANGE2_BIT to 26");
		let b_read_cache = true;
		let b_write_cache = ! b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
        let max_word= 512 * 4;
        let sigs = 350;
        let subsigs = 500; //220 for prev db
        let avg_pats_per_subsig = 8; //old value 8
        let avg_active_pats_per_subsig = 3;
        let perc_comp_subsigs = 20;
        let num_category = 1;
        let num_circs_per_category= 1;
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
			max_word, RANGE2_BIT, subsigs, 
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
            max_word, RANGE2_BIT, subsigs,
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
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_3.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_read_cache,
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
			num_category,
			num_circs_per_category,
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
	#[allow(dead_code)]
	fn full_data4<F:PrimeField>(b_check_lkup: bool){
		assert!(RANGE2_BIT==26, "set RANGE2_BIT to 26");
		let b_read_cache = true;
		let b_write_cache = ! b_read_cache;
        let set1 = "data/debug/full_data_set/config/"; //for dfa
        let max_word= 512 * 4;
        let sigs = 380;
        let subsigs = 560; //220 for prev db
        let avg_pats_per_subsig = 8; //old value 8
        let avg_active_pats_per_subsig = 2;
        let perc_comp_subsigs = 20;
        let num_category = 1;
        let num_circs_per_category= 1;
        let basis_unique_states = 2000; //15 cpercent
        let basis_acc_states = 1800; //9 cpercent
        let basis_pats_in_trace = 3000; //old value 100 cur value 1/1000.
        let basis_acc_states_igc = basis_acc_states ; //9 cpercent
        let basis_pats_in_trace_igc = basis_pats_in_trace;
            //old value 100 cur value 1/1000.
        let dfa_sigs = 6;
        let dfa_subsigs= 6;
        let perc_pats_expansion_rate = 30; //old good value 2
        let perc_pats_expansion_rate_igc = 30;
        //let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, RANGE2_BIT, subsigs, 
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
            max_word, RANGE2_BIT, subsigs,
            avg_pats_per_subsig,
            avg_active_pats_per_subsig,
            basis_pats_in_trace_igc,
            perc_pats_expansion_rate_igc,
            sigs,
            perc_comp_subsigs,
            basis_unique_states,
            basis_acc_states_igc,
        );

		//just test one at a time
		let min = 2; //starting: 0
		let max = 3; //max possible: 8
		for id in min..max{
			zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
				&format!("{}/main.dat",set1), //src sig
				&format!("{}/binexec_4_{}.dat",set1, id+1), //list of files to discharge
				"data/debug/full_data_set/reports/report2.dat", //report
				b_read_cache,
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
				num_category,
				num_circs_per_category,
				b_check_lkup
			);
		}
	}


	#[test]
	pub fn test_zkreg_main(){//test zkreg.main
		let b_check_lkup = false;
		//small_data::<Fr>(b_check_lkup); //small data
		small_data2::<Fr>(b_check_lkup);  //10k data 
		//small_data_debug::<Fr>(b_check_lkup);  //for debug
		//small_data3::<Fr>(b_check_lkup); //multi circ of 10k data -> fails
		//full_data1::<Fr>(b_check_lkup);
		//full_data2::<Fr>(b_check_lkup); //full data high acc state 
		//full_data3::<Fr>(b_check_lkup); //full data large file
		//full_data4::<Fr>(b_check_lkup); //full data large file
	}
}
