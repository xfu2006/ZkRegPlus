/* ZkregPlus Main Driver
	Created: 01/31/205
*/

//use std::collections::{HashSet};
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
use utils::{
	os::{proj_root, read_lines,read_nibbles,read,write_to_file},
	data::{pack_nibbles}
};
use data_processor::{
	clamav::{default_clamav_cfg, quick_discharge_file_adv},
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
			sigma_ir1cs::{LookupTableTwoCol_Inst,SigmaIR1CS_Inst,WordInfo,SigmaIR1CS,LookupTableTwoCol,GadgetMapper},
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
};
use rayon::prelude::*;


// --------- type aliases for zkp_driver below -------------
type LK<F> = LookupTableTwoCol_Inst<F>;
type GM<F> = CompositeGadgetMapper<F,LK<F>>;
type FC<F,C,CS> = SigmaIR1CS_Inst<F,C,CS,LK<F>,GM<F>,false>;
// --------- type aliases for zkp_driver above -------------

/// load the files and pack them as nibbles
fn load_files<F:PrimeField>(list_file_path: &str, db: &ClamavDB<F>, cfg:&ClamavApproxConfig, b_read_cache: bool, b_write_cache: bool, cache_dir: &str)
	->(Vec<Vec<F>>, Vec<WordInfo>){
	//1. read the list of files
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

	let sdir = format!("{}/data/cache/{}/", &proj_root(), cache_dir);
    let vec_word_info= if b_read_cache{
		let s_wi= read(&format!("{}/vec_word_info.txt", sdir));
		let vec_word_info:Vec<WordInfo> = serde_json::from_str(&s_wi)
				.expect("Convert vec_sigs fails");
		println!("DEBUG USE 2001: loaded vec_word_info: {:?}", vec_word_info);
		vec_word_info
	}else{
		let vec_word_info = file_names.into_par_iter().map(|fpath|
		{
			let abspath = format!("{}/{}", &proj_root(), fpath);
			let nibbles = read_nibbles(&abspath);
			let rec = quick_discharge_file_adv(
				fpath, 
				&nibbles,
				&db.vec_sigs,
				&db.map_crit_pat, 
				&db.map_crit_pat_igc, 
				&db.dfa_crit, 
				&db.bundle_subsig.vec_acdfa[0], //dfa_patterns, 
				&db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
				cfg, 
				&db.sig_to_id); //use optimize mode

			println!("DEBUG USE 1001: quic_res: {:?}", rec);
			rec
		}).collect::<Vec<WordInfo>>();

		if b_write_cache{
			let s_wi = serde_json::to_string(&vec_word_info).unwrap();
			write_to_file(&format!("{}/vec_word_info.txt", &sdir), &s_wi);
			println!("DEBUG USE 2002: SAVED vec_word_info: {:?}", vec_word_info);
		}
		vec_word_info
	};

	(final_data, vec_word_info)
}

/// build the list of circs. Note: for convenience of implementation,
/// we put the circ config hard coded in this function. To change
/// config, modify the local variables at the beginning of this function.
fn build_circs<F,C,CS>(poseidon_config: &PoseidonConfig<F>, total_word_n: usize, lkup_len: usize, db: Rc<ClamavDB<F>> ) 
->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb,
{

	// TEMP PLAN: remove later
	// each circ has one composite mapper which consists of one component 
	// mapper which has fixed length. Two circs, one handling length 8,
	// one handling length 4.

	//1. create cp_components
	let avg_lk_wd = lkup_len/total_word_n;
	let avg_lk_wd = if avg_lk_wd<1 {1} else {avg_lk_wd};
	let cap1 = CpCapacity{max_word_len: 1, final_states_len: 8, join_buf_capacity: 4, sig_buf_capacity: 2};
	let cap2 = CpCapacity{max_word_len: 2, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 2};
	let cap3 = CpCapacity{max_word_len: 3, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let cap4 = CpCapacity{max_word_len: 4, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let b_igc = false;
	let comp1 = CpComponentMapper::<F,LK<F>>::new(cap1, db.clone(), b_igc);
	let comp2 = CpComponentMapper::<F,LK<F>>::new(cap2, db.clone(), b_igc);
	let comp3 = CpComponentMapper::<F,LK<F>>::new(cap3, db.clone(), b_igc);
	let comp4 = CpComponentMapper::<F,LK<F>>::new(cap4, db.clone(), b_igc);
	let _cg4 = CompositeGadgetMapper::<F,LK<F>>::new("w4",vec![Rc::new(RefCell::new(comp4))]); 
	let _cg3 = CompositeGadgetMapper::<F,LK<F>>::new("w3",vec![Rc::new(RefCell::new(comp3))]); 
	let _cg2 = CompositeGadgetMapper::<F,LK<F>>::new("w2",vec![Rc::new(RefCell::new(comp2))]); 
	let cg1 = CompositeGadgetMapper::<F,LK<F>>::new("w1",vec![Rc::new(RefCell::new(comp1))]); 
	println!("DEBUG USE 1001: lkup_len: {}, avg_lk_wd: {}, comp1 share size: {}", lkup_len, avg_lk_wd, cg1.max_word_len()*avg_lk_wd);

	//2. create sed components
	let max_word = 1;
	let sigs = 2;
	let subsigs = 4;
	let avg_pat_per_sig = 4;
	let avg_active_pat_per_sig = 2;
	let store_id = 0; //implies 'all' for sig_id, for SED
	let perc_pats_in_trace = 40;
	let scap1= SedCapacity::new(max_word, db.dfa_crit.state_part_bits, subsigs, 
		avg_pat_per_sig, avg_active_pat_per_sig, perc_pats_in_trace, sigs);
	let scomp1 = SedComponentMapper::<F,LK<F>>::new(scap1, db.clone(), b_igc, store_id);
	let scg1 = CompositeGadgetMapper::<F,LK<F>>::new("w1",vec![Rc::new(RefCell::new(scomp1))]); 


	let lk_share1 = cg1.max_word_len()*avg_lk_wd;
	let lk_share2 = _cg2.max_word_len()*avg_lk_wd;
	let _c1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c1"), poseidon_config.clone(), 
			Rc::new(RefCell::new(cg1)), false, lk_share1).expect("c1");
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

	//4. create sed instances
	let sc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("sc1"), poseidon_config.clone(), 
			Rc::new(RefCell::new(scg1)), false, lk_share1).expect("sc1");

	//vec![ vec![c4,c3], vec![c2,c1] ]
	//vec![ vec![_c2,_c1] ] //for saving cost
	//vec![ vec![_c1] ] //for saving cost
	vec![ vec![sc1] ] //for saving cost
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
{
	//1. build or load the clamdb
	let poseidon_config = poseidon_canonical_config::<CF1<C1>>();
	let mut vlog = vec![];
    let cfg = default_clamav_cfg();
    let db = ClamavDB::<CF1<C1>>::build_or_load(&cfg, sig_file, 
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		&mut vlog, cache_dir, b_read_cache, b_write_cache);
    db.print_summary(&mut vlog);
	
	//2. load the files as vec of words
	let (vec_words, vec_word_info) = load_files::<CF1<C1>>(list_file_to_scan, &db, &cfg, b_read_cache, b_write_cache, cache_dir);
	let total_word_len:usize = vec_words.iter().map(|w| w.len()).sum();
	let lkup_len = db.lkup.get_size();

	//3. build the circuits
	let rc_db = Rc::new(db.clone());
	let vec_circs = build_circs::<CF1<C1>,C1,CS1>(&poseidon_config, total_word_len, lkup_len, rc_db);

	//4. run the foldpot_main
	let sample_individual_prf = 0; //generate individual proof 1
	let lkup = Rc::new(RefCell::new(db.lkup));
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>>(
		lkup, vec_circs, vec_words, vec_word_info, sample_individual_prf).expect("main err");

}

#[cfg(test)]
pub mod tests_zkp_driver{
	use ark_ff::{PrimeField};
	use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
	use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
	use ark_groth16::Groth16;
	use folding_schemes::{commitment::{pedersen::Pedersen, kzg::KZG}};
	use crate::zkp_driver::{zkp_driver};

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


	fn small_data<F:PrimeField>(){
		let b_read_cache = false;
		let b_write_cache = true;
		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			"data/small_data_set/config/sigs.dat", //src sig
			"data/small_data_set/config/binexec.dat", //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_read_cache,
			b_write_cache,
			"small_20", //cache name
			"data/small_data_set/config/dfa.dat", //signs that need dfa
			"data/small_data_set/config/ised.dat", //signs that need ised 
			"data/small_data_set/config/ised_igc.dat", //signs that need ised igc
		);
	}


	#[test]
	pub fn test_zkreg_main(){//test zkreg.main
		small_data::<Fr>();
	}
}
