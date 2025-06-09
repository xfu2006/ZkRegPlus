/* Created 10/02/2024 */


use std::{rc::Rc, cell::RefCell};
use core::marker::PhantomData;
use crate::commitment::CommitmentScheme;
use crate::{
	folding::{
		foldpot::{
			sigma_ir1cs::{LookupTableTwoCol,SigmaIR1CS,SigmaIR1CS_Inst,SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig,GadgetMapper,StatementInst,StatementExtraInfo,StatementConfig},
			circuits_super::{field_to_usize},
		},
		circuits::{nonnative::uint::NonNativeUintVar},
	},
	Error
};
use ark_ec::{CurveGroup};
use ark_ff::{PrimeField,BigInteger,Field};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_crypto_primitives::sponge::{
	constraints::CryptographicSpongeVar,
    poseidon::{PoseidonConfig, PoseidonSponge, constraints::PoseidonSpongeVar},
    Absorb, CryptographicSponge,
};
use ark_r1cs_std::{
	fields::{fp::FpVar,FieldVar},
	alloc::AllocVar, 
	R1CSVar,
	eq::EqGadget,
	boolean::{Boolean},
	bits::uint8::UInt8,
	ToBitsGadget,
	ToBytesGadget,
};
use ark_crypto_primitives::crh::{
	sha256::{
		constraints::{Sha256Gadget, UnitVar},
		Sha256,
	},
	CRHScheme, CRHSchemeGadget,
};
use sha2::{Sha256 as Sha256Raw, Digest};


/// compute hash_chain using Sha256.
/// We don't use Poseidon here as we need to compute the same hash 
/// for input (as bits) over two different fields.
/// Here we consider Bn254's scalar and prime field (we assume both
/// are close but not exactly 256-bits). So each number (hash)
/// is represented using two field elements (each 128-bit).
/// Here hc: is the previous hashchain (represented using 2 field elements,
/// each up to 128 bits).
/// a is a vector of field elements (each is padded to 256-bit).
/// It returns 2 field elements representing the result of new hashchain.
/// where hashchain_out = hash(hashchain_in, <a>)
pub fn compute_hc<F:PrimeField + Absorb>(hc: &(F,F), a: &Vec<F>)->(F,F)
{
	let mut hasher = Sha256Raw::new();
	let mut vec_bytes = vec![hc.0.into_bigint().to_bytes_le(), 
		hc.1.into_bigint().to_bytes_le()];
	for x in a{ vec_bytes.push(x.into_bigint().to_bytes_le()); }
	let all_bytes = vec_bytes.concat();
	hasher.update(&all_bytes);
	let result = hasher.finalize();
	assert!(result.len()==32);
	let res1 = result[0..16].to_vec();
	let res2 = result[16..32].to_vec();
	let ret = (F::from_le_bytes_mod_order(&res1), F::from_le_bytes_mod_order(&res2));
	ret
}

/// convert a uint var to FpVar
fn uint8_to_fp<F:PrimeField>(v: &UInt8<F>)->FpVar<F>{
	let cs = v.cs();
	let u8_val = v.value().unwrap();
	let f_u8_val = F::from(u8_val as u32);
	let res = FpVar::<F>::new_witness(cs.clone(), || Ok(f_u8_val)).unwrap();
	res
}

/// 16 bytes to one FpVar (it's about 128 bits - so safe for
/// most curves in use, e.g., bn254 and bls12-381).
/// little endian.
fn sixteen_char_to_fp_le<F:PrimeField>(chars: &Vec<UInt8<F>>) -> FpVar<F>{
	assert!(chars.len()==16);
	let cs = chars[0].cs();
	let mut factor = FpVar::new_constant(cs.clone(), F::one()).unwrap();
	let unit = FpVar::new_constant(cs.clone(), F::from(256u32)).unwrap(); 
	let mut res = FpVar::new_witness(cs.clone(), 
		|| Ok(F::zero())).unwrap();
	for i in 0..16{
		let ele = uint8_to_fp(&chars[i]);
		res = res + ele * factor.clone();
		factor = factor * unit.clone();
	}
	res
}

/// This works for Var in native arithmetics.
///
/// Cost: 124k (for 2 + 3 field elements) -> around 25k each
pub fn compute_hc_var<F:PrimeField>(
	hc: &(FpVar<F>, FpVar<F>), 
	a: &Vec<FpVar<F>>, 
	cs: ConstraintSystemRef<F>)->(FpVar<F>, FpVar<F>){
	let vec_fq = vec![vec![hc.0.clone(), hc.1.clone()], a.clone()].concat();
	let all_bytes = vec_fq.iter().map(|x| 
		x.to_bytes().unwrap()).into_iter().
		flatten().collect::<Vec<UInt8<F>>>();
	let unitVar = UnitVar::default();
	let res1 = <Sha256Gadget<F> as CRHSchemeGadget<Sha256,F>>::evaluate(&unitVar, &all_bytes).unwrap();
	let res_bytes = res1.to_bytes().unwrap();	
	assert!(res_bytes.len()==32);
	let res1 = res_bytes[0..16].to_vec();
	let res2 = res_bytes[16..32].to_vec();
	let ret = (sixteen_char_to_fp_le(&res1),sixteen_char_to_fp_le(&res2));

	ret
}

/// convert a nonnative uint var to unsigned bytes Var.
fn nonnative_to_bytes<F:PrimeField>(x: &NonNativeUintVar<F>)
-> Vec<UInt8<F>>{
	let bits: Vec<Boolean<F>> = x.to_bits_le().unwrap();
	let chunks = bits.chunks(8); //8 bits per chunk
	let mut ret = vec![];
	for x in chunks{ ret.push(UInt8::from_bits_le(x));}

	ret
}

/// Computes the sha256 hashchain non-natively.
/// Here NonNativeUIntVar corresponds to FpVar over 2nd curve
///
/// Cost: 124k (for 2 + 3 field elements) -> around 25k each
pub fn compute_hc_var_nonnative<F:PrimeField>(
	hc: &(NonNativeUintVar<F>, NonNativeUintVar<F>), 
	a: &Vec<NonNativeUintVar<F>>, 
	cs: ConstraintSystemRef<F>)->(NonNativeUintVar<F>, NonNativeUintVar<F>){

	let vec_fq = vec![vec![hc.0.clone(), hc.1.clone()], a.clone()].concat();
	let all_bytes = vec_fq.iter().map(|x| 
		nonnative_to_bytes(x)).into_iter().
		flatten().collect::<Vec<UInt8<F>>>();
	let unitVar = UnitVar::default();
	let res1 = <Sha256Gadget<F> as CRHSchemeGadget<Sha256,F>>::evaluate(&unitVar, &all_bytes).unwrap();
	let res_bytes = res1.to_bytes().unwrap();	
	assert!(res_bytes.len()==32);
	let res1 = res_bytes[0..16].to_vec();
	let res2 = res_bytes[16..32].to_vec();
	let ret = (sixteen_char_to_fp_le(&res1),sixteen_char_to_fp_le(&res2));
	let ret2 = (
		NonNativeUintVar::<F>::new_witness(cs.clone(), || Ok(ret.0.value().unwrap())).unwrap(),
		NonNativeUintVar::<F>::new_witness(cs.clone(), || Ok(ret.1.value().unwrap())).unwrap(),
	);

	ret2
}



/// A gadget that computes the hashchain(a) and hashchain(b) for
/// a,b in e(a,b). Statement structure is shown below:
/// 
/// statement [gt1, a, b, gt2, hc(a)_in, hc(b)_in, hc(a)_out, hc(b)_out].
/// Where: gt2 = gt1 + e(a,b).
/// gt1 and gt2 are 12 field elements each, a is 3, and b is 5
/// field elements.
/// hc(a) and hc(b) are hashchain(a) and hashcain(b),
/// the _in and _out will be mapped to input and output buffer
/// respectively. hashchain(a)_out = hash(hashchain(a)_in, a).
/// Each hashchain costs 2 field element (128-bits each - reason:
/// later will be computed on BOTH bn254 and grumpkin).
/// Total: 12 + 3 + 5 + 12 + 2 + 2 + 2 + 2 = 40 field elements.
pub struct FoldPairGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
}

impl <F:PrimeField + Absorb> SigmaGadget<F> for FoldPairGadget<F>{
	/// statment size: 40, and all messages are 0.
	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		(40, 0, 0, 0)
	}

	fn gen_msg1(&self, stmt_vec: &Vec<F>, v_idx: &Vec<usize>) -> Vec<F>{
		vec![]
	}

	fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: 
		&Vec<usize>, msg1_vec: &Vec<F>, idx_msg1: usize, len_msg1: usize,
		msg2_vec: &Vec<F>, idx_msg2: usize, len_msg2: usize) -> Vec<F>{
		vec![]
	}

	/// leave the gt2 = gt1 + e(a,b) to cyclepair component.
	/// compute hc(a)_out = hash(hc(a)_in, a), and
	/// hc(b)_out = hash(hc(b)_in, b)
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		//Given: statement [gt1,a,b,gt2,hc(a)_in,hc(b)_in,hc(a)_out,hc(b)_out].
		//hc_a_in is located at idx 32, hc_b_in at 33, etc.
		let hc_a_in = (wtns.statement[stmt_idx[32]].clone(),
						wtns.statement[stmt_idx[33]].clone());
		let hc_b_in = (wtns.statement[stmt_idx[34]].clone(),
						wtns.statement[stmt_idx[35]].clone());
		let hc_a_out = (wtns.statement[stmt_idx[36]].clone(),
						wtns.statement[stmt_idx[37]].clone());
		let hc_b_out = (wtns.statement[stmt_idx[38]].clone(),
						wtns.statement[stmt_idx[39]].clone());



		//a has 3 elements and starts at idx 12
		let a = vec![
			wtns.statement[stmt_idx[12]].clone(),
			wtns.statement[stmt_idx[13]].clone(),
			wtns.statement[stmt_idx[14]].clone(),
		];
		let b = vec![
			wtns.statement[stmt_idx[15]].clone(),
			wtns.statement[stmt_idx[16]].clone(),
			wtns.statement[stmt_idx[17]].clone(),
			wtns.statement[stmt_idx[18]].clone(),
			wtns.statement[stmt_idx[19]].clone(),
		];

		let computed_ha_out = compute_hc_var(&hc_a_in, &a, cs.clone());
		#[cfg(test)]{
		 assert!(computed_ha_out.0.value().unwrap()==
		 	hc_a_out.0.value().unwrap());
		 assert!(computed_ha_out.1.value().unwrap()==
		 	hc_a_out.1.value().unwrap());
		 println!("REMOVE LATER 101!");
		}
		let computed_hb_out = compute_hc_var(&hc_b_in, &b, cs.clone());
		#[cfg(test)]{
		 assert!(computed_hb_out.0.value().unwrap()==
		 	hc_b_out.0.value().unwrap());
		 assert!(computed_hb_out.1.value().unwrap()==
		 	hc_b_out.1.value().unwrap());
		}
		computed_ha_out.0.enforce_equal(&hc_a_out.0);
		computed_ha_out.1.enforce_equal(&hc_a_out.1);
		computed_hb_out.0.enforce_equal(&hc_b_out.0);
		computed_hb_out.1.enforce_equal(&hc_b_out.1);

		Ok(())
	}
}

/// FoldPairMapper consists of one gadget,
/// which computes the hash chain of a and b in e(a,b)
/// and relays the computation of pairing to CyclePair component.
/// We do not use lookup in FoldPair.
pub struct FoldPairMapper<F:PrimeField, LK:LookupTableTwoCol<F>>{
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
}

impl <F:PrimeField + Absorb, LK: LookupTableTwoCol<F>> 
GadgetMapper<F,LK> for FoldPairMapper<F, LK>{
	fn get_name(&self) -> String { "FoldPairMapper".to_string() }

	/// expect [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out]
	/// total: 12 + 3 + 5 + 12 + 2 + 2 + 2 + 2 = 40 field elements
	fn max_word_len(&self)->usize{ 40 }

	fn create_gadgets(&self) -> Vec<Rc<dyn SigmaGadget<F>>>{ 
		let f_gadget= FoldPairGadget::<F>{_f:PhantomData};
		vec![Rc::new(f_gadget)]
	}

	/// expecting full statement (constructed by the caller):
	/// [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out].
	/// maps them to:
	/// inp: gt1, hc_a_in, hc_b_in (size 16 = 12 + 2 + 2)
	/// oup: gt2, hc_a_out, hc_b_out (size 16)
	/// data: a and b (size 8)
	/// We do not rely on prev_stmt
	fn build_statement(&self, word: &Vec<F>, prev_stmt: &Option<StatementInst<F,LK>>, lkup: Rc<RefCell<LK>>, ea: &StatementExtraInfo<F>) -> Result<StatementInst<F,LK>, Error>{
		//1. retrieve the information
		assert!(word.len()==36);
		let gt1 = word[0..12].to_vec();
		let a = word[12..15].to_vec();
		let b = word[15..20].to_vec();
		let gt2 = word[20..32].to_vec();
		let hc_a_in = (word[32].clone(), word[33].clone());
		let hc_b_in = (word[34].clone(), word[35].clone());
		let hc_a_out = (word[36].clone(), word[37].clone());
		let hc_b_out = (word[38].clone(), word[39].clone());
		assert!(prev_stmt.is_none());

		//2. retrieve the previous counter from previous witness
		let (zero, one) = (F::zero(), F::one());
		let f_n_circ = ea.n_circ;
		let ncirc_minus_pci = f_n_circ-ea.pc_i;
		let stmt = StatementInst{
			pc_i: ea.pc_i,
			pc_i1: ea.pc_i1, 
			n_circ: f_n_circ,
			n_circ_minus_pc: ncirc_minus_pci,
			act_input_size: F::from(16u32),
			act_output_size: F::from(16u32),
			act_lookup_share_size: F::from(0u32),
			act_word_subseg_size: F::from(8u32),
			word_id: ea.word_id,
			subseg_id: ea.subseg_id,
			total_word_len: ea.total_word_len,
			total_word_segs: ea.total_word_segs,
			total_words: ea.total_words,
			r_F: zero, //for debug

			inp_buf: vec![gt1.clone(), 
				vec![hc_a_in.0, hc_a_in.1, hc_b_in.0, hc_b_in.1]].concat(), 
			oup_buf: vec![gt2.clone(), 
				vec![hc_a_out.0, hc_a_out.1, hc_b_out.0, hc_b_out.1]].concat(),  			word_subseg: vec![a, b].concat(), //8 elements
			data: vec![], //empty
			subtable_id: vec![zero; 16 + 16 + 8+ 0],
			col1_share: vec![zero; 0],  //do not perform lookup for the circuit
			col2_share: vec![zero; 0], 
			m_share: vec![zero; 0],

			_lk: PhantomData,
		};
			
		Ok(stmt)
	}

	fn gen_statement_structure(&self) -> 
		(usize, StatementConfig, Vec<Vec<usize>>, Vec<(usize,usize)>,
		Vec<usize>){
		//1. a sample statemnet structure
		let input_size = 16;
		let output_size = 16;
		let word_subseg_size = 8;
		let data_size = 0;
		let lookup_share_size = 0;
		let cfg = StatementConfig::new(
			input_size, output_size, word_subseg_size,
			data_size, lookup_share_size
		);

		//2. generate the result to return
		let mut comp_map = vec![];
		for i in 0..word_subseg_size {comp_map.push(cfg.idx_word_subseg+i)}

		panic!("GENERATE the cyclepair map");
		let opt_join_constraints = vec![];
		let cyclepair_map = vec![];
		//3. return
		(cfg.total_size(), cfg, vec![comp_map], opt_join_constraints, cyclepair_map)
	}

}


/// create the sigma_ir1cs instance for folding qa-nizk for
/// k circuits. It will eventually perform 3k+1 folding steps.
/// Becaues for each circuit, need to reason about commitments of
/// W_i, E_i, and F_i.
pub fn create_sigma_fold_pair<F,C,CS,LK,const H: bool>(k: usize, poseidon_config: PoseidonConfig<F>)-> SigmaIR1CS_Inst<F,C,CS,LK,H> 
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		LK: LookupTableTwoCol<F> + 'static,
		F: PrimeField + Absorb
{
	let mapper = FoldPairMapper::<F,LK>{_f: PhantomData, _lk: PhantomData};
	let sigma = SigmaIR1CS_Inst::<F, C, CS, LK, H>::new_adv("paircycle".to_string(), poseidon_config.clone(), Rc::new(mapper), true).expect("error new sigma");

	sigma
}


#[cfg(test)]
pub mod tests_sigma_cyclepair{
	use crate::{
		folding::{
			foldpot::{
				sigma_ir1cs::{LookupTableTwoCol_Inst,StatementExtraInfo,LookupTableTwoCol,ZiPartTwoInst,SigmaIR1CS,SigmaIR1CS_Inst},
				sigma_cyclepair::{create_sigma_fold_pair, compute_hc, compute_hc_var, compute_hc_var_nonnative},
			},
			circuits::{
				nonnative::{uint::NonNativeUintVar},
			}
		}
	};
    use ark_bn254::{constraints::GVar, Bn254, Fr, Fq, G1Projective as Bn254G1, G2Projective as Bn254G2};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

	use ark_ec::{pairing::Pairing};
	use crate::{
		frontend::{FCircuit},
		commitment::{pedersen::Pedersen},
		transcript::poseidon::poseidon_canonical_config,
	};
	use ark_std::{rand::RngCore,UniformRand,test_rng,One,Zero};
	use ark_ff::{PrimeField,ToConstraintField,BigInteger};
	use std::{rc::{Rc}, cell::{RefCell}};
	use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError,ConstraintSystem};
	use ark_r1cs_std::{
		fields::{fp::FpVar,FieldVar},
		alloc::AllocVar, 
		R1CSVar,
		eq::EqGadget,
		boolean::{Boolean},
		bits::uint8::UInt8,
		ToBitsGadget,
	};

	type F = Fq;
	type C = Projective2;
	type CS = Pedersen<C>;
	type LK = LookupTableTwoCol_Inst<F>;

	#[test]
	fn test_sha2(){
		//1. test the native version
		let mut rng = test_rng();
		let cs = ConstraintSystem::<Fr>::new_ref();
		let hc = (Fr::rand(&mut rng), Fr::rand(&mut rng));
		let hc_var = (
			FpVar::<Fr>::new_witness(cs.clone(), || Ok(hc.0)).unwrap(),
			FpVar::<Fr>::new_witness(cs.clone(), || Ok(hc.1)).unwrap());
		let a = vec![Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng)];
		let a_var = a.clone().into_iter().map(|v|
			FpVar::<Fr>::new_witness(cs.clone(), || Ok(v)).unwrap())
				.collect::<Vec<FpVar<Fr>>>();
		let res = compute_hc(&hc, &a);
		let res_var = compute_hc_var(&hc_var, &a_var, cs.clone());
		assert!(res_var.0.value().unwrap()==res.0);
		assert!(res_var.1.value().unwrap()==res.1);

		//2. nonnative version
		let cs2 = ConstraintSystem::<Fq>::new_ref();
		let hc_var2 = (
			NonNativeUintVar::<Fq>::new_witness(cs2.clone(),
			|| Ok(hc_var.0.clone().value().unwrap())).unwrap(),
			NonNativeUintVar::<Fq>::new_witness(cs2.clone(),
			|| Ok(hc_var.1.clone().value().unwrap())).unwrap() );
		let a_var2 = vec![
			NonNativeUintVar::<Fq>::new_witness(cs2.clone(),
			|| Ok(a_var[0].clone().value().unwrap())).unwrap(),
			NonNativeUintVar::<Fq>::new_witness(cs2.clone(),
			|| Ok(a_var[1].clone().value().unwrap())).unwrap(),
			NonNativeUintVar::<Fq>::new_witness(cs2.clone(),
			|| Ok(a_var[2].clone().value().unwrap())).unwrap()];
		let res_var2 = compute_hc_var_nonnative(&hc_var2, &a_var2, cs2.clone());
		assert!(res_var2.0.value().unwrap()==res.0.into());
		assert!(res_var2.1.value().unwrap()==res.1.into());
			
	}


	#[test]
	fn test_sigma_cyclepair(){
	/*
        let cfg= poseidon_canonical_config::<Fq>();
		let sigma = create_sigma_fold_pair::<F,C,CS,LK,false>(5, cfg.clone());
		let mapper = sigma.get_mapper();
		let lk = LK::new(vec![
			(F::from(0u32), F::from(0u32)), //0, null entry
		]);
		let lkup = Rc::new(RefCell::new(lk));
		let ea = StatementExtraInfo::<F>{
				total_words: F::one(),
				word_id: F::one(),
				subseg_id: F::zero(),
				total_word_len: F::from(32 as u32),
				total_word_segs: F::one(),
				n_circ: F::one(),
				pc_i: F::zero(),
				pc_i1: F::zero(),
				act_word_subseg_size: F::from(8u32),
				hash_cmF: F::zero(), 
			};
		let mut rng = test_rng();
		let a =  Bn254G1::rand(&mut rng);
		let b =  Bn254G2::rand(&mut rng);

		let t1 =  Bn254G1::rand(&mut rng);
		let t2 =  Bn254G2::rand(&mut rng);
		let gt1 = Bn254::pairing(t1, t2).0;
		let gt2 = gt1 * Bn254::pairing(a,b).0;
		let vec_a = a.to_field_elements().unwrap(); //3 compared with get_cm in utils, wasted one element.
		let vec_b = b.to_field_elements().unwrap(); //5.
		let vec_gt1 = gt1.to_field_elements().unwrap();
		let vec_gt2 = gt2.to_field_elements().unwrap();
		let hc_a_in = Fq::rand(&mut rng);
		let hc_b_in = Fq::rand(&mut rng);
		let hc_a_out = compute_hc::<Fq>(&cfg, &hc_a_in, &vec_a);
		let hc_b_out = compute_hc::<Fq>(&cfg, &hc_b_in, &vec_b);
	
		let inp = vec![vec_gt1, vec_a, vec_b, vec_gt2, 
			vec![hc_a_in, hc_b_in, hc_a_out, hc_b_out]].concat();
		let stmt = mapper.build_statement(&inp, &None, lkup,&ea).unwrap();
		*/

/* RECOVER LATER
		let zi_part2_inst = ZiPartTwoInst::<F>::dummy();
		let (wtns, _, zipart2) = sigma.gen_witness(&stmt.to_vec(), 
			&zi_part2_inst);
		let cs = ConstraintSystemRef::<F>::new_ref();
		let external_inputs = vec![];
		let z_i = vec![];
		sigma.generate_step_constraints(cs.clone(), 0, z_i, &external_inputs);
		assert!(cs.is_satisfied());
*/
	}
}
