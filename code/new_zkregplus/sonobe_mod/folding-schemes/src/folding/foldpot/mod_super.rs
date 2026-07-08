use std::sync::Arc;
/// Replication of the mod.rs, which defines the data structures
/// such as committed instance and witness for the supernova version.
/// <https://eprint.iacr.org/2022/1758.pdf>
/* Created 08/30/2024 
	Revised: 10/07/2024 -> Added x2 (support of FoldPair)
*/

use utils::{logger::{log, log_perf, emit_stdout, LOG3,LOG4}, timer::Timer as GTimer};

use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{Group, CurveGroup, pairing::{Pairing} };

use crate::folding::foldpot::from_field::{AffineFromField};
use ark_ff::{BigInteger, PrimeField,Field,ToConstraintField};
use ark_r1cs_std::{
    prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	//prelude::*,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem,SynthesisMode};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};
use core::marker::PhantomData;
use sha3::{Sha3_256,Digest};

use crate::commitment::{CommitmentScheme};
use crate::folding::circuits::cyclefold::{fold_cyclefold_circuit, CycleFoldCircuit};
use crate::folding::circuits::{CF1,CF2,CF3};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNative, Transcript};
use crate::Error;
use crate::FoldingScheme;
use crate::{
    arith::r1cs::{extract_r1cs, extract_w_x, R1CS},
    utils::{get_cm_coordinates},
	folding::nova,
	folding::nova::{
		Witness, CommittedInstance,
		traits::NovaR1CS,
		//PreprocessorParam, ProverParams, VerifierParams,
	},
	folding::foldpot::{
		CommittedInstanceFoldPot, WitnessFoldPot, PreprocessorParamFoldPot,
		ProverParamsFoldPot, VerifierParamsFoldPot, 
		FOLDPOT_CF_N_POINTS, dummy_instance_foldpot, get_r1cs_from_cs,
		nifs::{NIFSFoldPot},
		circuits_super::{ChallengeGadgetFoldPotSuper,AugmentedFCircuitFoldPotSuper, field_to_usize},
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,LookupTableTwoCol_Inst,ZiPartTwoInst,StatementInst, GadgetMapper, cost_capture_begin, cost_capture_take, print_cost_report},
		utils::{f1_limbs_to_f2, f1_to_f2_limbs, get_mem_usage_mb,mb2s},
		cyclepair::{CyclePairCircuit,fold_cyclepair_circuit},
		qa_nizk::{QaNizkProverParams,QaNizkVerifierParams,SparseMatrix,setup_qa_nizk,prove_qa_nizk_fast},
		sigma_cyclepair::{compute_hc},
		decider_eth_circuit_super::{KZGChallengesGadgetSuper},
		utils::{B_DEBUG, B_DEBUG2, B_DEBUG3}
	}
};
// utility function for compute step cmF
/// `job_id`: The ID of the job being processed.
pub fn compute_step_hc_cmF_adv<
	C1: CurveGroup,
	LK:LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1,H>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,
C = C1>,
	const H: bool
>(
	hc_cmF: C1::ScalarField, 
	stmt: &StatementInst<C1::ScalarField, LK>,
	circ: &FC,
	_cs_pp: &CS1::ProverParams,
	poseidon_config: &PoseidonConfig<C1::ScalarField>,
	_job_id: usize
) -> Result<(C1::ScalarField,C1), Error>
where
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
{
	//1. create the sponge
	let mut sponge_cmf = 
		PoseidonSponge::<C1::ScalarField>::new(poseidon_config);

	//2. compute the cmF using witness of F
	//let act_idx = field_to_usize(&self.pc_i);
	let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
	let zi_part2 = ZiPartTwoInst::dummy(circ.is_full_mode(), fq_bits); //does not matter
	let cmF:C1 = circ.gen_cmF(&stmt.to_vec(), &zi_part2)
		.expect("gen_cmF error");

	let mut vec_cmF = vec![];
	cmF.to_native_sponge_field_elements_as_vec()
		.to_sponge_field_elements(&mut vec_cmF);
	let to_hash = vec![
		vec![hc_cmF],
		vec_cmF,
	].concat();
	sponge_cmf.absorb(&to_hash);

	//3. hash the result
	let new_hc_cmF:C1::ScalarField=sponge_cmf.squeeze_field_elements(1)[0];
	Ok( (new_hc_cmF, cmF) )
}


/// SuperNova version of CmomittedInstance. It is just a collection
/// of the standard CommittedInstance
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstanceFoldPotSuper<C: CurveGroup> {
	pub vec_inst: Vec<CommittedInstanceFoldPot<C>>,
	/// global x_1 value for Hash(cycle_fold_U)
	/// NOTE: for all committed instances, only its x[0] will be checked,
	/// their x[1] is moved out as global x_1 because we keep only one copy
	/// of cyclefold gadget.
	pub x_1: C::ScalarField,
	/// Hash(cycle_fold_pair) , optional only used in full mode
	pub x_2: Option<C::ScalarField>,
	/// the circuit ID to USE when fold with incoming instance.
	pub pc_i: C::ScalarField,
}

impl<C: CurveGroup> CommittedInstanceFoldPotSuper<C> {
    pub fn dummy(io_len: usize, n_inst: usize, b_full: bool) -> Self {
		let mut vec = vec![];
		let zero = C::ScalarField::zero();
		for _i in 0..n_inst{ 
        	vec.push(CommittedInstanceFoldPot{
				cmE: C::zero(),
				u: C::ScalarField::zero(),
				cmW: C::zero(),
				x: vec![C::ScalarField::zero(); io_len],
				cmF: C::zero(),
				}
			);
		}
		let x_2 = if b_full {Some(zero)} else {None};
		Self {vec_inst: vec, x_1: zero, x_2: x_2, pc_i: zero}
    }

	/// generate the (inp_sum, g1, g2, oup_sum) where
	/// oup_sum = inp_sum + e(g1, g2)
	/// these are serialized to vector of field elements
	/// size 3k+2 where k = n_circ - 1
	pub fn generate_cyclepair_inputs<E: Pairing<G1=C>>(&self, 
		_pkey: &QaNizkProverParams<E>, 
		vkey: &QaNizkVerifierParams<E>,
		com_all: &E::G1, prf_qa_nizk: &E::G1,
		poseidon_config: &PoseidonConfig<C::ScalarField>)
		->Vec<Vec<C::ScalarField>>
		where
		C: ToConstraintField<CF2<C>>, 
		<C as Group>::ScalarField: PrimeField + Absorb,
		<C as CurveGroup>::BaseField: PrimeField,
		<E as Pairing>::TargetField: ToConstraintField<CF2<C>>,
		<E as Pairing>::G2: ToConstraintField<CF2<C>>,
	{
		//1. collect all C1 elements
		//let mut res = vec![];
		let k = self.vec_inst.len();
		let mut vec_x = vec![];
		vec_x.push(com_all.clone());
		for i in 0..k{
			vec_x.push(self.vec_inst[i].cmW);
			vec_x.push(self.vec_inst[i].cmE);
			vec_x.push(self.vec_inst[i].cmF);
		}
		let minus_prf = C::zero() - prf_qa_nizk;
		if B_DEBUG {//check if it works
			use crate::folding::foldpot::qa_nizk::{QaNizkProof,verify_qa_nizk};
			let prf:QaNizkProof<E> = QaNizkProof{prf:prf_qa_nizk.clone()};
			assert!(verify_qa_nizk(&vec_x, &prf, vkey), "qanizk failed");
			assert!(minus_prf + prf_qa_nizk == C::zero());
		}
		vec_x.push( minus_prf ); 
		assert!(vec_x.len()==3*k+2);

		//2. build the vector of [gt1, a, b, gt2] so that
		//gt2 = gt1 + e(a,b) [note here + is represented as *]
		//a is from vec_x, b is from vkey.
		//gt1 starts from [0]_T, and we expect the last gt2
		//to be [0]_T
		let mut vec_tuples = vec![];
		// NOTE: E::pairing(a,b) returns a group element, its +
		// is equivalent to E::pairing(a,b).0 (target filed) *
		// so here E::TargetField::one() is essentially e(a,b)^0
		// the zero group element.
		let gt: E::TargetField = E::TargetField::one();
		let mut gt1 = gt.clone();
		assert!(vkey.c.len()==3*k+1);
		for i in 0..vec_x.len(){
			let a = vec_x[i].clone();
			let b = if i<vec_x.len()-1 {vkey.c[i].clone()} else {vkey.a.clone()};
			let prod = E::pairing(&a, &b).0;
			let gt2 = gt1 * prod; 
			vec_tuples.push( (gt1.clone(), a, b, gt2.clone()) );

			if B_DEBUG {
				if i==vec_x.len()-1{
					assert!(gt2.is_one()); // it's to assert that as a
					//group element it's zero
				}
			}
			gt1 = gt2.clone();
		}

		//3. build the output
		let mut vec_res = vec![];
		let mut ha_out = C::ScalarField::zero();
		let mut hb_out = C::ScalarField::zero();
		for i in 0..vec_tuples.len(){
			let (gt1, a, b, gt2) = vec_tuples[i];	
			let ha_in = ha_out.clone();
			let hb_in = hb_out.clone();

			let vec_gt1_raw:Vec<C::BaseField> = 
				gt1.to_field_elements().unwrap(); 
			let vec_gt1 = vec_gt1_raw.into_iter().map(|a|
				f1_to_f2_limbs::<C::BaseField,C::ScalarField>(&a) )
				.collect::<Vec<Vec<C::ScalarField>>>()
				.concat();
			assert!(vec_gt1.len()==12*5);

			let vec_a_raw = a.to_field_elements().unwrap(); 
			let vec_a = vec_a_raw.into_iter().map(|a|
				f1_to_f2_limbs::<C::BaseField,C::ScalarField>(&a) )
				.collect::<Vec<Vec<C::ScalarField>>>()
				.concat();
			assert!(vec_a.len()==3*5);

			let vec_b_raw:Vec<C::BaseField> = b.to_field_elements().unwrap(); 
			let vec_b = vec_b_raw.into_iter().map(|a|
				f1_to_f2_limbs::<C::BaseField,C::ScalarField>(&a) )
				.collect::<Vec<Vec<C::ScalarField>>>()
				.concat();
			assert!(vec_b.len()==5*5);

			let vec_gt2_raw:Vec<C::BaseField> = 
				gt2.to_field_elements().unwrap(); 
			let vec_gt2 = vec_gt2_raw.into_iter().map(|a|
				f1_to_f2_limbs::<C::BaseField,C::ScalarField>(&a) )
				.collect::<Vec<Vec<C::ScalarField>>>()
				.concat();
			assert!(vec_gt2.len()==12*5);

			ha_out = compute_hc(&poseidon_config, &ha_in, &vec_a);
			hb_out = compute_hc(&poseidon_config, &hb_in, &vec_b);

			let vec_all = vec![vec_gt1, vec_a, vec_b, vec_gt2,
				vec![ha_in, hb_in, ha_out, hb_out]].concat();
			assert!(vec_all.len()==164);


			vec_res.push(vec_all);
		}

		assert!(vec_res.len()==3*k+2);
		vec_res
	}

	pub fn dump(&self, msg: &str){
		for i in 0..self.vec_inst.len(){
			let inst = &self.vec_inst[i];
			emit_stdout(format!(
				"{}:   {}: cmE: {:?}, u: {}, cmW: {:?}, \
				x: {:?}, cmF: {:?}",
				msg, i, inst.cmE, inst.u, inst.cmW,
				inst.x, inst.cmF));
		}
		emit_stdout(format!(
			"{}:  x_1: {}, pc_i: {}", msg, self.x_1, self.pc_i));

	}
}

impl<C: CurveGroup> Absorb for CommittedInstanceFoldPotSuper<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        // This is never called
        unimplemented!()
    }

	/// note that the dest size is linear in the number of 
	/// instances
    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
		for x_inst in &self.vec_inst{
			x_inst.to_sponge_field_elements(dest);
		}
		self.x_1.to_sponge_field_elements(dest);
		if self.x_2.is_some(){
			self.x_2.to_sponge_field_elements(dest);
		}
		self.pc_i.to_sponge_field_elements(dest);

    }
}

impl<C: CurveGroup> AbsorbNonNative<C::BaseField> for 
CommittedInstanceFoldPotSuper<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
{
    // Compatible with the in-circuit `CycleFoldCommittedInstanceVar::to_native_sponge_field_elements`
    // in `cyclefold.rs`.
    fn to_native_sponge_field_elements(&self, dest: &mut Vec<C::BaseField>) {
		for x_inst in &self.vec_inst{
			x_inst.to_native_sponge_field_elements(dest);
		}
		[self.x_1].to_native_sponge_field_elements(dest);
		if self.x_2.is_some(){
			[self.x_2.unwrap()].to_native_sponge_field_elements(dest);
		}
		[self.pc_i].to_native_sponge_field_elements(dest);
    }
}

impl<C: CurveGroup> CommittedInstanceFoldPotSuper<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// hash implements the committed instance hash compatible 
	/// with the gadget implemented in
    /// nova/circuits.rs::CommittedInstanceVarSuper.hash.
    /// Returns `H(i, pc_i, z_0, z_i, U_i)`, 
	/// where `i` can be `i` but also `i+1`, and `U_i` is the
    /// `CommittedInstance`. Notice that a pc_i is added for SuperNova
	/// standing for the selected instance
    pub fn hash<T: Transcript<C::ScalarField>>(
        &self,
        sponge: &T,
        pp_hash: C::ScalarField, // public params hash
        i: C::ScalarField,
		pc_i: C::ScalarField,
        z_0: Vec<C::ScalarField>,
        z_i: Vec<C::ScalarField>,
    ) -> C::ScalarField {
		let zero = C::BaseField::zero();
		let _tp = (&zero, &zero);
        let mut sponge = sponge.clone();

        sponge.absorb(&pp_hash);
        sponge.absorb(&i);
        sponge.absorb(&pc_i);
        sponge.absorb(&z_0);
        sponge.absorb(&z_i);
		let mut U_vec: Vec<_> = vec![];
		let _elements = self.to_sponge_field_elements::<C::ScalarField>(&mut U_vec);
        sponge.absorb(&U_vec);
        let res: C::ScalarField = sponge.squeeze_field_elements(1)[0];


		res
    }
}


/// Essentially a collection of witness for each circuit.
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct WitnessFoldPotSuper<C: CurveGroup> {
	pub vec_wit: Vec<WitnessFoldPot<C>>
}


impl<C: CurveGroup> WitnessFoldPotSuper<C>
where
    <C as Group>::ScalarField: Absorb,
{
	/// start_F: the starting position of Fixed Mem segment in AugmentedCircuit
	/// witness, size_F: the size of the fixed mem segment
    pub fn new<const H: bool>(vec_wit: Vec<WitnessFoldPot<C>>)->Self{
		Self{ vec_wit}
	}

    pub fn dummy(vec_w_len: Vec<usize>, vec_e_len: Vec<usize>) -> Self {
		let mut v_wit: Vec<WitnessFoldPot<C>> = vec![];
		for i in 0..vec_w_len.len(){
			let (w_len, e_len) = (vec_w_len[i], vec_e_len[i]);
			v_wit.push( WitnessFoldPot::dummy(w_len, e_len) );
		}
        Self { vec_wit: v_wit }
    }

	/// generate KZG commitment to all W||E from all witness, and also
	/// the qa_nizk proof
	/// return (com_all_w, r_all_w, prf_qa_nizk, prf_kzg, kzg_challenge) 
	/// note proof kzg contains
	/// the evaluation point (which is the Fiat shamir of U1 and com_all).
	/// Note the r_all_w is the random used.
	pub fn gen_com_all_w_and_qa_nizk_prf<E: Pairing<G1=C,ScalarField=C::ScalarField>, CS1E: CommitmentScheme<C, HC, ProverChallenge=C::ScalarField,Challenge=C::ScalarField>, const HC: bool>
		(&self, 
			pkey: &QaNizkProverParams<E>, 
			comkey: &CS1E::ProverParams, 
			_vkey: &QaNizkVerifierParams<E>, 
			Ui1: &CommittedInstanceFoldPotSuper<C>, 
			poseidon_config: &PoseidonConfig<C::ScalarField>) 
	-> (C, C, C::ScalarField, CS1E::Proof, C::ScalarField)
where
    C: CurveGroup,
    C::ScalarField: PrimeField,
    <C as CurveGroup>::BaseField: PrimeField,
    C::ScalarField: Absorb,
{
		//1. collect all w
		let mut all_w = self.vec_wit.iter().map(|it| it.W.clone())
			.flatten().collect::<Vec<C::ScalarField>>();
		let mut all_e = self.vec_wit.iter().map(|it| it.E.clone())
			.flatten().collect::<Vec<C::ScalarField>>();
		all_w.append(&mut all_e);
		let mut rng = rand::rngs::OsRng;
		let r_all_w = C::ScalarField::rand(&mut rng);

		//2. generate the proof
		let qa_prf = prove_qa_nizk_fast(&all_w, r_all_w, pkey);
		let prf = qa_prf.prf.clone();

		//3. generate all commitment and the proof
		all_w.push(r_all_w);
		let zero = C::ScalarField::zero();
		let com_all = CS1E::commit(&comkey, &all_w, &zero).expect("err in cmt");
		let kzg_all_com_ch = KZGChallengesGadgetSuper::<C>
			::get_challenge_native(poseidon_config, Ui1.clone(), com_all);


		if B_DEBUG {
			use crate::folding::foldpot::qa_nizk::verify_qa_nizk;
			let k = Ui1.vec_inst.len();
			let mut vec_x = vec![];
			vec_x.push(com_all.clone());
			for i in 0..k{
				vec_x.push(Ui1.vec_inst[i].cmW.clone());
				vec_x.push(Ui1.vec_inst[i].cmE.clone());
				vec_x.push(Ui1.vec_inst[i].cmF.clone());
			}
			assert!(verify_qa_nizk(&vec_x, &qa_prf, &_vkey), "qa_nizk failed");
		}

		let prf_kzg = CS1E::prove_with_challenge(&comkey,
			kzg_all_com_ch,
			&all_w,
			&zero, None).expect("kzg prf err");

		(com_all, prf, r_all_w, prf_kzg, kzg_all_com_ch)
	}


	/// produces the CommittedInstanceFold pot separately
    pub fn commit<CS: CommitmentScheme<C, HC>, const HC: bool>(
        &self,
        params: &CS::ProverParams,
        vec_x: Vec<Vec<C::ScalarField>>,
		x_1: C::ScalarField,
		x_2: Option<C::ScalarField>,
		pc_i: C::ScalarField,
    ) -> Result<CommittedInstanceFoldPotSuper<C>, Error> {
		let mut vec_inst = vec![];
		assert!(vec_x.len()==self.vec_wit.len());
		for i in 0..self.vec_wit.len(){
			let wit = &self.vec_wit[i];
			vec_inst.push( wit.commit::<CS,HC>(params, vec_x[i].clone() )? );
		}
		let ci = CommittedInstanceFoldPotSuper{ 
			vec_inst: vec_inst, x_1: x_1, x_2: x_2, pc_i: pc_i};
		Ok(ci)
    }
}

#[derive(Debug, Clone)]
pub struct PreprocessorParamFoldPotSuper<C1, C2, FC, CS1, CS2, LK, GM, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{
	pub vec_pp: Vec<PreprocessorParamFoldPot<C1, C2, FC, CS1, CS2, LK, GM, H>>,
	/// commitment key for lookup (just one copy)
	pub lk_pp: Option<CS1::ProverParams>,
	/// verification key for lookup (just one copy)
	pub lk_vp: Option<CS1::VerifierParams>,
	/// whether support cycle pair
	pub b_full_mode: bool,
}

impl<C1, C2, FC, CS1, CS2, LK, GM, const H: bool> PreprocessorParamFoldPotSuper<C1, C2, FC, CS1, CS2, LK, GM, H>
where
    C1: CurveGroup,
    <C1 as Group>::ScalarField: Absorb,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{
    pub fn new(poseidon_config: PoseidonConfig<C1::ScalarField>, vec_F: Vec<FC>,lk: Arc<LK>, vec_size_F: Vec<usize>, b_full_mode: bool) -> Self {
		let vec_F = vec_F.clone();
		let vec_size_F = vec_size_F.clone();
		
		let n = vec_F.len();
		assert!(vec_size_F.len()==n);
		let mut vec_pp = vec![];
		for i in 0..n{
			let pp = PreprocessorParamFoldPot::new(poseidon_config.clone(), 
				vec_F[i].clone(), lk.clone(), vec_size_F[i].clone());
			vec_pp.push(pp);
		}
		Self{vec_pp, lk_pp: None, lk_vp: None, b_full_mode}
    }

}

#[derive(Debug, Clone)]
pub struct ProverParamsFoldPotSuper<E: Pairing<G1=C1>, C1, C2, CS1, CS2, CS1E, LK, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    CS1E: CommitmentScheme<C1, H>, //should actually be KZG
{
	pub vec_pp: Vec<ProverParamsFoldPot<C1, C2, CS1, CS2, LK, H>>,
	pub qa_pp: Option<QaNizkProverParams<E>>,
	pub cs1e_pp: Arc<CS1E::ProverParams>,
}

#[derive(Debug, Clone)]
pub struct VerifierParamsFoldPotSuper<E: Pairing<G1=C1>, C1, C2, CS1, CS2, CS1E, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    CS1E: CommitmentScheme<C1, H>, //should actually be KZG
{
	pub vec_vp: Vec<VerifierParamsFoldPot<C1, C2, CS1, CS2, H>>,
	pub cp_r1cs: Option<Arc<R1CS<C2::ScalarField>>>,
	pub qa_vp: Option<QaNizkVerifierParams<E>>,
	pub cs1e_vp: CS1E::VerifierParams
}

impl<E: Pairing<G1=C1>, C1, C2, CS1, CS2, CS1E, const H: bool> 
VerifierParamsFoldPotSuper< E, C1, C2, CS1, CS2, CS1E, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    CS1E: CommitmentScheme<C1, H>, //should actually be KZG
{
    /// returns the hash of the public parameters of SuperNova
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
		let mut vec_hashes = vec![];
		for vp in &self.vec_vp{
			vec_hashes.push( vp.pp_hash().expect("pp_hash fails") );
		}
    	let mut hasher = Sha3_256::new();
		for x in &vec_hashes{
			let mut bytes = Vec::new();
			x.serialize_uncompressed(&mut bytes)?;
			hasher.update(&bytes);
		}
		let res = hasher.finalize();
		Ok( C1::ScalarField::from_le_bytes_mod_order(&res) )
    }
}


/// SuperNova version (it can be regarded as a collection of FoldPot instances)
/// with pc_i indicating the current pc (which circuit to use).
/// Compared with FoldPot (Nova + CycleFold) all elements are not vectors.
#[derive(Clone, Debug)]
pub struct FoldPotSuper<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E, CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, const H: bool>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM, C=C1>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    CS1E: CommitmentScheme<C1, H>, //should actually be KZG
	CF2<C1>: PrimeField,
	CF2<C2>: PrimeField,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	CF2<E::G1>: PrimeField,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	C2G2: CurveGroup,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>>,
{
	_gm: PhantomData<GM>,
	_e: PhantomData<E>,
	_p: PhantomData<P>,
	_c2g2: PhantomData<C2G2>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
	_cs1: PhantomData<CS1>,

    /// R1CS of the Augmented Function circuit
    pub r1cs: Vec<Arc<R1CS<C1::ScalarField>>>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: Arc<R1CS<C2::ScalarField>>,
	/// R1CS of the CyclePair circuit
	pub cp_r1cs: Arc<R1CS<C2::ScalarField>>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,

    /// CommitmentScheme::ProverParams over C11E (commits
	/// to the combined W for all subcircuits)
    pub cs1e_pp: Arc<CS1E::ProverParams>,
	/// vector of commitment schemes for cmW, cmE, cmF for each
	/// subcircuit
    pub cs_pp: Vec<Arc<CS1::ProverParams>>,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_pp: Arc<CS2::ProverParams>, //just one copy
    /// CyclePair CommitmentScheme::ProverParams, over C2
    pub cp_cs_pp: Arc<CS2::ProverParams>, //just one copy

    /// All F circuits, the circuit that is being folded
    pub F: Vec<FC>,
	/// the lookup table SHARED with all instances
	pub lk_tbl: Option<Arc<LK>>,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state  (shared with all circs)
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
	/// the the contents that hash to z0.1
	pub z0_part2_inst: ZiPartTwoInst<C1::ScalarField>, //ADDED, ALWAYS same
	/// the contents that hashes to of zi.1
	pub zi_part2_inst: ZiPartTwoInst<C1::ScalarField>, //ADDED
    /// Nova instances (enhanced with fixed MEM)
    pub w_i: WitnessFoldPot<C1>, //just one instance
    pub u_i: CommittedInstanceFoldPot<C1>, //just one instance
    pub W_i: WitnessFoldPotSuper<C1>, //VECTOR of instances
    pub U_i: CommittedInstanceFoldPotSuper<C1>,

    /// CycleFold running instances.
	/// ONLY one copy (all sub-circuits share the same cyclefold component)
	/// because cycle fold is UNIFORM.
    pub cf_W_i: Witness<C2>,
    pub cf_U_i: CommittedInstance<C2>,

	/// CyclePair Running insstance.
	pub cp_W_i: Option<Witness<C2>>,
	pub cp_U_i: Option<CommittedInstance<C2>>,
	pub b_full_mode: bool,

	// Added
	/// size of F (Fixed Mem) in W
	pub size_F: Vec<usize>,
	/// index of F in the AugmentedFCircuit (4 + external_inp.len)
	pub start_F: Vec<usize>,

	// Added for super nova
	/// the number of circuits
	pub n_circ: C1::ScalarField, 
	/// the initial pc
	pub pc_0: C1::ScalarField,
	/// the current pc (must be less than the number of circuits)
	pub pc_i: C1::ScalarField,

	/// the circuit ID to perform the next step computation
	pub pc_i1: C1::ScalarField,

	/// number of words
	pub n_words: usize,

	pub job_id: usize,

	/// cached (pre-computed) commitment to Fixed segments

	/// usually from pass1 of driver
	pub vec_precomputed_group_cmF: Option<Vec<C1>>,
}

/// This just creates DUMMY instance. 
/// n_circ and pc_0 is needed to create the intial statement instance
/// for dummy instance
pub fn dummy_instance_foldpot_super<C:CurveGroup>(r1cs: &Vec<R1CS<C::ScalarField>>, size_F: Vec<usize>, start_F: Vec<usize>, n_circ: usize, b_full: bool)
-> (WitnessFoldPotSuper<C>, CommittedInstanceFoldPotSuper<C>)
where <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField{
		let mut vec_wit = vec![];
		let mut vec_inst = vec![];
		for i in 0..n_circ{
			let (w2, u2) = dummy_instance_foldpot(&r1cs[i], 
				size_F[i], start_F[i]);
			vec_wit.push(w2);
			vec_inst.push(u2);
		}
		let x_1 = C::ScalarField::zero();
		let x_2 = if b_full {Some(C::ScalarField::zero())} else {None};
		let pc_i = C::ScalarField::zero();

		(WitnessFoldPotSuper::<C>{vec_wit}, 
			CommittedInstanceFoldPotSuper::<C>{
				vec_inst, x_1, x_2, pc_i}
		)
}

impl<E: Pairing<G1=C1, G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, 
C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, const H: bool> 
FoldPotSuper<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H>
where
//    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
 //   C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{

    /// Initializes the SuperNova+CycleFold's IVC for the 
	/// given parameters and initial state `z_0`.
	/// IMPORTANT NOTICE: z_0 and z_i actually consists of the FOLLOWING:
	/// (1) the hashchain of cmF from the previous stage.
	/// (2) the hash of z_0 or z_i_part2
	/// NOTE: for step 0, we will make an exception to pass the information
	/// of ALREADY computed FINAL hashchain of cmF (so that we can
	/// rebuild the z0_part2_inst using it. In this case `z_0[0]`
	/// will be the FINAL hashchain cmF (i.e., the r used for 
	/// z0_part2).  At this moment, because there is no step 1 information,
	/// zi_part2_inst is the same as z0_part2_inst
	/// NOTE2: difference from mod.rs (nova + cyclefold), the augmented
	/// circuit is different.
    pub fn init_adv(
        params: &(ProverParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, LK, H>,
			VerifierParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, H>),
        vec_F: Vec<FC>, //a vector of circs
        z_0: Vec<C1::ScalarField>,
		n_circ: usize,
		pc_0_value: usize,
		b_full: bool,
		ch: C1::ScalarField,
		rc: C1::ScalarField,
		n_words: usize,
		vec_precomputed_group_cmF: Option<Vec<C1>>,
		job_id: usize,
    ) -> Result<Self, Error> {
        let (pp, vp) = params;
		let size_F = pp.vec_pp.iter().map(|p| p.size_F)
			.collect::<Vec<usize>>();
		let start_F = pp.vec_pp.iter().map(|p| p.start_F)
			.collect::<Vec<usize>>();
		let pc_0 = C1::ScalarField::from(pc_0_value as u32);
		let j = pc_0_value;
		let b_full_mode = b_full;
		for f in &vec_F{assert!(f.is_full_mode()==b_full);}

		//1. rebuild z0_part2 using the given random seed
		assert!(z_0.len()==2, "z_0 length: {} is not 2!", z_0.len());
		let hash_cmF = z_0[0];
		let poseidon_config = pp.vec_pp[0].poseidon_config.clone();
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2_inst=ZiPartTwoInst::new(ch, rc, &poseidon_config, b_full_mode, fq_bits, n_words); 
		let z0_part2_hash = z0_part2_inst.hash(&poseidon_config);
		assert!(z0_part2_hash==z_0[1], "z0_part2_hash: {} != z0[1]: {}",
			z0_part2_hash, z_0[1]);
		let z0_new = vec![hash_cmF, z0_part2_hash]; //rewrite it

		//2. build the r1cs constraint systems
		let n_circs = pp.vec_pp.len();
		//let total_cs_pp_len:usize = pp.vec_pp.iter().map(|pp| 
		//	pp.cs_pp_len).sum();

		assert!(vec_F.len()==n_circs);
		let r1cs =  vec_F.iter().enumerate().map(|(j,circ)|{
        	let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        	let augmented_F_circuit =
            	AugmentedFCircuitFoldPotSuper::<C1, C2, GC2, LK, FC, GM, H>
					::empty(&poseidon_config, circ.clone(), n_circs, j, job_id);
        	augmented_F_circuit.generate_constraints(cs.clone()).expect("gen constraints failure");
        	cs.finalize();
        	let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem).expect("cs gen failure");
        	let r1cs = extract_r1cs::<C1::ScalarField>(&cs);
			r1cs
		}).collect::<Vec<R1CS<C1::ScalarField>>>();


		//3. build the cf_r1cs constraints 
		let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
		let cf_circuit= CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);
		cf_circuit.generate_constraints(cs2.clone())?;
		cs2.finalize();
		let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
		let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

		//4. build the cp_r1cs constraints 
		let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
		let cp_circuit= CyclePairCircuit::<E, P, C1, C2G2>::empty();
		cp_circuit.generate_constraints(cs2.clone())?;
		cs2.finalize();
		let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
		let cp_r1cs = extract_r1cs::<C1::BaseField>(&cs2);


        //4. compute the public params hash and dummy instances
        let pp_hash = vp.pp_hash()?;
        let (w_dummy, u_dummy) = dummy_instance_foldpot::<C1>(&r1cs[j], size_F[j], start_F[j]);
        let (W_dummy, U_dummy) = dummy_instance_foldpot_super::<C1>(&r1cs, size_F.clone(), start_F.clone(), n_circ, b_full);


        let (cf_w_dummy, cf_u_dummy): (nova::Witness<C2>, nova::CommittedInstance<C2>) = cf_r1cs.dummy_instance();
        let (cp_w_dummy, cp_u_dummy): (nova::Witness<C2>, nova::CommittedInstance<C2>) = cp_r1cs.dummy_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
		let _lktbl = LookupTableTwoCol_Inst::<C1::ScalarField>::dummy();
		let cs1e_pp = pp.cs1e_pp.clone();
		let cs_pp = pp.vec_pp.iter().map(|pp| pp.cs_pp.clone()).
			collect::<Vec<Arc<CS1::ProverParams>>>();

        Ok(Self {
			_gm: PhantomData,
			_e: PhantomData,
			_p: PhantomData,
			_c2g2: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cs1: PhantomData,
            r1cs: r1cs.into_iter().map(Arc::new).collect(),
            cf_r1cs: Arc::new(cf_r1cs),
			cp_r1cs: Arc::new(cp_r1cs),
            poseidon_config: poseidon_config.clone(),
            cs1e_pp: cs1e_pp, 
            cs_pp: cs_pp, 
            cf_cs_pp: pp.vec_pp[0].cf_cs_pp.clone(),
            cp_cs_pp: pp.vec_pp[0].cp_cs_pp.clone(),
            F: vec_F,
            pp_hash,
            i: C1::ScalarField::zero(),
            z_0: z0_new.clone(),
            z_i: z0_new, //fake value
			z0_part2_inst: z0_part2_inst.clone(),
			zi_part2_inst: z0_part2_inst,
            w_i: w_dummy.clone(),
            u_i: u_dummy.clone(),
            W_i: W_dummy,
            U_i: U_dummy,
            // cyclefold running instance
            cf_W_i: cf_w_dummy.clone(),
            cf_U_i: cf_u_dummy.clone(),
			// cyclepair running instnance
            cp_W_i: if b_full {Some(cp_w_dummy.clone())} else {None},
            cp_U_i: if b_full {Some(cp_u_dummy.clone())} else {None},
			b_full_mode: b_full,

			lk_tbl: Some(pp.vec_pp[0].lk_tbl.clone()),
			size_F: size_F,
			start_F: start_F,

			n_circ: C1::ScalarField::from(n_circs as u32),
			pc_0: pc_0.clone(),
			pc_i: pc_0.clone(),
			pc_i1: pc_0.clone(),

			n_words: n_words,
			job_id,
			vec_precomputed_group_cmF,
        })
    }


    // computes T and cmT for the circ to fold
    pub fn compute_cmT(&self, j: usize) 
	-> Result<(Vec<C1::ScalarField>, C1), Error> {
        NIFSFoldPot::<C1, CS1, H>::compute_cmT(
            &self.cs_pp[j],
            &self.r1cs[j],
            &self.w_i,
            &self.u_i,
            &self.W_i.vec_wit[j],
            &self.U_i.vec_inst[j],
        )
    }

	/// fold (U_i1, W_i1) from (U_i, W_i) and (u_i, w_i), and also return
	/// the random factor r_Fr, and also the cmT
	pub fn gen_next_folded(&self) ->Result<(CommittedInstanceFoldPotSuper<C1>, 
		WitnessFoldPotSuper<C1>, C1::ScalarField, C1), Error>{
		//TODO: check if j and pci_val is set up right
		let pci_val= field_to_usize(&self.pc_i);
		let (T, cmT) = self.compute_cmT(pci_val)?;

        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(
			&self.poseidon_config);
        let r_bits = ChallengeGadgetFoldPotSuper::<C1>::get_challenge_native(
            &mut transcript,
            self.pp_hash,
            self.U_i.clone(),
            self.u_i.clone(),
            cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(
			&r_bits)).ok_or(Error::OutOfBounds)?;


        let (W_i1_pci, U_i1_pci) = NIFSFoldPot::<C1, CS1, H>::fold_instances(
            r_Fr, 
			&self.W_i.vec_wit[pci_val], 
			&self.U_i.vec_inst[pci_val], 
			&self.w_i, 
			&self.u_i, 
			&T, 
			cmT,
        )?;
		let mut W_i1 = self.W_i.clone();
		let mut U_i1 = self.U_i.clone();
		W_i1.vec_wit[pci_val] = W_i1_pci;
		U_i1.vec_inst[pci_val] = U_i1_pci;


		Ok( (U_i1, W_i1, r_Fr, cmT) )
	}

    // folds the given cyclefold circuit and its instances
    #[allow(clippy::type_complexity)]
    fn fold_cyclefold_circuit<T: Transcript<C1::ScalarField>>(
        &self,
        transcript: &mut T,
        cf_W_i: Witness<C2>,           // witness of the running instance
        cf_U_i: CommittedInstance<C2>, // running instance
        cf_u_i_x: Vec<C2::ScalarField>,
        cf_circuit: CycleFoldCircuit<C1, GC1>,
        rng: &mut impl RngCore,
    ) -> Result<
        (
            Witness<C2>,
            CommittedInstance<C2>, // u_i
            Witness<C2>,           // W_i1
            CommittedInstance<C2>, // U_i1
            C2,                    // cmT
            C2::ScalarField,       // r_Fq
        ),
        Error,
    > {
        fold_cyclefold_circuit::<C1, GC1, C2, GC2, FC, CS1, CS2, H>(
            FOLDPOT_CF_N_POINTS,
            transcript,
            &*self.cf_r1cs,
            (*self.cf_cs_pp).clone(),
            self.pp_hash,
            cf_W_i,
            cf_U_i,
            cf_u_i_x,
            cf_circuit,
            rng,
        )
    }

	/// given the statement of the current step and the current hashchain
	/// of cmF, compute the cmF.
	pub fn compute_step_hc_cmF(&self, hc_cmF: C1::ScalarField, stmt: &StatementInst<C1::ScalarField, LK>) -> Result<(C1::ScalarField,C1), Error>{
		/* REMOVE LATER if the call of compute_step_hc_cmF_adv works
		//1. create the sponge
        let mut sponge_cmf = 
			PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);

		//2. compute the cmF using witness of F
		//let act_idx = field_to_usize(&self.pc_i);
		let act_idx = field_to_usize(&self.pc_i1);
		let circ = &self.F[act_idx];
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_part2 = ZiPartTwoInst::dummy(self.F[0].is_full_mode(), fq_bits); //does not matter
		/*
		let (wit, _wconfig, zi1_part2) = circ
			.gen_witness(&stmt.to_vec(), &zi_part2);
		let cmF = wit.gen_cmF::<C1,CS1,H>(&self.cs_pp[act_idx])
			.expect("gen_cmF error"); 
		*/


		let cmF = circ.gen_cmF::<C1,CS1,H>(
				&stmt.to_vec(), &zi_part2, &self.cs_pp[act_idx])
			.expect("gen_cmF error");

		let mut vec_cmF = vec![];
		cmF.to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(&mut vec_cmF);
		let to_hash = vec![
			vec![hc_cmF],
			vec_cmF,
		].concat();
		sponge_cmf.absorb(&to_hash);

		//3. hash the result
		let new_hc_cmF:C1::ScalarField=sponge_cmf.squeeze_field_elements(1)[0];
		Ok(new_hc_cmF)
		*/

		let act_idx = field_to_usize(&self.pc_i1);
		let circ = &self.F[act_idx];
		let cs_pp = &self.cs_pp[act_idx];
		compute_step_hc_cmF_adv::<C1, LK, CS1, GM, FC, H>(
			hc_cmF, stmt, circ, cs_pp, &self.poseidon_config, 0
		)
	}

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E, CF3<C2G2>> + std::fmt::Debug + Clone, 
C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, const H: bool> 
FoldingScheme<C1, C2, FC> for FoldPotSuper<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H>
where
 //   C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
  //  C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM, C=C1>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>, //required to be kzg
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
   // C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
    type PreprocessorParam = PreprocessorParamFoldPotSuper<C1, C2, FC, CS1, CS2, LK, GM,  H>;
    type ProverParam = ProverParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, LK, H>;
    type VerifierParam = VerifierParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, H>;
    type RunningInstance = (CommittedInstanceFoldPotSuper<C1>, WitnessFoldPotSuper<C1>);
    type IncomingInstance = (CommittedInstanceFoldPot<C1>, WitnessFoldPot<C1>);
    type MultiCommittedInstanceWithWitness = ();
	//still nova inst. but one pair for each circuit
    type CFInstance = (CommittedInstance<C2>, Witness<C2>);

    fn preprocess(
        mut rng: impl RngCore,
        prep_param_src: &Self::PreprocessorParam,
		job_id: usize,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
		let log_level = LOG3;
		let mut gt1 = GTimer::new();
		//0. process lookup globally
		let lookup = &prep_param_src.vec_pp[0].lk_tbl;
		let (_col1_raw, _col2_raw) = lookup.get_cols();
		let lkup_len = _col1_raw.len();
		let mut m1 = get_mem_usage_mb();
		let m0 = m1;
		log_perf(job_id, log_level, &format!("preprocess() START: lkup size: {}, RAM: {} ", lkup_len, mb2s(m1)), &mut gt1);
		let mut _cp_r1cs: Option<R1CS<C2::ScalarField>> = None;
		let mut vec_pp = vec![];
		let mut vec_vp = vec![];
		let m2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!("preprocess() Step 1: INCREASED RAM: {}. ", mb2s(m2-m1)), &mut gt1);
		m1 = m2;

		//TO IMPROVE: can be distributed. However, it's not trivial.
		// The reason is that F and PrepParams are not Send + Sync
		// will need raw scoped multi-threads and challenel passing,
		// not sure how it is going to affect performance.
		let mut total_w_len = 0;
		let mut total_e_len = 0;
		let mut elen = vec![];
		let n_circ = prep_param_src.vec_pp.len();
		let mut idx_j = 0;
		let mut max_circ_pp_size = 0;
		let mut cost_grand_total = 0usize;
		for prep_param in &prep_param_src.vec_pp{
			// arm the per-gadget cost sink; get_r1cs_super synthesizes
			// the inner circuit (filling it), then print a circN cost
			// report grouped by CP/SED/DFA component. Zero extra synthesis.
			cost_capture_begin();
			let (r1cs,cf_r1cs,cp_r1cs_in)
				= get_r1cs_super::<E, P, C2G2, C1, GC1, C2, GC2, FC, LK, GM,H>(
				&prep_param.poseidon_config,
				prep_param.F.clone(), n_circ, idx_j
				).expect("fail in generating r1cs");
			if let Some(cap) = cost_capture_take(){
				let spans = prep_param.F.component_spans();
				// skip the Phase-2 cyclepair circuit (FoldPairMapper):
				// only the main CP/SED/DFA folding circuits are reported.
				let is_cyclepair = spans.iter()
					.any(|(n,_)| n.contains("FoldPair"));
				if !cap.gadgets.is_empty() && !is_cyclepair{
					cost_grand_total += print_cost_report(
						&format!("circ{}", idx_j), &cap, &spans);
				}
			}
			idx_j += 1;
			if idx_j == n_circ && cost_grand_total > 0{
				emit_stdout(format!(
					"==== COST GRAND TOTAL over {} circuits = {} ====",
					n_circ, cost_grand_total));
			}
			//if idx_j==1{ cp_r1cs = Some(cp_r1cs_in.clone()); }

			let cs_pp: CS1::ProverParams;
			let cs_vp: CS1::VerifierParams;
			let cf_cs_pp: CS2::ProverParams;
			let cf_cs_vp: CS2::VerifierParams;
			let cp_cs_pp: CS2::ProverParams;
			let cp_cs_vp: CS2::VerifierParams;

			if prep_param.cs_pp.is_some()
				&& prep_param.cf_cs_pp.is_some()
				&& prep_param.cs_vp.is_some()
				&& prep_param.cf_cs_vp.is_some()
			{
				assert!(false, "unable to set elen here!");
				cs_pp = (*prep_param.clone().cs_pp.unwrap()).clone();
				cs_vp = prep_param.clone().cs_vp.unwrap();
				cf_cs_pp = (*prep_param.clone().cf_cs_pp.unwrap()).clone();
				cf_cs_vp = prep_param.clone().cf_cs_vp.unwrap();
				cp_cs_pp = (*prep_param.clone().cp_cs_pp.unwrap()).clone();
				cp_cs_vp = prep_param.clone().cp_cs_vp.unwrap();
			} else {
				let max_row_col = if r1cs.A.n_cols>r1cs.A.n_rows {r1cs.A.n_cols}
					else {r1cs.A.n_rows};
				// cmF commits stmt+msg1, which can exceed the R1CS
				// matrix dim; the key must cover it (Pedersen rounds
				// up to a power of two).
				let key_len = max_row_col.max(prep_param.F.get_cmf_len());
				if key_len > max_circ_pp_size{
					max_circ_pp_size = key_len;
				}
				(cs_pp, cs_vp) = CS1::setup(&mut rng, key_len)?;
				total_w_len += r1cs.A.n_cols -1 - r1cs.l;
				total_e_len += r1cs.A.n_rows;
				log(job_id, log_level, &format!("PERF 1002 circ {}, r1cs cols: {}, rows: {}", idx_j, r1cs.A.n_cols, r1cs.A.n_rows));

				elen.push(r1cs.A.n_rows);
				(cf_cs_pp, cf_cs_vp) = CS2::setup(&mut rng, cf_r1cs.A.n_rows)?;
				(cp_cs_pp, cp_cs_vp) = CS2::setup(&mut rng, cp_r1cs_in.A.n_rows)?;
			}

			let prover_params = ProverParamsFoldPot::<C1, C2, CS1, CS2, LK, H> {
				poseidon_config: prep_param.poseidon_config.clone(),
				cs_pp: Arc::new(cs_pp),
				cf_cs_pp: Arc::new(cf_cs_pp),
				cp_cs_pp: Arc::new(cp_cs_pp),
				size_F: prep_param.size_F,
				start_F: prep_param.start_F,
				lk_tbl: prep_param.lk_tbl.clone(),
				cs_pp_len: r1cs.A.n_cols, 
			};

			let verifier_params = VerifierParamsFoldPot::<C1, C2, CS1, CS2, H> {
				poseidon_config: prep_param.poseidon_config.clone(),
				r1cs: Arc::new(r1cs),
				cf_r1cs: Arc::new(cf_r1cs),
				cs_vp,
				cf_cs_vp,
				cp_cs_vp,
				//kzg_lk_col1: kzg_lk_col1.clone(),
				//kzg_lk_col2: kzg_lk_col2.clone(),
			};
			vec_pp.push(prover_params);
			vec_vp.push(verifier_params);
		}
		let m2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!("preprocess() Step 2: setup circ params. circs: {}, max_circ_pp: {}, total_w: {}, total_e: {}, increased RAM: {}. ", vec_pp.len(), max_circ_pp_size, total_w_len, total_e_len, mb2s(m2-m1)), &mut gt1);
		m1 = m2;

		let b_full_mode = prep_param_src.b_full_mode;
		let mut rng = rand::rngs::OsRng;

		//+1 for extra random blinding factor
		let new_total_cs_pp_len = total_w_len + total_e_len + 1;

		let Ok( (cs1e_pp,cs1e_vp) ) = CS1E::setup(&mut rng, new_total_cs_pp_len)
			else {panic!("cs1e setup failed");};
		if b_full_mode {assert!(n_circ==1);}
		let m2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!("preprocess() Step 3: cs1e_pp: {}, INCREASED RAM: {}. ", new_total_cs_pp_len, mb2s(m2-m1)), &mut gt1);
		m1 = m2;

		let (qa_pp, qa_vp, cols_len) = {
			//1. construct the full row
			//let ped_row = vec_pp.iter().map(|p| CS1::pkey_in_affine(&p.cs_pp))
			//	.flatten().collect::<Vec<C1::Affine>>();
			let vecx_1 = if b_full_mode {4} else {3};
			let mut ped_row= vec_pp.iter().map(|pp| { 
				//vecx_1 is x.len() + 1 (when fullmode x.len is 3 otherwise 2)
				let cs_pp_len = pp.cs_pp_len - vecx_1; //excluding 1 and vecx 
				CS1::pkey_in_affine(&pp.cs_pp, cs_pp_len)
			}).  flatten().collect::<Vec<C1::Affine>>();
			assert!(ped_row.len()==total_w_len);
			let mut ped_row2= vec_pp.iter().zip(elen.clone()).map(|(pp,ei)| { 
				CS1::pkey_in_affine(&pp.cs_pp, ei)
			}).  flatten().collect::<Vec<C1::Affine>>();
			ped_row.append(&mut ped_row2);	
			let kzg_row = CS1E::pkey_in_affine(&cs1e_pp, new_total_cs_pp_len);
			let lg = kzg_row[kzg_row.len()-1];
			ped_row.push(lg);
			assert!(ped_row.len()==kzg_row.len()); //because extra random

			//2. build the vec rows (W, E, F) for each subcircuit
			let mut vec_rows = vec![];
			vec_rows.push( (0, 0, kzg_row.len()) );
			let mut w_start = 0;
			let mut e_start = 0;
			for i in 0..n_circ{
				let pp = &vec_pp[i];
				let tuple_w = (w_start, w_start, pp.cs_pp_len-vecx_1);
				let tuple_e = (e_start + total_w_len, e_start + total_w_len, elen[i]);
				let tuple_f = (w_start + pp.start_F, w_start, pp.size_F); //THE REASON use
					//the same key sequence of comW only size is different!
				vec_rows.push(tuple_w);
				vec_rows.push(tuple_e);
				vec_rows.push(tuple_f);
				w_start += pp.cs_pp_len - vecx_1;
				e_start += elen[i];
			}
			let cols_len = kzg_row.len();
			let smatrix = SparseMatrix::<E::G1>{
				rows: 3*n_circ + 1,
				cols: kzg_row.len(),
				ped_row: ped_row, 
				kzg_row: kzg_row,
				vec_rows: vec_rows,
			};
			let b_debug = B_DEBUG;
			let (pkey, vkey) = setup_qa_nizk::<E>(&smatrix, b_debug);
			(Some(pkey), Some(vkey), cols_len)
		};
		let m2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!("preprocess() Step 4 qa_nizk: rows: {}, cols: {}, INCREASED RAM: {}. ", 3*n_circ+1, cols_len, mb2s(m2-m1)), &mut gt1);

		//5. build up the cp_r1cs if needed
		let cp_r1cs = if !b_full_mode{
			None
		}else{
			let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
			let cp_circuit= CyclePairCircuit::<E, P, C1, C2G2>::empty();
			cp_circuit.generate_constraints(cs2.clone())?;
			cs2.finalize();
			let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
			let cp_r1cs = extract_r1cs::<C1::BaseField>(&cs2);
			Some(cp_r1cs)
		};


		//println!("DEBUG USE 1709.1: cp_r1cs: {}", (&cp_r1cs).is_some());
		let prover_params = ProverParamsFoldPotSuper{vec_pp, qa_pp, cs1e_pp: Arc::new(cs1e_pp)};
		let verifier_params = VerifierParamsFoldPotSuper{
			vec_vp, cp_r1cs: cp_r1cs.map(Arc::new), qa_vp, cs1e_vp};
		let m2 = get_mem_usage_mb();
		log(0, log_level-1, &format!("- KEYS info: n_circs: {}, total_w: {}, total_e: {}, cs1e: {}, max_pp: {}, INCREASED RAM: {}, TOTAL RAM: {}.", n_circ, total_w_len, total_e_len, new_total_cs_pp_len, max_circ_pp_size, mb2s(m2-m0), mb2s(m2)) ); 

        Ok((prover_params, verifier_params))
    }

    /// Initializes the SuperNova+CycleFold's IVC for the 
	/// given parameters and initial state `z_0`.
	/// IMPORTANT NOTICE: z_0 and z_i actually consists of the FOLLOWING:
	/// (1) the hashchain of cmF from the previous stage.
	/// (2) the hash of z_0 or z_i_part2
	/// NOTE: for step 0, we will make an exception to pass the information
	/// of ALREADY computed FINAL hashchain of cmF (so that we can
	/// rebuild the z0_part2_inst using it. In this case `z_0[0]`
	/// will be the FINAL hashchain cmF (i.e., the r used for 
	/// z0_part2).  At this moment, because there is no step 1 information,
	/// zi_part2_inst is the same as z0_part2_inst
	/// NOTE2: difference from mod.rs (nova + cyclefold), the augmented
	/// circuit is different.
    fn init(
        _params: &(Self::ProverParam, Self::VerifierParam),
        _F: FC,
        _z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
		unimplemented!("call init_adv() instead!");
    }

    /// Implements IVC.P of SuperNova+CycleFold (note that
	/// there are a vectof of instances, but only one active instance
	/// is being folded)
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
        // Nova does not support multi-instances folding
        _other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
		let b_debug = B_DEBUG; // should be the same as
			//circuit_super.generate_constraints.b_debug!
			//as the CS is set up with no matrix mode when not b_debug
		let log_level = LOG4;
		let mut gt1 = GTimer::new();
		let mut gt2 = GTimer::new();

        //1.  ensure that commitments are blinding if user has specified so.
		// here we only sample one (as it's prover side self-check).
		let j_pci1 = field_to_usize(&self.pc_i1); //for compute z_i1
		let j_pci = field_to_usize(&self.pc_i); //for folding
        if H && self.i >= C1::ScalarField::one() {
            let blinding_commitments = if self.i == C1::ScalarField::one() {
                // blinding values of the running instances are zero at the first iteration
                vec![self.w_i.rW, self.w_i.rE]
            } else {
                vec![self.w_i.rW, self.w_i.rE, 
					self.W_i.vec_wit[j_pci].rW, self.W_i.vec_wit[j_pci].rE]
            };
            if blinding_commitments.contains(&C1::ScalarField::zero()) {
                return Err(Error::IncorrectBlinding(
                    H,
                    format!("{:?}", blinding_commitments),
                ));
            }
        }

        //2. build  `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();
        let augmented_F_circuit: AugmentedFCircuitFoldPotSuper<C1,C2,GC2,LK,FC,GM,H>;
        if _other_instances.is_some() {
            return Err(Error::NoMultiInstances);
        }

		//3. double check zi_len and external input lens
        if self.z_i.len() != self.F[j_pci1].state_len() {
            return Err(Error::NotSameLength(
                "z_i.len()".to_string(),
                self.z_i.len(),
                "F.state_len()".to_string(),
                self.F[j_pci1].state_len(),
            ));
        }
        if external_inputs.len() != self.F[j_pci1].external_inputs_len() {
            return Err(Error::NotSameLength(
                "F.external_inputs_len()".to_string(),
                self.F[j_pci1].external_inputs_len(),
                "external_inputs.len()".to_string(),
                external_inputs.len(),
            ));
        }
        if self.i > C1::ScalarField::from_le_bytes_mod_order(&usize::MAX.to_le_bytes()) {
            return Err(Error::MaxStep);
        }
        let mut i_bytes: [u8; 8] = [0; 8];
        i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..8]);
        let i_usize: usize = usize::from_le_bytes(i_bytes);

		//4. build `z_{i+1}`: z_i1_part2 is the part 2 instance of the `z_{i+1}`
		let usize_i= field_to_usize(&self.i);
		let pre_cmF = if self.vec_precomputed_group_cmF.is_some(){
			Some(self.vec_precomputed_group_cmF.as_ref().
				unwrap()[usize_i].clone())
		}else{
			None	
		};
        let (wtns, wtns_config, z_i1_part2) = self
            .F[j_pci1]
            .gen_witness(&external_inputs, &self.zi_part2_inst, pre_cmF);
		//ADDED: now rebuild z_i1 (`z_{i+1}`)
		let zi_part2 = self.zi_part2_inst.hash(&self.poseidon_config);
		assert!(self.z_i[1]==zi_part2, "z_i[1] != zi_part2");
		let cur_hc_cmF = self.z_i[0];
		let to_hash = vec![
			vec![cur_hc_cmF],
			wtns.cmF.clone(),
		].concat();
        let mut sponge_cmf = 
			PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
		sponge_cmf.absorb(&to_hash);
		let new_hc_cmF:C1::ScalarField=sponge_cmf.squeeze_field_elements(1)[0];
		let z_i1 = vec![new_hc_cmF, z_i1_part2.hash(&self.poseidon_config)];
		log_perf(self.job_id, log_level, &format!("prove_step: Step 1. gen_witness: stmt_len: {}, wtns size: {}", wtns.statement.len(), wtns_config.get_total_size()), &mut gt2);

        //5. compute cross terms T and cmT for AugmentedFCircuit (active at j)
        // r_bits is the r used to the RLC of the F' instances
        let (T, cmT) = self.compute_cmT(j_pci)?;
        let r_bits = ChallengeGadgetFoldPotSuper::<C1>::get_challenge_native(
            &mut transcript,
            self.pp_hash,
            self.U_i.clone(),
            self.u_i.clone(),
            cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        //5. fold SuperNova instances (on active circuit j)
		// note (w_i, u_i) is one instance but W_i and U_i are vectors
        let (W_i1_j, U_i1_j): 
			(WitnessFoldPot<C1>, CommittedInstanceFoldPot<C1>) =
            NIFSFoldPot::<C1, CS1, H>::fold_instances(
                r_Fr, &self.W_i.vec_wit[j_pci], &self.U_i.vec_inst[j_pci], 
				&self.w_i, &self.u_i, 
				&T, cmT,
            )?;

		let mut W_i1 = self.W_i.clone();
		let mut U_i1 = self.U_i.clone();
		W_i1.vec_wit[j_pci] = W_i1_j;
		U_i1.vec_inst[j_pci] = U_i1_j;
		//U_i1.pc_i the one used to compute u_i1 and fold U_i1 with u_i1
		U_i1.pc_i = self.pc_i1;	 
		//let global_U_i_x1 = self.U_i.x_1; 
		//let global_u_i_x1 = self.u_i.x[1].clone(); 
		//let global_U_i1_x1 = global_U_i_x1 + r_Fr * global_u_i_x1; 
		//U_i1.x_1 = global_U_i1_x1; //coz we only do one copy of Hash(cf_Ui)
		U_i1.x_1 = self.U_i.x_1 + r_Fr * self.u_i.x[1].clone();


		U_i1.x_2 = if !self.b_full_mode {None} else{
			Some(self.U_i.x_2.unwrap() + r_Fr * self.u_i.x[2])
		};
		log_perf(self.job_id, log_level, &format!("prove_step: Step 2. fold_inst. inst size: {}", self.W_i.vec_wit[j_pci].W.len()), &mut gt2);
			
        //6. folded instance output (public input, x) for generating
		// r1cs of the augmented F circuit.
		// Different from Nova, we add pc_i
        // u_{i+1}.x[0] = H(i+1, pc_i+1, z_0, z_{i+1}, U_{i+1})
        let u_i1_x = U_i1.hash(
            &sponge,
            self.pp_hash,
            self.i + C1::ScalarField::one(),
			self.pc_i1,
            self.z_0.clone(),
            z_i1.clone(),
        );


		let x_size = if self.b_full_mode {3} else {2};
		let mut u_dummy1 = CommittedInstanceFoldPotSuper::<C1>::
			dummy(x_size, field_to_usize(&self.n_circ), self.b_full_mode);
		u_dummy1.pc_i = self.pc_i1; //to match the U_i1

		//u_dummy1.pc_i = pc_i1; //to be consistent with u_dummy in circ_super.
        let u_i1_x_base = u_dummy1.hash(
            &sponge,
            self.pp_hash,
            C1::ScalarField::one(),
			self.pc_i1.clone(),
            self.z_0.clone(),
            z_i1.clone(),
        );
		let u_i1_x = if self.i.is_zero() {u_i1_x_base} else {u_i1_x};


        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;
		let _zero = C1::ScalarField::zero();
		let mut cp_u_i1_x: Option<C1::ScalarField> = None;

        if self.i == C1::ScalarField::zero() {
			cp_u_i1_x = if self.b_full_mode {Some(self.cp_U_i.as_ref().expect("cp_U_i null").hash_cyclefold(&sponge, self.pp_hash)) } else {None};
            cf_u_i1_x = self.cf_U_i.hash_cyclefold(&sponge, self.pp_hash);

            // base case
            augmented_F_circuit = AugmentedFCircuitFoldPotSuper
				::<C1, C2, GC2, LK, FC, GM, H> {
				_gm: PhantomData,
                _lk: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(C1::ScalarField::zero()), // = i=0
                i_usize: Some(0),
                z_0: Some(self.z_0.clone()), // = z_i
                z_i: Some(self.z_i.clone()),
				z0_part2_inst: Some(self.z0_part2_inst.clone()),
				zi_part2_inst: Some(self.zi_part2_inst.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW), // = dummy
                u_i_cmF: Some(self.u_i.cmF), // = dummy
                U_i: Some(self.U_i.clone()), // = dummy
                U_i1_cmE: Some(U_i1.vec_inst[j_pci].cmE),
                U_i1_cmW: Some(U_i1.vec_inst[j_pci].cmW),
                U_i1_cmF: Some(U_i1.vec_inst[j_pci].cmF),
                cmT: Some(cmT),
                F: self.F[j_pci1].clone(),
                x: Some(u_i1_x),
                cf1_u_i_cmW: None,
                cf2_u_i_cmW: None,
                cf3_u_i_cmW: None,
                cf_U_i: None, //fine -> it's essentially dummy in circuit_super
                cf1_cmT: None,
                cf2_cmT: None,
                cf3_cmT: None,
                cf_x: Some(cf_u_i1_x),

				cp_u_i_cmW: None, 
				cp_U_i: None, //-> it's essentially dummy in circuit_super
				cp_cm_T: None,
				cp_x: cp_u_i1_x, 
				b_full_mode: self.b_full_mode,

				n_circ: field_to_usize(&self.n_circ), 
				j: self.pc_i1.clone(), //this is the j for Fj(z0)-> z1
									//its value should be pc_i1
				precomputed_cmF: pre_cmF,
    			job_id: self.job_id,
        };

            if B_DEBUG { NIFSFoldPot::<C1, CS1, H>::verify_folded_instance(r_Fr, &self.U_i.vec_inst[j_pci], &self.u_i, &U_i1.vec_inst[j_pci], &cmT)?; }
        } else {
            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            // cyclefold circuit for cmW
            let cfW_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.vec_inst[j_pci].cmW),
                get_cm_coordinates(&self.u_i.cmW),
                get_cm_coordinates(&U_i1.vec_inst[j_pci].cmW),
            ]
            .concat();
            // cyclefold circuit for cmE
            let cfE_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.vec_inst[j_pci].cmE),
                get_cm_coordinates(&cmT),
                get_cm_coordinates(&U_i1.vec_inst[j_pci].cmE),
            ].concat();
            // cyclefold circuit for cmF
            let cfF_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.vec_inst[j_pci].cmF),
                get_cm_coordinates(&self.u_i.cmF),
                get_cm_coordinates(&U_i1.vec_inst[j_pci].cmF),
            ]
            .concat();

            let cfW_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.vec_inst[j_pci].clone().cmW, 
					self.u_i.clone().cmW]),
                x: Some(cfW_u_i_x.clone()),
        };
            let cfE_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.vec_inst[j_pci].clone().cmE, cmT]),
                x: Some(cfE_u_i_x.clone()),
        };
            let cfF_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.vec_inst[j_pci].clone().cmF, 
					self.u_i.clone().cmF]),
                x: Some(cfF_u_i_x.clone()),
        };

            // fold self.cf_U_i + cfW_U -> folded running with cfW
            let (_cfW_w_i, cfW_u_i, cfW_W_i1, cfW_U_i1, cfW_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                self.cf_W_i.clone(), // CycleFold running instance witness
                self.cf_U_i.clone(), // CycleFold running instance
                cfW_u_i_x,
                cfW_circuit,
                &mut rng,
            )?;


            // fold [the output from folding self.cf_U_i + cfW_U] + cfE_U = folded_running_with_cfW + cfE
            let (_cfE_w_i, cfE_u_i, cfE_W_i1, cfE_U_i1, cfE_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                cfW_W_i1,
                cfW_U_i1.clone(),
                cfE_u_i_x,
                cfE_circuit,
                &mut rng,
            )?;

			// siimilarly fold with cfF (added)
            let (_cfF_w_i, cfF_u_i, cfF_W_i1, cfF_U_i1, cfF_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                cfE_W_i1,
                cfE_U_i1.clone(),
                cfF_u_i_x.clone(),
                cfF_circuit,
                &mut rng,
            )?;

            cf_u_i1_x = cfF_U_i1.hash_cyclefold(&sponge, self.pp_hash);

			// fold the cyclepair
			// build the x input and then fold circuit
			let (cp_u_i_cmW, cp_U_i, cp_cm_T, cp_x, cp_W_i1, cp_U_i1, _cp_w_i, _cp_u_i) = 
			if self.b_full_mode{
				assert!(z_i1_part2.cyclepair_input.is_some());
				let cp_u_i_x: Vec<CF1<C1>> = z_i1_part2.cyclepair_input
					.as_ref().unwrap().x.to_vec();
				assert!(cp_u_i_x.len()==160);
				let _chunks = 32;
				let ratio = 5;
				let _chunk = cp_u_i_x[0..5].to_vec();
				let cp_u_i_x_fq = cp_u_i_x.chunks(ratio)
					.map(|chunk| 
						f1_limbs_to_f2::<CF1<C1>,CF3<C1>>(&chunk.to_vec()))
					.collect::<Vec<CF3<C1>>>();
            	let cp_circuit = CyclePairCircuit::<E, P, C1, C2G2>::
					from_vec_fq(&cp_u_i_x_fq);


            	let (cp_w_i, cp_u_i, cp_W_i1, cp_U_i1, cp_cmT, _) = 
					fold_cyclepair_circuit
						::<E,P,C1,GC1,C2G2,C2,GC2,FC,CS1,CS2,H>(
						&mut transcript,
						&*self.cp_r1cs,
						(*self.cp_cs_pp).clone(),
						self.pp_hash,
						self.cp_W_i.as_ref().clone().unwrap().clone(),
						self.cp_U_i.as_ref().clone().unwrap().clone(),
						cp_u_i_x_fq,
						cp_circuit, 
						&mut rng,
				).unwrap();
				cp_u_i1_x = Some(cp_U_i1.hash_cyclefold(&sponge, self.pp_hash));


				(Some(cp_u_i.cmW), Some(self.cp_U_i.as_ref().clone().unwrap().clone()), Some(cp_cmT), cp_u_i1_x, Some(cp_W_i1), Some(cp_U_i1), Some(cp_w_i), Some(cp_u_i))
			}else{ (None, None, None, None, None, None, None, None) };
			log_perf(self.job_id, log_level, &format!("prove_step: Step 3. fold cyclefold and cyclepair circuits."), &mut gt2);

            augmented_F_circuit = AugmentedFCircuitFoldPotSuper
			::<C1, C2, GC2, LK, FC, GM, H> {
				_gm: PhantomData,
                _lk: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(self.i),
                i_usize: Some(i_usize),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
				z0_part2_inst: Some(self.z0_part2_inst.clone()),
				zi_part2_inst: Some(self.zi_part2_inst.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW),
                u_i_cmF: Some(self.u_i.cmF),
                U_i: Some(self.U_i.clone()),
                U_i1_cmE: Some(U_i1.vec_inst[j_pci].cmE),
                U_i1_cmW: Some(U_i1.vec_inst[j_pci].cmW),
                U_i1_cmF: Some(U_i1.vec_inst[j_pci].cmF),
                cmT: Some(cmT),
                F: self.F[j_pci1].clone(), //should be j1. F_j1(z_i)->z_{i+1}
                x: Some(u_i1_x),
                // cyclefold values
                cf1_u_i_cmW: Some(cfW_u_i.cmW),
                cf2_u_i_cmW: Some(cfE_u_i.cmW),
                cf3_u_i_cmW: Some(cfF_u_i.cmW),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf1_cmT: Some(cfW_cmT),
                cf2_cmT: Some(cfE_cmT),
                cf3_cmT: Some(cfF_cmT),
                cf_x: Some(cf_u_i1_x),

				//cycle pair (either None or Some instance)
				cp_u_i_cmW: cp_u_i_cmW ,
				cp_U_i:  cp_U_i,
				cp_cm_T: cp_cm_T,
				cp_x: cp_x,
				b_full_mode: self.b_full_mode,

				n_circ: field_to_usize(&self.n_circ), 
				j: self.pc_i1.clone(), //this is the pc for Fj(zi) -> z_i1
				precomputed_cmF: pre_cmF,
    			job_id: self.job_id,
        };

            self.cf_W_i = cfF_W_i1;
            self.cf_U_i = cfF_U_i1;
			self.cp_W_i = cp_W_i1.clone();
			self.cp_U_i = cp_U_i1.clone();

            if B_DEBUG {
                self.cf_r1cs.check_instance_relation(&_cfW_w_i, &cfW_u_i)?;
                self.cf_r1cs.check_instance_relation(&_cfE_w_i, &cfE_u_i)?;
                self.cf_r1cs
                    .check_relaxed_instance_relation(&self.cf_W_i, &self.cf_U_i)?;
				if self.b_full_mode{
                	self.cp_r1cs.check_instance_relation(&_cp_w_i.as_ref().unwrap().clone(), &_cp_u_i.as_ref().unwrap().clone())?;
                	self.cp_r1cs.check_relaxed_instance_relation(&self.cp_W_i.as_ref().unwrap().clone(), &self.cp_U_i.as_ref().unwrap().clone())?;
				}
            }
        }

		//println!(">*>*>* prove_step step 1, augment circ: j: {}, pc_i: {}", &augmented_F_circuit.j, &self.pc_i);
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
		if !b_debug && !B_DEBUG2 && !B_DEBUG3{//NOTE: b_debug of mod_super:generate_constraints
			//should be set to the same as this function.
			//OTHERWISE, it will have issues with witness assignment in
			//debug mode
			//we only need the all variables generated
			//no need for r1cs A,B,C matrices construction
			cs.set_mode(SynthesisMode::Prove{construct_matrices:false});
		}
		let c1 = cs.num_constraints();
        augmented_F_circuit.generate_constraints(cs.clone())?;

		if b_debug{
        	assert!(cs.is_satisfied().unwrap());
		}
		let c2 = cs.num_constraints();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);

        if x_i1[0] != u_i1_x || x_i1[1] != cf_u_i1_x {
            return Err(Error::NotEqual);
        }
		if self.b_full_mode{
			if x_i1[2] !=cp_u_i1_x.unwrap(){
            	return Err(Error::NotEqual);
			}
		}

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){
				assert!(csat.unwrap(), "step final of modular_super"); 
			}
		}

		if b_debug{
			if self.b_full_mode{
				if x_i1.len() != 3 {
					return Err(Error::NotExpectedLength(x_i1.len(), 3));
				}
			}else{
				if x_i1.len() != 2 {
					return Err(Error::NotExpectedLength(x_i1.len(), 2));
				}
			}
		}
		log_perf(self.job_id, log_level, &format!("prove_step: Step 4. generate augmented F.cs: {}", c2-c1), &mut gt2);

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1;
		self.zi_part2_inst = z_i1_part2;
        self.w_i = WitnessFoldPot::<C1>::
			new::<H>(w_i1, self.r1cs[j_pci1].A.n_rows, &mut rng, 
			self.size_F[j_pci1], self.start_F[j_pci1]); //j1 is `pc_{i+1}`

        self.u_i = self.w_i.commit::<CS1, H>(&self.cs_pp[j_pci1], x_i1)?;
        self.W_i = W_i1;
        self.U_i = U_i1;
		self.pc_i = C1::ScalarField::from(j_pci1 as u32);

		if b_debug{
			self.r1cs[j_pci1].check_instance_relation(&self.w_i.clone().into(), &self.u_i.clone().into())?;

            self.r1cs[j_pci1]
                .check_relaxed_instance_relation(&self.W_i.vec_wit[j_pci1].clone().into(), &self.U_i.vec_inst[j_pci1].clone().into())?;
        }

		// ===== DEBUG USE 62727 BEGIN -- per-step step-circuit satisfiability probe (REMOVE LATER) =====
		// Arm with env ZKR_STEP_CHECK=1. Per step runs ONLY the cheap tight
		// check (62727.1): the fresh honest witness vs its strict step-R1CS.
		// On failure it also names the first-bad constraint ROW (-> gadget
		// region) then panics (early abort at the culprit step). The relaxed
		// running-instance check (62727.2) is redundant for this diagnosis (the
		// fold maintains it by construction; the decider is the real fold-
		// integrity check) so it is OFF unless ZKR_STEP_CHECK_RELAXED is set.
		if std::env::var("ZKR_STEP_CHECK").is_ok() {
			let step_i = field_to_usize(&self.i);
			if let Err(e) = self.r1cs[j_pci1].check_instance_relation(
				&self.w_i.clone().into(), &self.u_i.clone().into()) {
				let row = self.r1cs[j_pci1].first_bad_instance_row(
					&self.w_i.clone().into(), &self.u_i.clone().into())
					.map(|r| r as i64).unwrap_or(-1);
				emit_stdout(format!("DEBUG USE 62727.1: FRESH-UNSAT step={} circ={} first_bad_row={} n_cons={} :: {:?}", step_i, j_pci1, row, self.r1cs[j_pci1].A.n_rows, e));
				panic!("DEBUG USE 62727.1: step-circuit UNSAT at step={} circ={} first_bad_row={}", step_i, j_pci1, row);
			}
			if std::env::var("ZKR_STEP_CHECK_RELAXED").is_ok() {
				if let Err(e) = self.r1cs[j_pci1].check_relaxed_instance_relation(
					&self.W_i.vec_wit[j_pci1].clone().into(), &self.U_i.vec_inst[j_pci1].clone().into()) {
					emit_stdout(format!("DEBUG USE 62727.2: RELAXED-UNSAT step={} circ={} :: {:?}", step_i, j_pci1, e));
					panic!("DEBUG USE 62727.2: running relaxed instance UNSAT at step={} circ={}", step_i, j_pci1);
				}
			}
			emit_stdout(format!("DEBUG USE 62727.3: step={} circ={} OK", step_i, j_pci1));
		}
		// ===== DEBUG USE 62727 END =====
		log_perf(self.job_id, log_level, &format!("prove_step: Step 5. commit to instance: wit len: {}", self.w_i.W.len()), &mut gt2);
		log_perf(self.job_id, log_level-1, &format!("-- prove_step cost: i: {}, circ_id: {}, stmt_len: {}, wtns size: {}", self.i, j_pci1, wtns.statement.len(), wtns_config.get_total_size()), &mut gt1);

        Ok(())
    }

    fn state(&self) -> Vec<C1::ScalarField> {
        self.z_i.clone()
    }

    fn instances(
        &self,
    ) -> (
        Self::RunningInstance,
        Self::IncomingInstance,
        Self::CFInstance,
        Option<Self::CFInstance>,
    ) {
        (

            (self.U_i.clone(), self.W_i.clone()),
            (self.u_i.clone(), self.w_i.clone()),
            (self.cf_U_i.clone(), self.cf_W_i.clone()),
			if self.b_full_mode{
				let cp_U_i = self.cp_U_i.clone().unwrap().clone();
				let cp_W_i = self.cp_W_i.clone().unwrap().clone();
				Some( (cp_U_i, cp_W_i) )
			}else{
				None
			}
        )
    }

    /// Implements IVC.V of SuperNova+CycleFold. 
	/// Notice that this method does not include the
    /// commitments verification, which is done in the Decider.
    fn verify(
        vp: Self::VerifierParam,
        z_0: Vec<C1::ScalarField>, // initial state
        z_i: Vec<C1::ScalarField>, // last state
        num_steps: C1::ScalarField,
        running_instance: Self::RunningInstance,
        incoming_instance: Self::IncomingInstance,
        cyclefold_instance: Self::CFInstance,
        cyclepair_instance: Option<Self::CFInstance>, //similar type
    ) -> Result<(), Error> {
		//1. check steps and input lengths
		let j_pci = field_to_usize(&running_instance.0.pc_i);
		let poseidon_config = &vp.vec_vp[0].poseidon_config;
        let sponge = PoseidonSponge::<C1::ScalarField>::new(poseidon_config);
        if num_steps == C1::ScalarField::zero() {
            if z_0 != z_i { return Err(Error::IVCVerificationFail); }
            return Ok(());
        }

        let (U_i, W_i) = running_instance;
        let (u_i, w_i) = incoming_instance;
        let (cf_U_i, cf_W_i) = cyclefold_instance;
		let pc_i = U_i.pc_i;
		let u_i_x = u_i.x.clone();

		let b_full_mode = U_i.x_2.is_some(); //if yes, full mode
		let expected_x_len = if b_full_mode {3} else {2};
        if u_i.x.len() != expected_x_len || U_i.vec_inst[j_pci].x.len() != expected_x_len {
			emit_stdout(format!(
				"ERROR: u_ix or U_i.x.len()!=2 or 3 (bFull), \
				u_ix: {}, U_i.x: {}",
				u_i.x.len(), U_i.vec_inst[j_pci].x.len()));
            return Err(Error::IVCVerificationFail);
        }
        let pp_hash = vp.pp_hash()?;

        //1. check that u_i's output points to the running instance
        // u_i.X[0] == H(i, pc_i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&sponge, pp_hash, num_steps, 
			pc_i.clone(), z_0.clone(), z_i.clone());
        if expected_u_i_x != u_i.x[0] {
			emit_stdout(format!(
				"u_i.x[0] error, u_i.x[0]: {}, expected_u_i_x: {}, \
				U_i: {:?}\nz_0: {:?}\nz_i1:{:?}",
				u_i.x[0], expected_u_i_x, U_i, z_0, z_i));
            return Err(Error::IVCVerificationFail);
        }

        //2. u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&sponge, pp_hash);
        if expected_cf_u_i_x != u_i.x[1] {
			emit_stdout("u_i.X[1] check fails".to_string());
            return Err(Error::IVCVerificationFail);
        }

        //3.3.3. check u_i.cmE==0, u_i.u==1 (=u_i is a un-relaxed instance)
        if !u_i.cmE.is_zero() || !u_i.u.is_one() {
			emit_stdout("cmE error".to_string());
            return Err(Error::IVCVerificationFail);
        }

		//4. check pc.i in range
		let n_circ = U_i.vec_inst.len();
		assert!(j_pci<n_circ, "pc_i out of range");

        //5.  check R1CS satisfiability
        vp.vec_vp[j_pci].r1cs.check_instance_relation(&w_i.into(), &u_i.into())?;

        //6. SuperNOVA: each  check RelaxedR1CS satisfiability
		for i in 0..n_circ{
			//println!("DEBUG USE 505: check instance: {}", i);
        	vp.vec_vp[i].r1cs.check_relaxed_instance_relation(
				&W_i.vec_wit[i].clone().into(), 
				&U_i.vec_inst[i].clone().into())?;
		}

        //7.check CycleFold RelaxedR1CS satisfiability
		//NOTE: just one copy is ok (actually cf_r1cs) only needs one copy
        vp.vec_vp[0].cf_r1cs
            .check_relaxed_instance_relation(&cf_W_i, &cf_U_i)?;

		if cyclepair_instance.is_some(){
			//2.5 verify u_i.x[2] = H(cp_U_i)
        	let (cp_U_i, cp_W_i) = cyclepair_instance.unwrap();
			let expected_cp_u_i_x = cp_U_i.hash_cyclefold(&sponge, pp_hash);
			if expected_cp_u_i_x != u_i_x[2] {
				emit_stdout("u_i.x[2] check fails".to_string());
				return Err(Error::IVCVerificationFail);
			}
			//7.check CycleFold RelaxedR1CS satisfiability
			//NOTE: just one copy is ok (actually cp_r1cs) only needs one copy
			vp.cp_r1cs.expect("cp_r1cs null")
				.check_relaxed_instance_relation(&cp_W_i, &cp_U_i)?;
		}

		//println!("DEBUG USE 7021 - verify step 10. DONE!!!");

        Ok(())
    }
}
  
/// helper method to get the R1CS for both the 
/// AugmentedFCircuitSuper (note: different from Nova)
/// and the CycleFold circuit
#[allow(clippy::type_complexity)]
pub fn get_r1cs_super<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E, CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, FC, LK, GM, const H: bool>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC, n_circ: usize, j: usize
) -> Result<(R1CS<C1::ScalarField>, R1CS<C2::ScalarField>, R1CS<C2::ScalarField>), Error>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM, C=C1>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	LK: LookupTableTwoCol<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C2G2: CurveGroup,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
    let augmented_F_circuit =
        AugmentedFCircuitFoldPotSuper::<C1, C2, GC2, LK, FC, GM, H>::empty(poseidon_config, F_circuit,n_circ, j, 0);
    let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);
    let cp_circuit = CyclePairCircuit::<E,P,C1, C2G2>::empty();
    //let cp_circuit = CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);
    let r1cs = get_r1cs_from_cs::<C1::ScalarField>(augmented_F_circuit)?;
    let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;
    let cp_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cp_circuit)?;
    Ok((r1cs, cf_r1cs,cp_r1cs))
}

#[cfg(test)]
pub mod tests_mod_super {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective,
		G2Projective as ProjectiveG2, constraints::PairingVar as PairingVar};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::transcript::poseidon::poseidon_canonical_config;
	use crate::folding::foldpot::{
		sigma_ir1cs::{
			SigmaIR1CS_Inst,StatementInst,
			tests_sigma_ir1cs::{gen_six_root, SixRootMapper},
		},
	};

	type E = Bn254;
	type P = PairingVar;
	type C2G2 = ProjectiveG2;

    /// This test tests the Nova+CycleFold IVC, and by consequence it is also testing the
    /// AugmentedFCircuit
    #[test]
    fn test_ivc() {
		type GM = SixRootMapper<Fr,LookupTableTwoCol_Inst<Fr>>;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let num_steps: usize = 5;
		let (lk1, F_circuit, _vec_stmt) = gen_six_root::<Fr,Projective,Pedersen<Projective>,LookupTableTwoCol_Inst<Fr>,false>(5);
		let (lk3, F_circuit3, vec_stmt) = gen_six_root::<Fr,Projective,KZG<Bn254>, LookupTableTwoCol_Inst<Fr>, false>(5);
        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective>, Pedersen<Projective2>, LookupTableTwoCol_Inst<Fr>, GM, false>(
            poseidon_config.clone(),
			lk1,
            F_circuit.clone(),
			&vec_stmt,
			num_steps
        );

        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, KZG<Bn254>, Pedersen<Projective2>, LookupTableTwoCol_Inst<Fr>,GM, false>(
			poseidon_config, lk3, F_circuit3, &vec_stmt, num_steps);
    }

    // test_ivc allowing to choose the CommitmentSchemes
    fn test_ivc_opt<
        CS1E: CommitmentScheme<Projective, H>,
        CS1: CommitmentScheme<Projective, H>,
        CS2: CommitmentScheme<Projective2, H>,
		LK: LookupTableTwoCol<Fr> + 'static,
		GM: GadgetMapper<Fr,LK> + std::clone::Clone + Debug,
        const H: bool,
    >(
        poseidon_config: PoseidonConfig<Fr>,
		lkup_inp: Arc<LK>,
        F_circuit: SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>,
		vec_stmts: &Vec<StatementInst<Fr,LK>>,
		num_steps: usize,
    ) {
        let mut rng = ark_std::test_rng();
		let b_full_mode = false;

        let prep_param =
            PreprocessorParamFoldPotSuper::<Projective, Projective2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM, H>, CS1, CS2, LK, GM, H>
			::new(
				poseidon_config.clone(), 
				vec![F_circuit.clone()], 
				lkup_inp,
				vec![F_circuit.get_size_f()],
				b_full_mode
			);
        let nova_params = FoldPotSuper::<
			E,
			P,
			C2G2,
            Projective,
            GVar,
            Projective2,
            GVar2,
            SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>,
            CS1,
            CS2,
            CS1E,
			LK,
			GM,
            H,
        >::preprocess(&mut rng, &prep_param, 0)
        .unwrap();


		//PASS1. generate cm_F first
		let zero = Fr::zero();
		let (ch, rc) = (zero, zero);
		let b_full = F_circuit.is_full_mode();
		let fq_bits = <<Projective as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let n_words = 1;
		let z0_part2 = ZiPartTwoInst::<Fr>::new(zero, zero, &poseidon_config, b_full, fq_bits, n_words);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);
		let z_0 = vec![zero, z0_part2_hash];
		let n_circ = 1;
		let pc_0_val = 0;
		let _pc_0 = Fr::from(pc_0_val as u32);
		let b_full = false;
		let precomputed_cmF = None;
        let nova1 =
            FoldPotSuper::<E,P,C2G2, Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK, GM, H>, CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &nova_params,
                vec![F_circuit.clone()],
                z_0.clone(),
				n_circ, 
				pc_0_val,
				b_full,
				ch,
				rc,
				num_steps,
				precomputed_cmF,
				0
            )
            .unwrap();

		let mut hash_cmF= Fr::zero();
		for i in 0..num_steps{
			(hash_cmF,_) = nova1.compute_step_hc_cmF(hash_cmF, &vec_stmts[i])
				.expect("hash_cmf generation error");
		}
		let fq_bits = <<Projective as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let num_words = 1;
		let z0_part2 = ZiPartTwoInst::<Fr>::new(hash_cmF, rc, &poseidon_config, b_full, fq_bits, num_words);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);

		//2. PASS2 real IVC
		// NOTE: for step 0, the z_0[0] will be the FINAL hc_cmF,
		// for other steps, it will be hte hashchain of cmF from
		// the previous step
		println!("DEBUG USE 1000 ########################### START PASS 2\n\n\n");
        let z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
		let precomputed_cmF = None;
        let mut nova =
            FoldPotSuper::<E,P,C2G2, Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>, CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &nova_params,
                vec![F_circuit.clone()],
                z_0.clone(),
				n_circ,
				pc_0_val,
				b_full,
				ch,
				rc,
				num_steps,
				precomputed_cmF,
				0
            )
            .unwrap();

        for j in 0..num_steps {
			let v_stmt = vec_stmts[j].to_vec();
            nova.prove_step(&mut rng, v_stmt, None).expect("prove step error");
        }

        assert_eq!(Fr::from(num_steps as u32), nova.i);

        let (running_instance, incoming_instance, cyclefold_instance, cyclepair_instance) = nova.instances();
        FoldPotSuper::<E,P,C2G2, Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>, CS1, CS2, CS1E, LK, GM,H>::verify(
            nova_params.1, // Nova's verifier params
            z_0,
            nova.z_i,
            nova.i,
            running_instance,
            incoming_instance,
            cyclefold_instance,
			cyclepair_instance
        )
        .unwrap();
    }
}

