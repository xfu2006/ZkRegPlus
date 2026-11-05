use std::sync::{Arc, Mutex};
/// Implements the batch processing scheme.
/// Mainly this is about proving a word belongs to concatenation
/// of a collection of words. Check Section 6.5 of our paper.

/* Created 12/01/2024 */
use rand::RngCore;
use ark_ff::{PrimeField};
use ark_poly::Polynomial;
use crate::folding::circuits::{CF2};
use crate::folding::foldpot::container_config::ColEle;
use ark_relations::r1cs::ToConstraintField;
use ark_snark::{SNARK};
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{
	Group, CurveGroup,
	//AffineRepr, 
	pairing::{Pairing}
//	,PairingOutput},
	//VariableBaseMSM
};
use crate::Error;
use crate::commitment::{
	CommitmentScheme,
	kzg::{KZG, Proof as KZGProof},
	kzg
};
use rayon::prelude::*;
use utils::{
	timer::Timer,
	logger::{log, log_perf, emit_stdout, ERR, LOG1},
};
use core::marker::PhantomData;
use crate::folding::foldpot::{
	veccom::{VecCom},
	veccom,
	qa_nizk::{setup_qa_nizk_standard, Matrix, QaNizkProverParams,
		QaNizkVerifierParams, prove_qa_nizk_fast,
		QaNizkProof, verify_qa_nizk},
	sigma_ir1cs::{LookupTableTwoCol},
	decider_eth_circuit_super::{CircPubInput, kzg_ch, KZG_CH_TAG_S1, KZG_CH_TAG_S2},
	from_field::{AffineFromField},
	utils::{B_DEBUG,get_mem_usage_mb,mb2s},
};
use crate::transcript::AbsorbNonNative;
use crate::utils::vec::poly_from_vec;

/// T933 Hole A: verdict text of a VERIFY-FLAGS line. A failed check is
/// REJECT. A green proof from a run with the lookup check off
/// (b_check_lkup = false) is UNBOUND, never PASS, because it binds
/// neither the lookup table nor the words. Only the log text changes.
fn verdict_str(ok: bool, b_unbound: bool) -> &'static str {
	if !ok {"REJECT"} else if b_unbound {"UNBOUND"} else {"PASS"}
}

/// This structure contains the information which
/// generates the random challenge and folding rand
/// for evaluating the w, vec_len, vec_r, vec_v 
/// and for the random combination factor for batched kzg proof.
#[derive(Clone,Debug)]
pub struct SnarkRandInput<E: Pairing>{
	// First four elements from BatchClaim
	/// kzg of all words
	pub kzg_all_words: E::G1, 
	/// kzg of length of each words
	pub kzg_length: E::G1,
	/// kzg of lookup column1
	pub kzg_lk_col1: E::G1,
	/// kzg of lookup column2
	pub kzg_lk_col2: E::G1,

	/// hash chain of cmF
	pub hash_cmF: E::ScalarField,	
	/// kzg of the vec_r
	pub kzg_vec_r: E::G1,
	/// kzg of the vec_v
	pub kzg_vec_v: E::G1,
	/// poseidon config
	pub poseidon_config: PoseidonConfig<E::ScalarField>
}

impl <E:Pairing> SnarkRandInput<E> where
<E as Pairing>::ScalarField: Absorb{
	/// generate the random challenge ch and the random combination factor rc
	pub fn gen_challenge(&self) -> (E::ScalarField, E::ScalarField){
		let mut sponge= PoseidonSponge::<E::ScalarField>
			::new(&self.poseidon_config);
		let mut arr_fe:Vec<E::ScalarField> = vec![];
		let coms = vec![self.kzg_all_words.clone(), self.kzg_length.clone(),
			self.kzg_lk_col1.clone(), self.kzg_lk_col2.clone(),
			self.kzg_vec_r.clone(), self.kzg_vec_v.clone()];
		for com in coms{
			com.to_native_sponge_field_elements_as_vec()
				.to_sponge_field_elements(&mut arr_fe);
		}
		arr_fe.push(self.hash_cmF.clone());
		sponge.absorb(&arr_fe);
		let vec: Vec<E::ScalarField> = sponge.squeeze_field_elements(2);
		(vec[0], vec[1])
	}
}


/// The batch processor. Treat it as a collection of functions..
/// CS1E is actually KZG, but to be compative with driver
pub struct BatchProcessor<E:Pairing, LK: LookupTableTwoCol<E::ScalarField>,
	S: SNARK<E::ScalarField>, CS1E, const H: bool>
where
    CS1E: CommitmentScheme<
        E::G1, H,
        ProverChallenge = E::ScalarField,
        Challenge = E::ScalarField,
        Proof = KZGProof<E::G1>,
    >,
{
	_e: PhantomData<E>,
	_lk: PhantomData<LK>,
	_s: PhantomData<S>,
	_c: PhantomData<CS1E>,
}

/// T934: commit-and-prove SNARK. D = MSM(d_query, a_S) + kappa [delta]_1
/// commits the committed wires a_S under its own pairing base (Mirage).
pub trait CpSnark<E: Pairing>: SNARK<E::ScalarField> {
	fn cp_commit(pk: &Self::ProvingKey, a_s: &[E::ScalarField], kappa: E::ScalarField) -> E::G1;
	fn prove_cp<C: ark_relations::r1cs::ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
		pk: &Self::ProvingKey, circ: C, kappa: E::ScalarField, d_pre: Option<E::G1>, rng: &mut R)
		-> Result<Self::Proof, Self::Error>;
	fn commitment(prf: &Self::Proof) -> E::G1;
}

impl<E: Pairing> CpSnark<E> for ark_groth16::Groth16<E> {
	fn cp_commit(pk: &Self::ProvingKey, a_s: &[E::ScalarField], kappa: E::ScalarField) -> E::G1 {
		ark_groth16::Groth16::<E>::cp_commit(pk, a_s, kappa)
	}
	fn prove_cp<C: ark_relations::r1cs::ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
		pk: &Self::ProvingKey, circ: C, kappa: E::ScalarField, d_pre: Option<E::G1>, rng: &mut R)
		-> Result<Self::Proof, Self::Error> {
		use ark_std::{UniformRand, Zero};
		assert!(pk.n_commit == 0 || !kappa.is_zero(), "T934: kappa = 0");
		let (r, s) = (E::ScalarField::rand(rng), E::ScalarField::rand(rng));
		Self::create_proof_with_reduction(circ, pk, r, s, kappa, d_pre)
	}
	fn commitment(prf: &Self::Proof) -> E::G1 { prf.d.into() }
}

/// prover key
#[derive(Clone,Debug)]
pub struct BatchProcessorProverParams<'a, E:Pairing>{
	/// used for kzg_all_words 
	pub kzg: <KZG::<'a, E> as CommitmentScheme<E::G1>>::ProverParams,
	/// vector commitment params
	pub vec: <VecCom::<'a,E> as CommitmentScheme<E::G1>>::ProverParams,
	/// Poseidon config
	pub poseidon_config: PoseidonConfig<E::ScalarField>,
	/// qa_nizk 
	pub pk_qa_nizk: QaNizkProverParams<E>,
	/// T933 s10. KZG commitments to the two lookup columns, made once
	/// by setup from the public table. gen_claims copies them.
	pub lk_cm1: E::G1,
	/// see lk_cm1
	pub lk_cm2: E::G1,
}

/// verifier key
#[derive(Clone,Debug)]
pub struct BatchProcessorVerifierParams<'a, E:Pairing, CS1E, const H: bool>
where CS1E: CommitmentScheme<
        E::G1, H,
        ProverChallenge = E::ScalarField,
        Challenge = E::ScalarField,
        Proof = KZGProof<E::G1>,
    >,
{
	/// used for kzg_all_words
	pub kzg: <KZG::<'a, E> as CommitmentScheme<E::G1>>::VerifierParams,
	/// used for vector commitment
	pub vec: <VecCom::<'a,E> as CommitmentScheme<E::G1>>::VerifierParams,
	/// same Poseidon config as parameter params
	pub poseidon_config: PoseidonConfig<E::ScalarField>,
	/// verifier key of qa_nizk (for 1st qa_nizk proof) [not the 2nd phase]
	pub vk_qa_nizk: QaNizkVerifierParams<E>,
	/// the hash of the verifier key
	pub qa_nizk_vkey_hash: E::ScalarField,
	/// kzg verifier param of dirver 1, set up later when driver 1 is available
	/// This is actually KZG param, for syntax wise to be compatible with driver
	pub kzg_driver1: Option<CS1E::VerifierParams>,
	/// for driver 2
	pub kzg_driver2: Option<CS1E::VerifierParams>,
	/// entry count the veccom eval domain was built for (= n_words+2,
	/// the same value passed to VecCom::setup; T933 s9 B2: two blind
	/// slots n_words, n_words+1). Needed to recompute omega^i for the
	/// position opening in verify_individual.
	pub vec_dom_size: usize,
	/// T933 s10 (paper Fig 13 (ii)). The trusted lookup-column
	/// commitments, the same pair as the prover key. verify_batch
	/// requires the claim's kzg_lk_col1/2 to equal them.
	pub lk_cm1: E::G1,
	/// see lk_cm1
	pub lk_cm2: E::G1,
}

impl<'a, E:Pairing, CS1E, const H: bool> BatchProcessorVerifierParams<'a, E, CS1E, H>
where CS1E: CommitmentScheme<
        E::G1, H,
        ProverChallenge = E::ScalarField,
        Challenge = E::ScalarField,
        Proof = KZGProof<E::G1>,
    >,
{
	/// T933: word count the key was built for (two blind slots follow).
	pub fn n_words(&self) -> usize { self.vec_dom_size.saturating_sub(2) }
}


/// The claim: kzg_all_words commits to the concatenation of all words.
/// Since T932-F2W each word in it is followed by its blind (two
/// blinds since T933 s9).
/// then the length array decides the words. (1) the total sum of the
/// lengths match the length of combined words. (2) each word
/// is malware free (regarding the regex signatures).
///
/// Note1: it is very likely in practice that the 
/// combined word CONTAINS instances
/// of malware, but none of the individual word does. That's the reason
/// we do the dinvidual proof. 
/// Note2: KZG commitment and vcom_commitment is 1-leaky. It's accomplished
/// by padding a random, just like halo2(plonk) and Lunar. T933 s9: two
/// randoms, so a commitment and one published evaluation stay
/// jointly uniform. 
/// Note that all KZG are actually commitment to the REVERSE of vectors.
/// but VecCom are normal order.
#[derive(Clone,Debug)]
pub struct BatchClaim<E:Pairing>{
	/// KZG commitment to combined words
	pub kzg_all_words: E::G1,
	/// vector commitment to vector of length
	pub kzg_length: E::G1,
	/// kzg of lkup col1
	pub kzg_lk_col1: E::G1,
	/// kzg of lkup col2
	pub kzg_lk_col2: E::G1,
}

/// The individual claim that the word hiding behind kzg_word
/// is the i'th word of the combined word in the batch claim
#[derive(Clone,Debug)]
pub struct IndividualClaim<E:Pairing>{
	/// index of word (starting from 0)
	pub i: usize,
	/// KZG commitment of i'th word (1-leaky)
	pub kzg_word: E::G1,
	/// reference to the BatchClaim 
	pub ref_batch_claim: Arc<Mutex<BatchClaim<E>>>,
}
#[derive(Clone,Debug)]
/// prove the invidual claim that kzg_word is the i'th word
/// of the kzg_word given the kzg_length
pub struct IndividualProof<E:Pairing>{
	/// Combined proof of vcom_ri and vcom_vi
	pub vcom_prf:  veccom::Proof<E::G1>,
	/// v_i (the eval of w_i over r_i)
	pub v_i: E::ScalarField,
	/// KZG proof that kzg_word evaluates to v_i at r_i
	pub kzg_prf: kzg::Proof<E::G1>,
}

#[derive(Clone,Debug)]
/// Global Proof: which proves the BatchClaim <kzg_all_words, kzg_length>
/// that all words defined by the above are ``malware free".
/// Total: 20G1 + 2G2 + 7F
pub struct BatchProof<E:Pairing, S: SNARK<E::ScalarField>>{
	/// the vector commitment to vec_v
	pub vcom_vec_v: E::G1,
	/// the kzg commitment to vec_v
	pub kzg_vec_v: E::G1,
	/// the vector commitment to vec_r
	pub vcom_vec_r: E::G1,
	/// the kzg commitment to vec_r
	pub kzg_vec_r: E::G1,
	/// qa_nizk_proof for equiv between kzg_vec_r and vecom_vec_r
	/// and kzg_vec_v and vcom_vec_v
	pub prf_qa_nizk: QaNizkProof<E>, 
	/// challenge for KZG eval
	pub ch: E::ScalarField,
	/// random combination factor for combining polynomials
	pub rc: E::ScalarField,
	/// kzg proof of kzg_all_words, kzg_length, kzg_vec_r, kzg_vec_v
	/// aggregately evaluates to a point at ch to a certain value
	/// it has two elements, eval and kzg proof
	pub agg_kzg_prf: kzg::Proof<E::G1>,

	// the following are part 2 (added after the phase2 proof is
	// completed, and the snark proof is generated

	/// kzg of all w and e for circ1
	pub kzg_all_com1: Option<E::G1>,
	/// proof kzg_all_com1
	/// the corresponding proof (it contains eval_w_e1)
	pub kzg_all_com_prf1: Option<kzg::Proof<E::G1>>,

	/// kzg of all w and e for circ2
	pub kzg_all_com2: Option<E::G1>,
	/// the corresponding proof (note it consists of the eval)
	pub kzg_all_com_prf2: Option<kzg::Proof<E::G1>>,

	/// the comE of U_{i+1} of circ2
	pub comE2: Option<E::G1>,
	/// the comW of U_{i+1} of circ2
	pub comW2: Option<E::G1>,
	/// the comF of U_{i+1} of circ2
	pub comF2: Option<E::G1>,
	/// the QA_nizk for kzg_all_com2 and comE2, comW2, comF2
	pub qa_nizk_prf2: Option<QaNizkProof<E>>,

	/// the snark proof for the Main circ
	pub snark_proof_main: Option<S::Proof>,
	/// the snark proof for the Cyclepair circ
	pub snark_proof_cp: Option<S::Proof>,
	/// the hash of the mainres from te Main circ
	pub mainres_hash: Option<E::ScalarField>,

	/// hash chain of cmF
	pub hash_cmF: E::ScalarField,	
}

impl <E:Pairing, S: SNARK<E::ScalarField>> BatchProof<E,S>{
	pub fn add_part2(&mut self, 
		kzg_all_com1: E::G1,
		kzg_all_com_prf1: kzg::Proof<E::G1>,

		kzg_all_com2: E::G1,
		kzg_all_com_prf2: kzg::Proof<E::G1>,

		comE2: E::G1,
		comW2: E::G1,
		comF2: E::G1,
		qa_nizk_prf2: QaNizkProof<E>,

		snark_proof_main: S::Proof,
		snark_proof_cp: S::Proof,
		mainres_hash: E::ScalarField
	){
		self.kzg_all_com1 = Some(kzg_all_com1);
		self.kzg_all_com_prf1 = Some(kzg_all_com_prf1);

		self.kzg_all_com2 = Some(kzg_all_com2);
		self.kzg_all_com_prf2 = Some(kzg_all_com_prf2);

		self.comE2 = Some(comE2);
		self.comW2 = Some(comW2);
		self.comF2 = Some(comF2);

		self.qa_nizk_prf2 = Some(qa_nizk_prf2);
		self.snark_proof_main = Some(snark_proof_main);
		self.snark_proof_cp = Some(snark_proof_cp);
		self.mainres_hash= Some(mainres_hash);


	}
}

use ark_serialize::{CanonicalSerialize, Compress};

/// Running tally of proof elements + their compressed byte size.
/// G1/G2 are group elements, Fr is a scalar field element.
struct SizeAcc{ n_g1: usize, n_g2: usize, n_fr: usize, bytes: usize }
impl SizeAcc{
	fn new() -> Self{ Self{n_g1:0, n_g2:0, n_fr:0, bytes:0} }
	/// one G1 group element
	fn g1<C: CanonicalSerialize>(&mut self, name: &str, e: &C){
		let b = e.serialized_size(Compress::Yes);
		self.n_g1 += 1; self.bytes += b;
		emit_stdout(format!("  {:<22}: 1 G1             : {:>5} B", name, b));
	}
	/// one Fr scalar element
	fn fr<C: CanonicalSerialize>(&mut self, name: &str, e: &C){
		let b = e.serialized_size(Compress::Yes);
		self.n_fr += 1; self.bytes += b;
		emit_stdout(format!("  {:<22}: 1 Fr             : {:>5} B", name, b));
	}
	/// a kzg/veccom Proof = 1 Fr (eval) + 1 G1 (proof)
	fn kzg_like<F: CanonicalSerialize, G: CanonicalSerialize>(
		&mut self, name: &str, eval: &F, proof: &G){
		let be = eval.serialized_size(Compress::Yes);
		let bp = proof.serialized_size(Compress::Yes);
		self.n_fr += 1; self.n_g1 += 1; self.bytes += be + bp;
		emit_stdout(format!(
			"  {:<22}: 1 Fr + 1 G1      : {:>5} B", name, be+bp));
	}
}

impl<E: Pairing> IndividualProof<E>{
	/// Print each field's element kinds + compressed bytes, then the
	/// element totals; return the total byte size.
	pub fn print_size(&self) -> usize{
		emit_stdout("==== IndividualProof ====".to_string());
		let mut a = SizeAcc::new();
		a.kzg_like("vcom_prf", &self.vcom_prf.eval, &self.vcom_prf.proof);
		a.fr("v_i", &self.v_i);
		a.kzg_like("kzg_prf", &self.kzg_prf.eval, &self.kzg_prf.proof);
		emit_stdout(format!(
			"  ---- elements: {} G1, {} G2, {} Fr | TOTAL {} bytes",
			a.n_g1, a.n_g2, a.n_fr, a.bytes));
		a.bytes
	}
}

impl<E: Pairing, S: SNARK<E::ScalarField>> BatchProof<E, S>
	where S::Proof: CanonicalSerialize{
	/// Print each field's element kinds + compressed bytes, then the
	/// element totals; return the total byte size. Option (part-2)
	/// fields print Some/None and count only when present. Each Groth16
	/// S::Proof is a known shape (3 G1 + 1 G2 with T934's D): its bytes
	/// come from serialized_size (exact for any S) and 3 G1 + 1 G2 fold
	/// into the element tally.
	pub fn print_size(&self) -> usize{
		emit_stdout("==== BatchProof ====".to_string());
		let mut a = SizeAcc::new();
		a.g1("vcom_vec_v", &self.vcom_vec_v);
		a.g1("kzg_vec_v",  &self.kzg_vec_v);
		a.g1("vcom_vec_r", &self.vcom_vec_r);
		a.g1("kzg_vec_r",  &self.kzg_vec_r);
		a.g1("prf_qa_nizk.prf", &self.prf_qa_nizk.prf);
		a.fr("ch", &self.ch);
		a.fr("rc", &self.rc);
		a.kzg_like("agg_kzg_prf",
			&self.agg_kzg_prf.eval, &self.agg_kzg_prf.proof);
		// part 2 (Option) -- present-aware
		match &self.kzg_all_com1{ Some(x)=>a.g1("kzg_all_com1", x),
			None=>emit_stdout("  kzg_all_com1          : None".to_string()) }
		match &self.kzg_all_com_prf1{
			Some(p)=>a.kzg_like("kzg_all_com_prf1", &p.eval, &p.proof),
			None=>emit_stdout("  kzg_all_com_prf1      : None".to_string()) }
		match &self.kzg_all_com2{ Some(x)=>a.g1("kzg_all_com2", x),
			None=>emit_stdout("  kzg_all_com2          : None".to_string()) }
		match &self.kzg_all_com_prf2{
			Some(p)=>a.kzg_like("kzg_all_com_prf2", &p.eval, &p.proof),
			None=>emit_stdout("  kzg_all_com_prf2      : None".to_string()) }
		match &self.comE2{ Some(x)=>a.g1("comE2", x),
			None=>emit_stdout("  comE2                 : None".to_string()) }
		match &self.comW2{ Some(x)=>a.g1("comW2", x),
			None=>emit_stdout("  comW2                 : None".to_string()) }
		match &self.comF2{ Some(x)=>a.g1("comF2", x),
			None=>emit_stdout("  comF2                 : None".to_string()) }
		match &self.qa_nizk_prf2{ Some(p)=>a.g1("qa_nizk_prf2.prf", &p.prf),
			None=>emit_stdout("  qa_nizk_prf2          : None".to_string()) }
		// Groth16 proofs: bytes via serialized_size, 3 G1 + 1 G2 each
		for (name, sp) in [("snark_proof_main", &self.snark_proof_main),
			("snark_proof_cp", &self.snark_proof_cp)]{
			match sp{
				Some(p)=>{
					let b = p.serialized_size(Compress::Yes);
					a.n_g1 += 3; a.n_g2 += 1; a.bytes += b;
					emit_stdout(format!(
						"  {:<22}: Groth16 3 G1+1 G2: {:>5} B", name, b));
				},
				None=>emit_stdout(format!("  {:<22}: None", name)),
			}
		}
		match &self.mainres_hash{ Some(x)=>a.fr("mainres_hash", x),
			None=>emit_stdout("  mainres_hash          : None".to_string()) }
		a.fr("hash_cmF", &self.hash_cmF);
		emit_stdout(format!(
			"  ---- elements: {} G1, {} G2, {} Fr | TOTAL {} bytes",
			a.n_g1, a.n_g2, a.n_fr, a.bytes));
		a.bytes
	}
}

/// The (secret) advice input for the SNARK System.
/// vec_r contains r_i for i'th individual proof.
/// the commitment to vec_r will be 1-leaky, and similar is vec_v.
/// The i'th word evaluates to v_i at r_i.
/// words and rands are the same as those in BatchProcessor struct.
#[derive(Clone)]
pub struct SnarkAdvice<F:PrimeField>{
	// the words
	//pub words: Vec<Vec<F>>,
	/// the rands (to be padded to each word)
	pub rands: Vec<F>,
	/// T933 s9 B1. The second per-word blinds o_i2, padded after
	/// rands[i]. The pair makes (C_i, v_i) jointly uniform.
	pub rands2: Vec<F>,
	/// the nonce for kzg_all_words
	pub r_all_words: F,
	/// T933 s9 B2. Second nonce for kzg_all_words.
	pub r_all_words2: F,
	/// the nonce for kzg_len
	pub r_kzg_len: F,
	/// T933 s9 B2. Second nonce for kzg_len.
	pub r_kzg_len2: F,
	/// nonce hiding vec_r, shared by the vec_com and the kzg commit:
	/// the qa_nizk proves both from ONE witness vector, so a split
	/// nonce would make that proof unsatisfiable.
	pub r_vec_r: F,
	/// nonce hiding vec_v; shared by vec_com and kzg as for r_vec_r.
	pub r_vec_v: F,
	/// T933 s9 B2. Second nonce of vec_r (slot n_words+1).
	pub r_vec_r2: F,
	/// T933 s9 B2. Second nonce of vec_v (slot n_words+1).
	pub r_vec_v2: F,
	/// the vec of v_i
	pub vec_v: Vec<F>,
	/// the vec of r_i
	pub vec_r: Vec<F>,
}

impl <F:PrimeField> SnarkAdvice<F>{
	/// dummy function just kee the length of words (no use)
	pub fn empty(words: &Vec<Vec<F>>)->Self{
		let vf = vec![F::zero(); words.len()];
		let zero = F::zero();
		Self{
			rands: vf.clone(),
			rands2: vf.clone(),
			r_all_words: zero,
			r_all_words2: zero,
			r_kzg_len: zero,
			r_kzg_len2: zero,
			r_vec_r: zero,
			r_vec_v: zero,
			r_vec_r2: zero,
			r_vec_v2: zero,
			vec_v: vf.clone(),
			vec_r: vf.clone()
		}
	}
}

impl <'a, 
	E:Pairing<G1=C1,ScalarField=F>, 
	C1:CurveGroup<ScalarField=F> + ToConstraintField<CF2<C1>>, 
	F:PrimeField + Absorb + ColEle, 
	LK: LookupTableTwoCol<E::ScalarField>, 
	S: CpSnark<E>,
	CS1E,
	const H: bool> 
BatchProcessor <E,LK,S,CS1E,H> 
where
    CS1E: CommitmentScheme<
        E::G1, H,
        ProverChallenge = E::ScalarField,
        Challenge = E::ScalarField,
        Proof = KZGProof<E::G1>>,
	C1: ToConstraintField<CF2<C1>>, 
	<C1 as Group>::ScalarField: PrimeField + Absorb,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<E as Pairing>::TargetField: ToConstraintField<CF2<C1>>,
	<E as Pairing>::G2: ToConstraintField<CF2<C1>>,
	<E as Pairing>::ScalarField: PrimeField + Absorb,
	C1::Affine: AffineFromField<CF2<C1>>,
{

	/// constructor
	pub fn new() -> Self{ 
		Self{_e: PhantomData,_lk: PhantomData,_s: PhantomData,_c: PhantomData} 
	}

	/// return the max key size needed for kzg commitment
	pub fn key_size(words: &Vec<Vec<F>>) -> usize{
		let n = words.iter().map(|w| w.len()).sum::<usize>();
		//T932-F2W, T933 s9 B1. kzg_all_words holds every word
		//followed by its two blinds, so n + 2*words.len() entries.
		//Its own two blinds are covered by the +2 in setup.
		n + 2*words.len()
	}

	/// T933 s10. The two lookup-column commitments: the columns of
	/// `lkup.get_cols()` reversed, blind zero. Only setup calls it, so
	/// the claim and the verifier key hold the same pair.
	fn commit_lkup_cols(
		kzg: &<KZG::<'a, E> as CommitmentScheme<E::G1>>::ProverParams,
		lkup: &LK) -> Result<(E::G1, E::G1), Error>{
		let zero = F::zero();
		let (mut lk1, mut lk2) = lkup.get_cols();
		lk1.reverse();
		lk2.reverse();
		Ok((KZG::<E>::commit(kzg, &lk1, &zero)?,
			KZG::<E>::commit(kzg, &lk2, &zero)?))
	}

	/// set up the prover and verifier params
	/// max_total_n should be greater than the combined length of all words
	/// plus 2*n_words (T932-F2W, T933 s9: two blinds per word in
	/// kzg_all_words), and the lookup table size
	/// `job_id`: The ID of the job being processed.
	/// `lkup`: the public lookup table. Both keys get its commitments.
	pub fn setup(mut rng: impl RngCore, max_total_n: usize, n_words: usize,
		poseidon_config: PoseidonConfig<F>, job_id: usize, lkup: &LK)
	-> (BatchProcessorProverParams<'a, E>, BatchProcessorVerifierParams<'a,E,CS1E,H>){
		let b_debug = B_DEBUG;
		let logl = LOG1;
		let mut gt = Timer::new();
		let mut gt2 = Timer::new();
		let mut m1 = get_mem_usage_mb();
		let m0 = m1;
		log_perf(job_id, logl, &format!("BatchProcessor step 1. BEFOFORE setting up kzg: {}, RAM NOW: {}", max_total_n, mb2s(get_mem_usage_mb())), &mut gt);
		m1 = get_mem_usage_mb();
	
		let kzg =  KZG::<E>::setup(&mut rng, max_total_n+2)
			.expect("kzg key fail");
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 2. setting up kzg: {}, INCREASED RAM now: {}. ", max_total_n, mb2s(m2.saturating_sub(m1))), &mut gt);
		m1 = m2;

		//T933 s9 B2. n_words entries plus two blind slots.
		let kzg_frag = KZG::<E>::pkey_in_affine(&kzg.0, n_words+2);
		//lg is for random blinding factor
		let lg= KZG::<E>::pkey_in_affine(&kzg.0, n_words+3)[n_words+2];

		let vec = VecCom::<E>::setup(&mut rng, n_words + 2).expect("vec setup fails"); 
		let mut vec_frag = VecCom::<E>::pkey_in_affine(&vec.0, n_words+2);
		vec_frag.reverse(); //because it's order is the REVERSE
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 3. setting up veccom: {}, INCREASED RAM: {} ", n_words, mb2s(m2.saturating_sub(m1))), &mut gt);
		m1 = m2;

		//of the vector which generates kzg
		let vz = vec![ E::G1::zero().into_affine(); n_words + 2];
		//w will be [vec_r || vec_v]
		let matrix = vec![
			vec![kzg_frag.clone(), vz.clone(),vec![lg]].concat(), //-> kzg_vec_r
			vec![vec_frag.clone(), vz.clone(),vec![lg]].concat(), //-> vecom_vec_r 
			vec![vz.clone(), kzg_frag.clone(),vec![lg]].concat(), // -> kzg_vec_v 
			vec![vz.clone(), vec_frag.clone(),vec![lg]].concat(), // -> vecom_vec_v
		];
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 4. setting up matrix: {}, INCREASED RAM now: {}", (&matrix[0]).len(), mb2s(m2.saturating_sub(m1))), &mut gt);
		m1 = m2;
		let mat = Matrix::<E::G1>{rows: matrix.len(), cols: matrix[0].len(), 
			matrix};
		let (pkey_qanizk, vkey_qanizk) = setup_qa_nizk_standard::<E>(&mat, b_debug);
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 5. setting up qa_nizk, INCREASED RAM: {}. ", mb2s(m2.saturating_sub(m1))), &mut gt);

		//T933 s10. Commit the public table once (2 MSMs of its size).
		let (lk_cm1, lk_cm2) = Self::commit_lkup_cols(&kzg.0, lkup)
			.expect("lkup commit fail (table larger than the kzg key?)");
		log_perf(job_id, logl, &format!("BatchProcessor step 5b. commit lkup cols: {} rows", lkup.get_size()), &mut gt);

		let pkey = BatchProcessorProverParams::<'a, E>{
			kzg: kzg.0, vec: vec.0, 
			poseidon_config: poseidon_config.clone(),
			pk_qa_nizk: pkey_qanizk,
			lk_cm1, lk_cm2,
		};

	
		let qa_nizk_vkey_hash = vkey_qanizk.hash(&poseidon_config);
		let vkey = BatchProcessorVerifierParams::<'a, E,CS1E,H>{
			kzg: kzg.1, vec: vec.1, poseidon_config,
			vk_qa_nizk: vkey_qanizk,
			kzg_driver1: None,
			kzg_driver2: None,
			qa_nizk_vkey_hash: qa_nizk_vkey_hash,
			//same length handed to VecCom::setup just above; setup
			//rounds it to a power of two internally.
			vec_dom_size: n_words + 2,
			lk_cm1, lk_cm2,
		};
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 5. setting up qa_nizk, INCREASED RAM: {}, TOTAL RAM now: {}. ", mb2s(m2.saturating_sub(m0)), mb2s(m2)), &mut gt2);
		(pkey, vkey)
	}

	/// return the batch claim, vector of individual claims,
	/// and the snark_input. Note that all vectors are REVERSED
	/// so that in circuit, using Homer's approach is easier.
	pub fn gen_claims(
		pkey: &BatchProcessorProverParams<'a,E>,
		rng: &mut impl RngCore,
		words: &Vec<Vec<F>>)
	-> Result<(BatchClaim<E>, Vec<IndividualClaim<E>>, 
		SnarkAdvice<F>), Error>{
		//1. generate the global claim
		let n_words = words.len();

		let zero = F::zero();
		//one INDEPENDENT hiding pad per word: rayon::iter::repeat
		//would draw once and clone, sharing one pad across all words.
		let rands: Vec<F> = (0..n_words)
			.map(|_| <E::G1 as Group>::ScalarField::rand(rng))
			.collect();
		//T933 s9 B1. The second per-word blind o_i2, independent.
		let rands2: Vec<F> = (0..n_words)
			.map(|_| <E::G1 as Group>::ScalarField::rand(rng))
			.collect();
		let r_all_words = <E::G1 as Group>::ScalarField::rand(rng);
		let r_kzg_len = <E::G1 as Group>::ScalarField::rand(rng);
		//T933 s9 B2. Second nonces of kzg_all_words and kzg_length.
		let r_all_words2 = <E::G1 as Group>::ScalarField::rand(rng);
		let r_kzg_len2 = <E::G1 as Group>::ScalarField::rand(rng);
		//T932-F2W. Each word is followed by its blind rands[i], so
		//kzg_all_words commits to rands BEFORE any r_i is drawn (r_i
		//absorbs kzg_all_words). T933 s9 B1: then by rands2[i]. Layout
		//w1||o11||o12||...||wn||on1||on2, then || r_all_words ||
		//r_all_words2 and reversed below, as for every KZG vector.
		let all_words: Vec<F> = words.iter().zip(rands.iter())
			.zip(rands2.iter())
			.flat_map(|((w, r), r2)| w.iter().cloned()
				.chain([*r, *r2]))
			.collect();
		//here blind: zero (coz default kzg does not take blind anyway)
		let kzg_all_words = {
			let mut all_words2 = all_words.clone();
			all_words2.push(r_all_words);
			all_words2.push(r_all_words2);
			all_words2.reverse();
			KZG::<E>::commit(&pkey.kzg, &all_words2, &zero)?
		};
		assert!(words.len()==rands.len());

		let kzg_length = {
			let mut all_len:Vec<F> 
				= words.iter().map(|w| F::from(w.len() as u32)).collect();
			all_len.push(r_kzg_len);
			all_len.push(r_kzg_len2);
			all_len.reverse();
			KZG::<E>::commit(&pkey.kzg, &all_len, &zero)?
		};
		//T933 s10. The table commitments come from setup.
		let batch_claim = BatchClaim::<E>{kzg_all_words, kzg_length,
			kzg_lk_col1: pkey.lk_cm1, kzg_lk_col2: pkey.lk_cm2};

		//2. generate the individual claim
		let vec_idx = (0..n_words).collect::<Vec<usize>>();
		assert!(vec_idx.len()==n_words);
		let vec_kzg_words= words.par_iter().zip(rands.par_iter())
			.zip(rands2.par_iter())
			.map(|((w, r), r2)| {
				//T932-F2W. Commit (len, w) || rho, reversed
				//like every KZG vector. T933 s9 B1: (len, w) ||
				//o_i1 || o_i2, so o_i2 at X^0 and o_i1 at X^1.
				let mut w2 = vec![F::from(w.len() as u32)];
				w2.extend_from_slice(w);
				w2.push(*r);
				w2.push(*r2);
				w2.reverse();
				KZG::<E>::commit(&pkey.kzg, &w2, &zero)
					.expect("kzg fails")
			}).collect::<Vec<E::G1>>();
		let rc = Arc::new(Mutex::new(batch_claim.clone()));
		let vec_ind_claims = vec_kzg_words.iter().zip(vec_idx.iter())
			.map(|(kzg_word,i)| 
				IndividualClaim{i: *i, kzg_word:kzg_word.clone(), 
					ref_batch_claim: rc.clone()}
			).collect::<Vec<IndividualClaim<E>>>();

		//3. generate the SNARK input
		let vec_r_v = vec_kzg_words.iter().zip(vec_idx.iter())
			.zip(words.iter())
			.map(|((kzg_word,i),w)|{
        		let mut sponge= PoseidonSponge::<F>
					::new(&pkey.poseidon_config);
				let mut arr_fe:Vec<F> = vec![];
				let arr_c1 = {
					let guard = rc.lock().unwrap();
					vec![guard.kzg_all_words.clone(),
						guard.kzg_length.clone(),
						kzg_word.clone()]
				};
				for c in arr_c1{
					c.to_native_sponge_field_elements_as_vec()
						.to_sponge_field_elements(&mut arr_fe);
				}
				sponge.absorb(&F::from(*i as u32));
				sponge.absorb(&arr_fe);
				let r_i:F = sponge.squeeze_field_elements(1)[0];
				let r = rands[*i];
				//T932-F2W length prefix, as in the commitment.
				let mut w2 = vec![F::from(w.len() as u32)];
				w2.extend_from_slice(w);
				w2.push(r);
				w2.push(rands2[*i]); //T933 s9 B1
				w2.reverse();
				let p_i = poly_from_vec(w2).unwrap();
				let v_i = p_i.evaluate(&r_i);

				(r_i, v_i)
			}).collect::<Vec<(F,F)>>();
		let (vec_r, vec_v): (Vec<F>, Vec<F>) = vec_r_v.into_iter().unzip(); 

		//two INDEPENDENT nonces: rayon::iter::repeat draws once and
		//clones, which made all four of these identical.
		let r_vec_r = <E::G1 as Group>::ScalarField::rand(rng);
		let r_vec_v = <E::G1 as Group>::ScalarField::rand(rng);
		//T933 s9 B2. Second nonces, at Lagrange slot n_words+1.
		let r_vec_r2 = <E::G1 as Group>::ScalarField::rand(rng);
		let r_vec_v2 = <E::G1 as Group>::ScalarField::rand(rng);

		let snark_input = SnarkAdvice::<F>{
			rands, rands2,
			r_all_words, r_all_words2, r_kzg_len, r_kzg_len2,
			r_vec_r, r_vec_v, r_vec_r2, r_vec_v2,
			vec_r, vec_v
		};

		Ok( (batch_claim, vec_ind_claims, snark_input) )
	}

	/// Combiner `ch` of an individual proof (Issue 6b). It absorbs the
	/// batch's vector commitments BEFORE (r_i, v_i). With H(r_i, v_i)
	/// alone, a cheating batch prover could learn `ch` first and pick a
	/// screened word's slot value r_t so that r_t + ch*v_t equals the
	/// target of an unscreened word, since vec_r is free in the batch.
	pub fn ind_combiner(poseidon_config: &PoseidonConfig<F>,
		vcom_vec_r: &C1, vcom_vec_v: &C1, r_i: F, v_i: F) -> F {
		let mut arr_fe: Vec<F> = vec![];
		for c in [vcom_vec_r, vcom_vec_v] {
			c.to_native_sponge_field_elements_as_vec()
				.to_sponge_field_elements(&mut arr_fe);
		}
		let mut sponge = PoseidonSponge::<F>::new(poseidon_config);
		sponge.absorb(&arr_fe);
		sponge.absorb(&vec![r_i, v_i]);
		sponge.squeeze_field_elements(1)[0]
	}

	/// generate the individual proof for the i'th word (in SnarkAdvice)
	pub fn prove_individual(pkey: &BatchProcessorProverParams<'a,E>,
		snark_input: &SnarkAdvice<E::ScalarField>,
		words: &Vec<Vec<E::ScalarField>>,
		ind_claim: &IndividualClaim<E>,
		batch_proof: &BatchProof<E,S>,
		i: usize)->IndividualProof<E>{
		//1. retrieve r_i, v_i and compute ch for batched
		// verification of vec_r[r_i] and vec_v[v_i]
		assert!(i==ind_claim.i);	
		let r_i = snark_input.vec_r[i];
		let v_i = snark_input.vec_v[i];
		//note: r_i is hased from (com_v, com_r, i) already
		let ch = Self::ind_combiner(&pkey.poseidon_config,
			&batch_proof.vcom_vec_r, &batch_proof.vcom_vec_v,
			r_i, v_i);

		//2. compute the combined vector
		let zero = E::ScalarField::zero();
		let mut vec = snark_input.vec_r.iter().zip(snark_input.vec_v.iter()).
			map(|(a,b)| *a + ch * *b).collect::<Vec<E::ScalarField>>();
		let last_ele = snark_input.r_vec_r + ch * snark_input.r_vec_v;
		vec.push(last_ele);
		//T933 s9 B2. The second blind slot n_words+1.
		vec.push(snark_input.r_vec_r2 + ch * snark_input.r_vec_v2);
		//S102/F2: open the combined vec-com at the POSITION omega^i.
		//`ch` stays what it should be -- the linear-combination
		//coefficient that folds vec_r and vec_v into one vector.
		let idx_pt = pkey.vec.get_idx(i);
		let vcom_prf =
			VecCom::<'a,E>::prove_with_challenge(&pkey.vec, idx_pt, &vec,
			&zero, None).expect("vcom proof err");
		//T932-F2W. Open the length-prefixed vector, as gen_claims
		//commits it.
		let mut wi = vec![E::ScalarField::from(words[i].len() as u32)];
		wi.extend_from_slice(&words[i]);
		wi.push(snark_input.rands[i]);
		wi.push(snark_input.rands2[i]); //T933 s9 B1
		wi.reverse();
		let kzg_prf = KZG::<'a,E>
			::prove_with_challenge(&pkey.kzg, r_i,  &wi, &zero, None)
			.expect("kzg prf error");

		IndividualProof{vcom_prf, v_i, kzg_prf}
	}

	/// verify individual proof.
	pub fn verify_individual(vkey: &BatchProcessorVerifierParams<'a,E,CS1E,H>,
		i: usize,
		claim: &IndividualClaim<E>,
		//T932-F2W. The BatchClaim (pubstat) that verify_batch checked.
		batch_claim: &BatchClaim<E>,
		batch_proof: &BatchProof<E,S>,
		ind_proof: &IndividualProof<E>,
		log_tag: Option<usize>, //Some(job_id): route report lines to that
			//job's log; None keeps the legacy shared-stdout behaviour
		ctx: &'static str, //call-site tag, "self" (prover self-check) or
			//"final" (post-fold verification), so ONE job log tells them apart
		b_unbound: bool, //true when the run folds with the lookup check
			//off: a green verdict prints UNBOUND, not PASS (T933 Hole A).
			//The returned bool is unchanged.
		)->bool{
		//1. verify the generated challenges
		assert!(i==claim.i);
		// lvl: ERR for a failed sub-check, LOG1 for the always-on flags.
		let emit = |lvl: usize, m: String| match log_tag {
			Some(jid) => log(jid, lvl, &m),
			None => emit_stdout(m),
		};
		let mut sponge= PoseidonSponge::<E::ScalarField> 
			::new(&vkey.poseidon_config);
		let mut arr_fe:Vec<F> = vec![];
		let rc = &claim.ref_batch_claim;
		let (kzg_all_words, kzg_length) = {
			let guard = rc.lock().unwrap();
			(guard.kzg_all_words.clone(), guard.kzg_length.clone())
		};
		//T932-F2W (paper P18). r_i below is hashed over these
		//kzg_all_words and kzg_length. They must be the commitments
		//the aggregate opening bound, which are batch_claim's.
		let b_claim = kzg_all_words == batch_claim.kzg_all_words &&
			kzg_length == batch_claim.kzg_length;
		let arr_c1 = vec![kzg_all_words, kzg_length, claim.kzg_word.clone()];
		for c in arr_c1{
				c.to_native_sponge_field_elements_as_vec()
					.to_sponge_field_elements(&mut arr_fe);
		}
		sponge.absorb(&F::from(i as u32));
		sponge.absorb(&arr_fe);
		let r_i:F = sponge.squeeze_field_elements(1)[0];
		let v_i = ind_proof.v_i;
		//Issue 6b. ch absorbs vcom_vec_r and vcom_vec_v (ind_combiner)
		let ch = Self::ind_combiner(&vkey.poseidon_config,
			&batch_proof.vcom_vec_r, &batch_proof.vcom_vec_v,
			r_i, v_i);

		//2. verify the vec_com AT omega^i, and bind the opened value.
		//S102/F2: opening at `ch` and trusting the prover's own
		//proof.eval proved only "can open a commitment it knows" --
		//nothing about index i. The combined vector interpolates to
		//vec_r[i] + ch*vec_v[i] at omega^i, so that is the value the
		//opening must report.
		let newcm = batch_proof.vcom_vec_r + batch_proof.vcom_vec_v.mul(ch);
		//R2: evaluate EVERY sub-check, then AND them -- the returned
		//value is the same predicate the early returns computed.
		//b_vcom is the only one needing idx_pt, so None => false
		//reproduces the old `Err(_) => return false` exactly.
		//Issue 6a. Only the word slots 0..n_words-1 may be opened.
		//Slots n_words and n_words+1 hold the blinding nonces (T933
		//s9 B2, vec_dom_size = n_words + 2), and omega_pow_idx
		//wraps i, so an unchecked i reaches them. Do not write
		//`i + 2` here, since it wraps at usize::MAX without overflow
		//checks and then hits a blind slot when n_words + 2 is the
		//domain size. b_vcom stays the raw opening result, so the
		//log shows which of the two rejected.
		//T933 K2-min: the main decider pins the fold's word count to
		//n_words (public input 2), so i < n_words is a position in the
		//certified batch (lookups on; with b_check_lkup off the
		//verdict is UNBOUND).
		let b_range = i < vkey.n_words();
		let opt_idx = veccom::omega_pow_idx::<E::ScalarField>(
			vkey.vec_dom_size, i).ok();
		let b_idx = b_range && opt_idx.is_some();
		let b_vcom_eval = ind_proof.vcom_prf.eval == r_i + ch * v_i;
		let b_vcom = match opt_idx {
			Some(p) => VecCom::<'a,E>::verify_with_challenge(&vkey.vec,
				p, &newcm, &ind_proof.vcom_prf).is_ok(),
			None => false,
		};

		//3. verify the kzg commitment, and bind its opened value to v_i.
		//S102/F3: without this the check only proves the word
		//commitment opens to SOME value at r_i, not that it is v_i.
		let b_kzg_eval = ind_proof.kzg_prf.eval == v_i;
		let b_kzg = KZG::<'a,E>::verify_with_challenge(&vkey.kzg, r_i,
			&claim.kzg_word, &ind_proof.kzg_prf).is_ok();

		//4. report all six flags, then the detail of each red one.
		let ok = b_claim && b_idx && b_vcom_eval && b_vcom && b_kzg_eval
			&& b_kzg;
		emit(LOG1, format!("VERIFY-FLAGS ind[{}] i={}: claim={} idx={} \
			veval={} vcom={} keval={} kzg={} verdict={}", ctx, i,
			b_claim as u8, b_idx as u8, b_vcom_eval as u8,
			b_vcom as u8,
			b_kzg_eval as u8, b_kzg as u8,
			verdict_str(ok, b_unbound)));
		if !b_claim {emit(ERR, format!("ind[{}] i={}: claim's batch \
			commitments differ from pubstat", ctx, i));}
		if !b_idx {emit(ERR, format!("ind[{}] i={}: not a word slot \
			(n_words={}) or omega^i failed, dom_size={}", ctx, i,
			vkey.n_words(), vkey.vec_dom_size));}
		if !b_vcom_eval {emit(ERR, format!("ind[{}] i={}: vcom eval \
			got={} want={} (r_i={} ch={} v_i={})", ctx, i,
			ind_proof.vcom_prf.eval, r_i + ch * v_i, r_i, ch, v_i));}
		if !b_vcom {emit(ERR, format!("ind[{}] i={}: vcom pairing \
			fails", ctx, i));}
		if !b_kzg_eval {emit(ERR, format!("ind[{}] i={}: kzg eval \
			got={} want={}", ctx, i, ind_proof.kzg_prf.eval, v_i));}
		if !b_kzg {emit(ERR, format!("ind[{}] i={}: kzg pairing \
			fails, r_i={}", ctx, i, r_i));}
		ok
	}

	/// generate the global proof.
	/// snark_input is the input for snark prover.
	/// SnarkRandInput is PARTIAL (missing kzg_vec_r and kzg_vec_v)
	/// but including other information from driver such as
	///    the claim, the hash_cmF and the kzg to lookup tables
	/// Return the batch proof and the rebuilt rand-input for generating
	/// the (random challenge, random combination factor). The rebuilt
	/// rand-input is just for implementation convenience (it can
	/// be rebuilt from batch_claim and driver's verifier param).
	pub fn prove_batch(pkey: &BatchProcessorProverParams<'a,E>,
		snark_input: &SnarkAdvice<E::ScalarField>,
		words: &Vec<Vec<E::ScalarField>>,
		lkup: Arc<LK>,
		partial_rand_inp: &SnarkRandInput<E>) -> (BatchProof<E,S>, SnarkRandInput<E>){
		let mut rand_inp = partial_rand_inp.clone();

		//1. vcom and kzg of vec_r
		// NOTE: vcom (vec com) is the NORMAL sequence, kzg is the reversed
		let zero = E::ScalarField::zero();
		//T933 s9 B2. Both nonces, at slots n_words and n_words+1.
		let mut vec_r = vec![snark_input.vec_r.clone(), 
			vec![snark_input.r_vec_r, snark_input.r_vec_r2]].concat();
		let vcom_vec_r = VecCom::<'a,E>::commit(&pkey.vec, &vec_r, &zero)
			.expect("vcom_vec_r error");
		//after the reverse, index 0 IS the r_vec_r2 appended above
		//(r_vec_r at 1): kzg and vec_com must commit to the SAME vector.
		vec_r.reverse();
		let kzg_vec_r = KZG::<'a,E>::commit(&pkey.kzg, &vec_r, &zero)
			.expect("kzg_vec_r error"); 

		//2. vcom and kzg of vec_v
		let mut vec_v = vec![snark_input.vec_v.clone(), 
			vec![snark_input.r_vec_v, snark_input.r_vec_v2]].concat();
		let vcom_vec_v = VecCom::<'a,E>::commit(&pkey.vec, &vec_v, &zero)
			.expect("vcom_vec_v error");
		//after the reverse, index 0 IS the r_vec_v2 appended above
		//(r_vec_v at 1): kzg and vec_com must commit to the SAME vector.
		vec_v.reverse();
		let kzg_vec_v = KZG::<'a,E>::commit(&pkey.kzg, &vec_v, &zero)
			.expect("kzg_vec_r error"); 
		rand_inp.kzg_vec_r = kzg_vec_r.clone();
		rand_inp.kzg_vec_v = kzg_vec_v.clone();

		//3. build the qa_nizk for eqvauilence of vecom_vec_r and kzg_vec_r
		// and the same for vec_v
		let w = vec![vec_r, vec_v].concat();
		let prf_qa_nizk = prove_qa_nizk_fast(&w, zero, &pkey.pk_qa_nizk);
		if B_DEBUG {
			use crate::folding::foldpot::qa_nizk::compute_x;
			if pkey.pk_qa_nizk.matrix.is_some(){
				let matrix = pkey.pk_qa_nizk.matrix.as_ref();
				let x = compute_x::<E>(&w, zero, &matrix.unwrap());
				assert!(x[0] == kzg_vec_r);
				assert!(x[1] == vcom_vec_r);
				assert!(x[2] == kzg_vec_v);
				assert!(x[3] == vcom_vec_v);
			}
		}

		//4. build the aggregated KZG proof for 
		//kzg_lk1, kzg_lk2, kzg_all_w, kzg_vec_l, kzg_vec_r, kzg_vec_v, 
		// this challenge
		//should be fiat-shamir plus a commitment of Fixed Mem of 
		//stage 1 of the snark proof.
		// NOTE that to use homer's method (.... (a1+r*(a0)....)
		// all vectors are REVERSED!
		let (ch, rc) = rand_inp.gen_challenge();


		let agg_kzg_prf = {
			let (mut lk1, mut lk2) = lkup.get_cols();
			lk1.reverse();
			lk2.reverse();

			//T932-F2W. Same interleaved layout as kzg_all_words
			//in gen_claims (T933 s9: both blinds per word, two
			//trailing nonces).
			let mut all_words: Vec<F> = words.iter()
				.zip(snark_input.rands.iter())
				.zip(snark_input.rands2.iter())
				.flat_map(|((w, r), r2)| w.iter().cloned()
					.chain([*r, *r2]))
				.collect();
			all_words.push(snark_input.r_all_words);
			all_words.push(snark_input.r_all_words2);
			let mut all_len:Vec<F> 
				= words.iter().map(|w| F::from(w.len() as u32))
				.collect();
			all_words.reverse();

			all_len.push(snark_input.r_kzg_len);
			all_len.push(snark_input.r_kzg_len2);
			all_len.reverse();

			let mut vec_r = snark_input.vec_r.clone();
			vec_r.push(snark_input.r_vec_r);
			vec_r.push(snark_input.r_vec_r2);
			vec_r.reverse();

			let mut vec_v = snark_input.vec_v.clone();
			vec_v.push(snark_input.r_vec_v);
			vec_v.push(snark_input.r_vec_v2);
			vec_v.reverse();


			let vec2d = vec![lk1, lk2, all_words, all_len, vec_r, vec_v];
		


			let res = KZG::<E>::batch_prove_with_challenge(&pkey.kzg, ch, &vec2d, rc)
				.expect("kzg batch prove error");
			res
		};
			

		let batch_prf = BatchProof{
			vcom_vec_r, kzg_vec_r, vcom_vec_v, kzg_vec_v,
			prf_qa_nizk, ch, rc, agg_kzg_prf,

			kzg_all_com1: None,
			kzg_all_com_prf1: None,
			kzg_all_com2: None,
			kzg_all_com_prf2: None,
			comE2: None,
			comW2: None,
			comF2: None,
			qa_nizk_prf2: None,

			snark_proof_main: None,
			snark_proof_cp: None,
			mainres_hash: None,
			hash_cmF: rand_inp.hash_cmF.clone(), 
		};

		(batch_prf, rand_inp)

	}


	/// verify the batch proof
	/// vkey is the batch processor verifier of driver 1 (phase 1).
	/// NOTE that there are 3 qa_nizk verificatio:
	/// the first one using vkey.qa_nizk_vkey is for verifying equivalence
	/// between vec_com and kzg_com; the 2nd one: nova1_qa_nizk_vkey is for
	/// verifying kzg_all_com and comE, W, F; and nova2_qa_nizk_vkey2 
	/// does the same for the 2nd circuit.
	///
	/// when optional kzg_sum1 is passed as non-nill,
	/// it implies that the b_check_lkup flag is false for driver (that is
	/// we use a much smaller lkup share in circuit so that the entire
	/// lkup table is NOT covered by the folding of circuits). Thus,
	/// kzg_sum1 produced by the circuits will NOT BE equal
	/// to the KZG eval of the lkup as a poly. The cp SNARK input then
	/// takes the circuit's own kzg_sum1, so c5 is only a
	/// self-consistency check. Such a proof binds neither the lookup
	/// table nor the words, and a green part 2 is reported as
	/// verdict=UNBOUND, never PASS (T933 Hole A). Part 2 still runs, so
	/// c1-c4 keep their decider smoke test.
	pub fn verify_batch(
		vkey: &BatchProcessorVerifierParams<'a,E,CS1E,H>, 
		nova1_qa_nizk_vkey_hash: Option<E::ScalarField>, //only use in part2 
		nova2_qa_nizk_vkey: Option<QaNizkVerifierParams<E>>, //only use in part2
		snark_vk_main: Option<S::VerifyingKey>,
		snark_vk_cp: Option<S::VerifyingKey>,
		claim: &BatchClaim<E>,
		prf: &BatchProof<E,S>,
		poseidon_config: &PoseidonConfig<E::ScalarField>,
		b_check_part2: bool,
		opt_kzg_sum1: Option<F>, //optional kzg_sum1
		log_tag: Option<usize>, //Some(job_id): route sub-check FAILs to the
			//per-job log so a concurrent N-way batch attributes them per share
		ctx: &'static str, //call-site tag, "self" (prover self-check) or
			//"final" (post-fold verification), so ONE job log tells them apart
		)->bool{
		//0. build rand input for generate Fiat-Shamir randoms
		// route each report line to the per-job log when a job id is given
		// (bisect_job3.py N-way batch), else to shared stdout as before.
		// lvl: ERR for a failed sub-check, LOG1 for the always-on flags.
		let emit = |lvl: usize, m: String| match log_tag {
			Some(jid) => log(jid, lvl, &m),
			None => emit_stdout(m),
		};
		let rand_inp = SnarkRandInput::<E>{
			kzg_all_words: claim.kzg_all_words.clone(),
			kzg_length: claim.kzg_length.clone(),
			kzg_lk_col1: claim.kzg_lk_col1.clone(), 
			kzg_lk_col2: claim.kzg_lk_col2.clone(), 
			hash_cmF: prf.hash_cmF.clone(),
			kzg_vec_r: prf.kzg_vec_r.clone(),
			kzg_vec_v: prf.kzg_vec_v.clone(),
			poseidon_config: poseidon_config.clone()
		};


		//1. check the qa_nizkProof
		let x = vec![prf.kzg_vec_r.clone(), prf.vcom_vec_r.clone(),
			prf.kzg_vec_v.clone(), prf.vcom_vec_v.clone()];
		let b_qa = verify_qa_nizk::<E>(&x, &prf.prf_qa_nizk,
			&vkey.vk_qa_nizk);

		//2. verify the aggregated kzg proof 
		let coms = vec![
				claim.kzg_lk_col1.clone(),
				claim.kzg_lk_col2.clone(),
				claim.kzg_all_words.clone(),
				claim.kzg_length.clone(),
				prf.kzg_vec_r.clone(),
				prf.kzg_vec_v.clone()
		];
		let (ch, rc) = rand_inp.gen_challenge();
		let b_fs = ch==prf.ch && rc==prf.rc;
		let mut com_all = E::G1::zero();
		let mut factor = E::ScalarField::one();
		for i in 0..coms.len(){
			com_all = com_all + coms[i].mul(factor);
			factor = factor * rc;
		}
		let b_kzg = KZG::<E>::verify_with_challenge(&vkey.kzg,
			ch, &com_all, &prf.agg_kzg_prf).is_ok();

		//T933 s10 (paper Fig 16 (1)). The claim's lookup commitments
		//must be the ones setup made from the public table. They feed
		//only the Fiat-Shamir input and the aggregated opening above,
		//so without this a prover commits its own table and passes.
		let b_lk1 = claim.kzg_lk_col1 == vkey.lk_cm1;
		let b_lk2 = claim.kzg_lk_col2 == vkey.lk_cm2;
		let b_lk = b_lk1 && b_lk2;

		//R2: report ALL of part 1 before returning, so one red
		//sub-check no longer hides the other two.
		let part1_ok = b_qa && b_fs && b_kzg && b_lk;
		emit(LOG1, format!("VERIFY-FLAGS batch1[{}]: qa={} fs={} \
			kzg={} lk={} verdict={}", ctx, b_qa as u8, b_fs as u8,
			b_kzg as u8, b_lk as u8,
			if part1_ok {"PASS"} else {"REJECT"}));
		if !b_qa {emit(ERR, "qa_nizk verif fails".to_string());}
		if !b_fs {emit(ERR, format!("fs challenge (ch/rc) mismatch: \
			ch_exp={} ch_got={} rc_exp={} rc_got={}",
			ch, prf.ch, rc, prf.rc));}
		if !b_kzg {emit(ERR, format!("kzg verif fails: n_coms={} \
			eval={}", coms.len(), prf.agg_kzg_prf.eval));}
		if !b_lk {emit(ERR, format!("lkup commitments differ from vk: \
			col1={} col2={}", b_lk1 as u8, b_lk2 as u8));}
		if !part1_ok {
			//part 2 opens ~18 Options with .expect(); today's early
			//return makes those states unreachable, so keep the gate
			//and say why part 2 carries no flags.
			if b_check_part2 {
				emit(LOG1, format!("VERIFY-SKIP batch2[{}]: part 1 \
					REJECT -- part 2 not evaluated", ctx));
			}
			return false;
		}

		if b_check_part2{//check the rest part
			assert!(prf.kzg_all_com1.is_some());
			// so one (very expensive) run reveals the full pass/fail vector.
			// mh = mainres_hash, a per-job-unique correlation key for the
			// threaded log (verify_batch has no job_id).
			let mh = prf.mainres_hash.map(|x| format!("{}", x))
				.unwrap_or_else(|| "NA".to_string());

			//T934 D6: r_2 / r' = H(tag, C_WE / C_W'E', D) with D read
			//from the matching snark proof.
			let r2 = kzg_ch(poseidon_config, KZG_CH_TAG_S1, prf.kzg_all_com1.expect("kzg1 empty"),
				S::commitment(prf.snark_proof_main.as_ref().expect("snark main empty")));
			let rp = kzg_ch(poseidon_config, KZG_CH_TAG_S2, prf.kzg_all_com2.expect("kzg2 empty"),
				S::commitment(prf.snark_proof_cp.as_ref().expect("snark cp empty")));

			//1. check kzg_all_com1
			let c1 = CS1E::verify_with_challenge(
				&vkey.kzg_driver1.clone().expect("driver 1 kzg ver key null!"),
				r2,
				&prf.kzg_all_com1.expect("kzg1 empty"),
				&prf.kzg_all_com_prf1.as_ref().expect("prf1 empty")).is_ok();
			if !c1 {emit(ERR, "cs1e kzg_all_ocm1 verif fails".to_string());}

			//2. check kzg_all_com2
			let c2 = CS1E::verify_with_challenge(
				&vkey.kzg_driver2.clone().expect("driver2 kzg ver null!"),
				rp,
				&prf.kzg_all_com2.expect("kzg2 empty"),
				&prf.kzg_all_com_prf2.as_ref().expect("prf2 empty")).is_ok();
			if !c2 {emit(ERR, "cs1e kzg_all_com2 res2 fails".to_string());}

			//3. check qa_nizk_prf2
			let vec_x = vec![
				prf.kzg_all_com2.unwrap().clone(),
				prf.comW2.unwrap().clone(),
				prf.comE2.unwrap().clone(),
				prf.comF2.unwrap().clone()];
			let c3 = verify_qa_nizk::<E>(
				&vec_x,
				&prf.qa_nizk_prf2.clone().unwrap(),
				&nova2_qa_nizk_vkey.expect("qanizk vkey empty")
			);
			if !c3 {emit(ERR, "qanizk2 fails".to_string());}

			//4. check the snark proof
			let kzg_sum1 = if opt_kzg_sum1.is_some(){
				opt_kzg_sum1.unwrap() //in NOT check lkup mode
					//the full eval of entire lkup KZG will not work
					//take the circuits' output instead.
			}else{
				prf.agg_kzg_prf.eval //normal mode
			};
			//4.1 verify the maincirc snark proof
			let pub_inp = vec![prf.mainres_hash.unwrap(),
				F::from(vkey.n_words() as u64)];
			let snark_v_main = S::verify(
				&snark_vk_main.expect("snark vkey_main empty"),
				&pub_inp,
				&prf.snark_proof_main.as_ref().clone()
					.expect("snark main empty")
			);
			let c4 = snark_v_main.is_ok() && snark_v_main.unwrap().clone();
			if !c4 {emit(ERR, "snark main fails.".to_string());}

			//4.2 verify te cpcirc snark proof
			let snark_inp = CircPubInput{
				ch1: prf.ch,
				rc1: prf.rc,
				//S107: FS-seed pin -- the cp snark verifies only
				//if prf.hash_cmF == the disclosed decider z_n[0].
				hash_cmF1: prf.hash_cmF,
				kzg_sum1: kzg_sum1,
				kzg_all_com_ch1: r2,
				eval_w_e1: prf.kzg_all_com_prf1.clone()
					.expect("eval_w_e1 null").eval,
				mainres_hash: prf.mainres_hash.unwrap(),

				kzg_all_com_ch2: rp,
				eval_w_e2: prf.kzg_all_com_prf2.clone()
					.expect("eval_w_e2 null").eval,

				comE2: prf.comE2.expect("com_e2 null").clone(),
				comW2: prf.comW2.expect("com_e2 null").clone(),
				comF2: prf.comF2.expect("com_e2 null").clone(),
				kzg_all_com1: prf.kzg_all_com1.expect("kzg1 empty"),

				qa_nizk_vkey_hash: nova1_qa_nizk_vkey_hash
					.expect("nova1 qanizk vkey hash empty!"),

			};
			let public_input: Vec<F> = snark_inp.to_vec().expect("to_vec err");
        	let snark_v_cp= S::verify(
				&snark_vk_cp.expect("snark vkey empty!"),
				&public_input,
				&prf.snark_proof_cp.as_ref().clone().expect("snark pf empty"));
					//.map_err(|e| Error::Other(e.to_string())).unwrap();
			let c5 = snark_v_cp.is_ok() && snark_v_cp.unwrap().clone();
			if !c5 {emit(ERR, "snark_v_cp fails.".to_string());}
			//R5: the rebuilt public inputs are the only evidence for a
			//cp-snark rejection (counterpart to driver.rs 60100.3.1
			//assemble-side); dump them on failure only.
			if !c5 {
				for (k, v) in public_input.iter().enumerate() {
					emit(ERR, format!("snark_v_cp pubin[{}] = {}",
						k, v));
				}
			}

			let part2_ok = c1 && c2 && c3 && c4 && c5;
			emit(LOG1, format!("VERIFY-FLAGS batch2[{}]: c1={} c2={} \
				c3={} c4={} c5={} mh={} n_pub={} verdict={}", ctx,
				c1 as u8, c2 as u8, c3 as u8, c4 as u8, c5 as u8,
				mh, public_input.len(),
				verdict_str(part2_ok, opt_kzg_sum1.is_some())));
			if !part2_ok { return false; }
		}

		true
	}
}



#[cfg(test)]
mod tests_batch_proc {
	use ark_groth16::Groth16;
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
	use crate::folding::foldpot::batch_proc::{BatchProcessor,SnarkRandInput};
//    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_std::{test_rng, UniformRand,Zero};
	use ark_ec::{Group};
	use crate::folding::foldpot::sigma_ir1cs::{LookupTableTwoCol,LookupTableTwoCol_Inst};

  //  use super::*;
   use crate::transcript::poseidon::poseidon_canonical_config;
   use crate::folding::foldpot::{batch_proc::KZG};
   use std::sync::{Arc, Mutex};
	//S102/F2+F3: for the forged-word rejection test below.
	use crate::folding::foldpot::batch_proc::{IndividualClaim,
		IndividualProof};
	use crate::folding::foldpot::veccom::VecCom;
	use ark_crypto_primitives::sponge::{
		poseidon::PoseidonSponge, Absorb, CryptographicSponge};
	use crate::transcript::AbsorbNonNative;
	use crate::utils::vec::poly_from_vec;
	use crate::commitment::CommitmentScheme;
	use ark_poly::Polynomial;

	/// T933 Hole A: a green check-off run prints UNBOUND, never PASS.
	/// REJECT wins over the unbound flag.
	#[test]
	fn verdict_str_fails_closed_when_unbound(){
		use crate::folding::foldpot::batch_proc::verdict_str;
		assert_eq!(verdict_str(true, false), "PASS");
		assert_eq!(verdict_str(true, true), "UNBOUND");
		assert_eq!(verdict_str(false, false), "REJECT");
		assert_eq!(verdict_str(false, true), "REJECT");
	}


   #[test]
   fn batch_proc(){
		type CS1E = KZG<'static, Bn254>;
   		let mut words = vec![];
		let n_words = 20;
        let mut rng = &mut test_rng();
		for _i in 0..n_words{
			let mut word = vec![];
			//for j in 0..2{ word.push(Fr::from( (j+i) as u32)); }
			for _j in 0..2{ word.push(Fr::rand(&mut rng)); }
			words.push(word);
		}
		let lk = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)), //0, null entry
			(Fr::from(1u32), Fr::from(0u32)), 
			(Fr::from(1u32), Fr::from(1u32))]);
		let lkup = Arc::new(lk);

		let keysize = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>, CS1E, false>::key_size(&words);
		let (pk,vk) = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>, CS1E, false>::setup(&mut rng,keysize,n_words,
			poseidon_canonical_config::<Fr>(), 0, &lkup);
		let (global_claim, ind_claims, snark_inp) = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>, Groth16<Bn254>, CS1E, false>::gen_claims(&pk, &mut rng, &words).unwrap();

		let i = 2;
		let poseidon_config = poseidon_canonical_config::<Fr>();
		let g1 = G1::generator();

		let partial_input = SnarkRandInput::<Bn254>{
			kzg_all_words: global_claim.kzg_all_words.clone(),
			kzg_length: global_claim.kzg_length.clone(),
			kzg_lk_col1: global_claim.kzg_lk_col1.clone(), 
			kzg_lk_col2: global_claim.kzg_lk_col2.clone(), 
			hash_cmF: Fr::zero(),
			kzg_vec_r: g1.clone(), //default value
			kzg_vec_v: g1.clone(),
			poseidon_config: poseidon_config.clone()
		};

		let (batch_proof, _rand_inp2) = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>, CS1E, false> ::prove_batch(&pk, &snark_inp, &words, lkup, &partial_input); 
		assert!(BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E, false>::verify_batch(&vk, None, None, None, None, &global_claim, &batch_proof, &poseidon_config, false, None, None,
			"test"));
		let ind_prf = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E,false>::prove_individual(&pk, 
			&snark_inp, &words, &ind_claims[i], &batch_proof, i);
		let res = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E,false>::verify_individual(&vk, i,
			&ind_claims[i], &global_claim, &batch_proof, &ind_prf, None, "test", false);
		assert!(res, "verify indidivudal proof failed");
   }

	/// T932W-A fixture. n_words random words of length wlen, key from
	/// key_size(), then gen_claims, prove_batch, verify_batch (asserted)
	/// and the honest individual proof of word i.
	type T932Bp = BatchProcessor<Bn254,LookupTableTwoCol_Inst<Fr>,
		Groth16<Bn254>,KZG<'static, Bn254>,false>;
	struct T932wFix{
		words: Vec<Vec<Fr>>,
		pk: super::BatchProcessorProverParams<'static, Bn254>,
		vk: super::BatchProcessorVerifierParams<'static, Bn254,
			KZG<'static, Bn254>,false>,
		global_claim: super::BatchClaim<Bn254>,
		ind_claims: Vec<IndividualClaim<Bn254>>,
		snark_inp: super::SnarkAdvice<Fr>,
		batch_proof: super::BatchProof<Bn254,Groth16<Bn254>>,
		ind_prf: IndividualProof<Bn254>,
		i: usize,
	}
	fn t932w_fix(n_words: usize, wlen: usize, i: usize) -> T932wFix{
		let mut rng = test_rng();
		let words: Vec<Vec<Fr>> = (0..n_words).map(|_|
			(0..wlen).map(|_| Fr::rand(&mut rng)).collect()).collect();
		let lkup = Arc::new(LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]));
		let cfg = poseidon_canonical_config::<Fr>();
		let (pk, vk) = T932Bp::setup(&mut rng, T932Bp::key_size(&words),
			n_words, cfg.clone(), 0, &lkup);
		let (global_claim, ind_claims, snark_inp) =
			T932Bp::gen_claims(&pk, &mut rng, &words).unwrap();
		let g1 = G1::generator();
		let partial_input = SnarkRandInput::<Bn254>{
			kzg_all_words: global_claim.kzg_all_words.clone(),
			kzg_length: global_claim.kzg_length.clone(),
			kzg_lk_col1: global_claim.kzg_lk_col1.clone(),
			kzg_lk_col2: global_claim.kzg_lk_col2.clone(),
			hash_cmF: Fr::zero(),
			kzg_vec_r: g1.clone(),
			kzg_vec_v: g1.clone(),
			poseidon_config: cfg.clone()
		};
		let (batch_proof, _r2) = T932Bp::prove_batch(&pk, &snark_inp,
			&words, lkup, &partial_input);
		assert!(T932Bp::verify_batch(&vk, None, None, None, None,
			&global_claim, &batch_proof, &cfg, false, None, None, "test"),
			"T932W-A: verify_batch failed on the honest fixture");
		let ind_prf = T932Bp::prove_individual(&pk, &snark_inp, &words,
			&ind_claims[i], &batch_proof, i);
		T932wFix{words, pk, vk, global_claim, ind_claims, snark_inp,
			batch_proof, ind_prf, i}
	}
	fn t932w_verify(f: &T932wFix, claim: &IndividualClaim<Bn254>,
		bc: &super::BatchClaim<Bn254>) -> bool{
		T932Bp::verify_individual(&f.vk, f.i, claim, bc, &f.batch_proof,
			&f.ind_prf, None, "test", false)
	}
	fn t932w_kzg(f: &T932wFix, v: &Vec<Fr>) -> G1{
		let mut v2 = v.clone();
		v2.reverse();
		KZG::<Bn254>::commit(&f.pk.kzg, &v2, &Fr::zero()).unwrap()
	}

	/// T932W-A item 0 (C1.1). 7 words of length 2: kzg_all_words needs
	/// 14 + 7 + 1 = 22 coefficients (T933 s9: 14 + 14 + 2 = 30). Without
	/// C1.1 the key has 18 powers and gen_claims fails. Items 1
	/// (positive) run on the same fixture.
	#[test]
	fn t932w_a0_key_bound_and_positive(){
		let f = t932w_fix(7, 2, 2);
		assert!(t932w_verify(&f, &f.ind_claims[f.i], &f.global_claim),
			"T932W-A1: honest individual proof rejected");
	}

	/// T932W-A item 2 (C1.3). The per-word commitment is
	/// kzg(reverse((len, w) || rho)), not kzg(reverse(w || rho)). A claim
	/// on the old layout is rejected. T933 s9 B1: rho is the pair
	/// (rho, rho2).
	#[test]
	fn t932w_a2_prefix_layout(){
		let f = t932w_fix(20, 2, 2);
		let (w, rho) = (&f.words[f.i], f.snark_inp.rands[f.i]);
		let rho2 = f.snark_inp.rands2[f.i];
		let mut pre = vec![Fr::from(w.len() as u32)];
		pre.extend_from_slice(w);
		pre.push(rho);
		pre.push(rho2);
		let mut old = w.clone();
		old.push(rho);
		old.push(rho2);
		let (c_pre, c_old) = (t932w_kzg(&f, &pre), t932w_kzg(&f, &old));
		assert!(f.ind_claims[f.i].kzg_word == c_pre,
			"T932W-A2: kzg_word is not the length-prefixed layout");
		assert!(c_pre != c_old);
		let mut claim_old = f.ind_claims[f.i].clone();
		claim_old.kzg_word = c_old;
		assert!(!t932w_verify(&f, &claim_old, &f.global_claim),
			"T932W-A2: old-layout claim accepted");
	}

	/// T932W-A item 3 (C1.7). Each batch commitment of the checked
	/// claim, changed alone, makes verify_individual reject. r_i is
	/// hashed over ref_batch_claim, which stays honest, so only b_claim
	/// moves.
	#[test]
	fn t932w_a3_claim_check_per_field(){
		let f = t932w_fix(20, 2, 2);
		let g = G1::generator();
		assert!(t932w_verify(&f, &f.ind_claims[f.i], &f.global_claim));
		let mut bc = f.global_claim.clone();
		bc.kzg_all_words += g;
		assert!(!t932w_verify(&f, &f.ind_claims[f.i], &bc),
			"T932W-A3: changed kzg_all_words accepted");
		let mut bc = f.global_claim.clone();
		bc.kzg_length += g;
		assert!(!t932w_verify(&f, &f.ind_claims[f.i], &bc),
			"T932W-A3: changed kzg_length accepted");
	}

	/// T932W-A item 4 (C1.2, C1.8). kzg_all_words commits to
	/// w_1, rho_1, ..., w_n, rho_n, r_all_words (reversed). Built with a
	/// plain loop. verify_batch passed in the fixture, so the aggregate
	/// opening (C1.8) uses the same polynomial. T933 s9: each rho_j is
	/// followed by rho2_j, and r_all_words by r_all_words2.
	#[test]
	fn t932w_a4_interleaved_layout(){
		let f = t932w_fix(20, 2, 2);
		let mut s: Vec<Fr> = vec![];
		for j in 0..f.words.len(){
			for x in f.words[j].iter(){ s.push(*x); }
			s.push(f.snark_inp.rands[j]);
			s.push(f.snark_inp.rands2[j]);
		}
		s.push(f.snark_inp.r_all_words);
		s.push(f.snark_inp.r_all_words2);
		assert!(f.global_claim.kzg_all_words == t932w_kzg(&f, &s),
			"T932W-A4: kzg_all_words is not the interleaved layout");
	}

	/// T932W-A item 5, regression guard. r_i absorbs both batch
	/// commitments: moving one in BOTH the claim's ref and the checked
	/// claim (b_claim holds) must still reject.
	#[test]
	fn t932w_a5_r_i_absorbs_batch_commitments(){
		let f = t932w_fix(20, 2, 2);
		let g = G1::generator();
		for k in 0..2{
			let mut bc2 = f.global_claim.clone();
			if k == 0 {bc2.kzg_all_words += g;} else {bc2.kzg_length += g;}
			let mut claim2 = f.ind_claims[f.i].clone();
			claim2.ref_batch_claim = Arc::new(Mutex::new(bc2.clone()));
			assert!(!t932w_verify(&f, &claim2, &bc2),
				"T932W-A5: r_i ignores batch commitment {}", k);
		}
	}

	/// S102/F2+F3: a certificate for a word never in the batch must be
	/// REJECTED. Pre-fix both checks were vacuous and this passed.
	#[test]
	fn individual_proof_rejects_forged_word(){
		type CS1E = KZG<'static, Bn254>;
		let mut rng = test_rng();
		let n_words = 20;
		let mut words = vec![];
		for _i in 0..n_words{
			let mut word = vec![];
			for _j in 0..2{ word.push(Fr::rand(&mut rng)); }
			words.push(word);
		}
		let lk = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]);
		let lkup = Arc::new(lk);
		let keysize = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,
			Groth16<Bn254>,CS1E,false>::key_size(&words);
		let (pk,vk) = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,
			Groth16<Bn254>,CS1E,false>::setup(&mut rng, keysize, n_words,
			poseidon_canonical_config::<Fr>(), 0, &lkup);
		let (global_claim, ind_claims, snark_inp) =
			BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,
			Groth16<Bn254>,CS1E,false>::gen_claims(
			&pk, &mut rng, &words).unwrap();
		let poseidon_config = poseidon_canonical_config::<Fr>();
		let g1 = G1::generator();
		let partial_input = SnarkRandInput::<Bn254>{
			kzg_all_words: global_claim.kzg_all_words.clone(),
			kzg_length: global_claim.kzg_length.clone(),
			kzg_lk_col1: global_claim.kzg_lk_col1.clone(),
			kzg_lk_col2: global_claim.kzg_lk_col2.clone(),
			hash_cmF: Fr::zero(),
			kzg_vec_r: g1.clone(),
			kzg_vec_v: g1.clone(),
			poseidon_config: poseidon_config.clone()
		};
		let (batch_proof, _r2) = BatchProcessor::<Bn254,
			LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E,false>
			::prove_batch(&pk, &snark_inp, &words, lkup, &partial_input);

		//the forgery: a word that is NOT in the batch, committed and
		//opened HONESTLY at every step. Only its membership is a lie.
		let i = 2;
		let zero = Fr::zero();
		let mut w2 = vec![Fr::rand(&mut rng), Fr::rand(&mut rng)];
		w2.push(Fr::rand(&mut rng)); //the 1-leaky nonce
		w2.reverse();
		let kzg_word_fake = KZG::<Bn254>::commit(&pk.kzg, &w2, &zero)
			.unwrap();
		let claim_fake = IndividualClaim::<Bn254>{ i,
			kzg_word: kzg_word_fake,
			ref_batch_claim: ind_claims[i].ref_batch_claim.clone()};

		//r_i' is an RO output over the FORGED commitment, so it differs
		//from the honest vec_r[i]; the forger then opens honestly at it.
		let mut sponge = PoseidonSponge::<Fr>::new(&poseidon_config);
		let mut arr_fe: Vec<Fr> = vec![];
		for c in vec![global_claim.kzg_all_words.clone(),
			global_claim.kzg_length.clone(), kzg_word_fake]{
			c.to_native_sponge_field_elements_as_vec()
				.to_sponge_field_elements(&mut arr_fe);
		}
		sponge.absorb(&Fr::from(i as u32));
		sponge.absorb(&arr_fe);
		let r_fake: Fr = sponge.squeeze_field_elements(1)[0];
		let v_fake = poly_from_vec(w2.clone()).unwrap().evaluate(&r_fake);
		let kzg_prf = KZG::<Bn254>::prove_with_challenge(
			&pk.kzg, r_fake, &w2, &zero, None).unwrap();
		//the verifier's own combiner (Issue 6b), so the forger is not
		//rejected merely for using a stale formula
		let ch = T932Bp::ind_combiner(&poseidon_config,
			&batch_proof.vcom_vec_r, &batch_proof.vcom_vec_v,
			r_fake, v_fake);

		//best effort on the vec-com: open the REAL combined vector, the
		//only one matching newcm, at omega^i.
		let mut vec_c = snark_inp.vec_r.iter().zip(snark_inp.vec_v.iter())
			.map(|(a,b)| *a + ch * *b).collect::<Vec<Fr>>();
		vec_c.push(snark_inp.r_vec_r + ch * snark_inp.r_vec_v);
		vec_c.push(snark_inp.r_vec_r2 + ch * snark_inp.r_vec_v2);
		//Try BOTH opening points. omega^i is the forger's best move
		//against the current verifier; `ch` is what a pre-fix forger
		//used. Asserting on both stops this test passing for the
		//trivial reason that the opening point simply mismatched --
		//with F2/F3 reverted, the `ch` arm IS accepted (measured).
		for (name, pt) in vec![("omega^i", pk.vec.get_idx(i)),
			("ch", ch)]{
			let vcom_prf = VecCom::<Bn254>::prove_with_challenge(
				&pk.vec, pt, &vec_c, &zero, None).unwrap();
			let ind_prf = IndividualProof::<Bn254>{
				vcom_prf, v_i: v_fake, kzg_prf: kzg_prf.clone()};
			let res = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,
				Groth16<Bn254>,CS1E,false>::verify_individual(
				&vk, i, &claim_fake, &global_claim, &batch_proof, &ind_prf, None, "test",
				false);
			assert!(!res,
				"forged word ACCEPTED (opened at {}): F2/F3 not binding",
				name);
		}
	}

	use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;

	/// Issue 6 fixture. n_words two-char words (word `empty` has length
	/// 0 if given), honest claims, keys, and the part-1 rand input.
	struct Issue6Fix{
		words: Vec<Vec<Fr>>,
		lkup: Arc<LookupTableTwoCol_Inst<Fr>>,
		pk: super::BatchProcessorProverParams<'static, Bn254>,
		vk: super::BatchProcessorVerifierParams<'static, Bn254,
			KZG<'static, Bn254>, false>,
		gc: super::BatchClaim<Bn254>,
		claims: Vec<IndividualClaim<Bn254>>,
		si: super::SnarkAdvice<Fr>,
		partial: SnarkRandInput<Bn254>,
	}
	fn issue6_setup(n_words: usize, empty: Option<usize>) -> Issue6Fix{
		let mut rng = test_rng();
		let words: Vec<Vec<Fr>> = (0..n_words).map(|k|
			if Some(k) == empty { vec![] }
			else { vec![Fr::rand(&mut rng), Fr::rand(&mut rng)] })
			.collect();
		let lkup = Arc::new(LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]));
		let pc = poseidon_canonical_config::<Fr>();
		let (pk, vk) = T932Bp::setup(&mut rng, T932Bp::key_size(&words),
			n_words, pc.clone(), 0, &lkup);
		let (gc, claims, si) = T932Bp::gen_claims(&pk, &mut rng, &words)
			.unwrap();
		let g1 = G1::generator();
		let partial = SnarkRandInput::<Bn254>{
			kzg_all_words: gc.kzg_all_words,
			kzg_length: gc.kzg_length,
			kzg_lk_col1: gc.kzg_lk_col1,
			kzg_lk_col2: gc.kzg_lk_col2,
			hash_cmF: Fr::zero(), kzg_vec_r: g1, kzg_vec_v: g1,
			poseidon_config: pc};
		Issue6Fix{words, lkup, pk, vk, gc, claims, si, partial}
	}

	/// r_i exactly as verify_individual derives it for (i, C).
	fn issue6_r(pc: &PoseidonConfig<Fr>,
		gc: &super::BatchClaim<Bn254>, i: usize, c: G1) -> Fr {
		let mut sponge = PoseidonSponge::<Fr>::new(pc);
		let mut arr_fe: Vec<Fr> = vec![];
		for x in vec![gc.kzg_all_words, gc.kzg_length, c]{
			x.to_native_sponge_field_elements_as_vec()
				.to_sponge_field_elements(&mut arr_fe);
		}
		sponge.absorb(&Fr::from(i as u32));
		sponge.absorb(&arr_fe);
		sponge.squeeze_field_elements(1)[0]
	}

	/// An unscreened word C*, honestly committed, and its (r*, v*) at
	/// index i. Returns (coefficients, C*, r*, v*).
	fn issue6_unscreened(f: &Issue6Fix, i: usize) -> (Vec<Fr>, G1, Fr, Fr){
		let mut rng = test_rng();
		let mut wm = vec![Fr::rand(&mut rng), Fr::rand(&mut rng),
			Fr::rand(&mut rng)];
		wm.reverse();
		let c_star = KZG::<Bn254>::commit(&f.pk.kzg, &wm, &Fr::zero())
			.unwrap();
		let r_star = issue6_r(&f.partial.poseidon_config, &f.gc, i, c_star);
		let v_star = poly_from_vec(wm.clone()).unwrap().evaluate(&r_star);
		(wm, c_star, r_star, v_star)
	}

	/// Plant (r*, v*) of an unscreened word C* in the blind slot, prove
	/// the batch, and return the verdict of verify_individual for C* at
	/// index i, opened at the domain point pt. T933 s9 B2: `second`
	/// plants in the second blind slot n_words+1 instead of n_words.
	fn issue6_blind_forgery(f: &mut Issue6Fix, i: usize, pt: Fr,
		ctx: &'static str, second: bool) -> bool {
		let pc = f.partial.poseidon_config.clone();
		let zero = Fr::zero();
		let (wm, c_star, r_star, v_star) = issue6_unscreened(f, i);
		if second {
			f.si.r_vec_r2 = r_star;
			f.si.r_vec_v2 = v_star;
		} else {
			f.si.r_vec_r = r_star;
			f.si.r_vec_v = v_star;
		}
		let (bp, _) = T932Bp::prove_batch(&f.pk, &f.si, &f.words,
			f.lkup.clone(), &f.partial);
		assert!(T932Bp::verify_batch(&f.vk, None, None, None, None, &f.gc,
			&bp, &pc, false, None, None, ctx),
			"Issue 6a: verify_batch rejects the planted nonces");
		let ch = T932Bp::ind_combiner(&pc, &bp.vcom_vec_r,
			&bp.vcom_vec_v, r_star, v_star);
		let mut vec_c = f.si.vec_r.iter().zip(f.si.vec_v.iter())
			.map(|(a,b)| *a + ch * *b).collect::<Vec<Fr>>();
		vec_c.push(f.si.r_vec_r + ch * f.si.r_vec_v);
		vec_c.push(f.si.r_vec_r2 + ch * f.si.r_vec_v2);
		let vcom_prf = VecCom::<Bn254>::prove_with_challenge(&f.pk.vec,
			pt, &vec_c, &zero, None).unwrap();
		let kzg_prf = KZG::<Bn254>::prove_with_challenge(&f.pk.kzg,
			r_star, &wm, &zero, None).unwrap();
		let claim = IndividualClaim::<Bn254>{ i, kzg_word: c_star,
			ref_batch_claim: f.claims[0].ref_batch_claim.clone() };
		let prf = IndividualProof::<Bn254>{ vcom_prf, v_i: v_star,
			kzg_prf };
		T932Bp::verify_individual(&f.vk, i, &claim, &f.gc, &bp, &prf,
			None, ctx, false)
	}

	/// Issue 6a. Slot n_words holds the blinding nonces, which no batch
	/// check constrains. A batch prover that sets them to (r*, v*) of an
	/// unscreened word opens that slot honestly, so only the index range
	/// check rejects the proof.
	#[test]
	fn individual_proof_rejects_blind_slot(){
		let mut f = issue6_setup(20, None);
		let i = f.words.len();
		let pt = f.pk.vec.get_idx(i);
		let res = issue6_blind_forgery(&mut f, i, pt, "test-6a", false);
		assert!(!res, "blind-slot forgery ACCEPTED, no range check");
	}

	/// T933-B2 (s9). Both blind slots, n_words and n_words+1, hold
	/// unconstrained nonces. The 64217 forgery planted in either one is
	/// rejected by the range check alone (verify_batch passes).
	#[test]
	fn t933_b2_blind_slots_rejected(){
		for (k, second) in [(0usize, false), (1usize, true)]{
			let mut f = issue6_setup(20, None);
			let n = f.words.len();
			assert_eq!(f.vk.vec_dom_size, n + 2,
				"T933-B2: veccom is not n_words + 2 slots");
			let i = n + k;
			let pt = f.pk.vec.get_idx(i);
			let res = issue6_blind_forgery(&mut f, i, pt, "test-s9-b2",
				second);
			assert!(!res, "T933-B2: forgery in blind slot n+{} ACCEPTED", k);
		}
	}

	/// Issue 6a with overflow. With n_words + 2 = 32 = the domain size
	/// (T933 s9: n_words = 30), omega^usize::MAX = omega^31 is the
	/// second blind slot, and `i as u32` maps usize::MAX to u32::MAX in
	/// r_i. A check written as `i + 2 < vec_dom_size` wraps there
	/// without overflow checks.
	#[test]
	fn individual_proof_rejects_wrapped_index(){
		let mut f = issue6_setup(30, None);
		let i = usize::MAX;
		let pt = super::veccom::omega_pow_idx::<Fr>(f.vk.vec_dom_size, i)
			.unwrap();
		assert!(pt == f.pk.vec.get_idx(f.words.len() + 1),
			"not the blind slot");
		let res = issue6_blind_forgery(&mut f, i, pt, "test-6a-max", true);
		assert!(!res, "index usize::MAX ACCEPTED, range check wraps");
	}

	/// Issue 6b. vec_r is free in the batch relation. If a batch prover
	/// could compute the combiner ch before fixing vec_r, it could set
	/// the slot i of a screened word t to r_t with r_t + ch*v_t =
	/// r* + ch*v*, and an unscreened word would open at the in-range
	/// index i. Word t is empty, so p_t = rho2_t + rho_t X (prefixed
	/// layout (0) || rho_t || rho2_t, T932 + T933 s9) and r_t solves a
	/// linear equation. The forger takes ch from the honest batch's
	/// commitments, then re-proves the batch with slot i changed, which
	/// moves ch.
	#[test]
	fn individual_proof_rejects_combiner_forgery(){
		let i = 2usize;
		let f = issue6_setup(20, Some(i));
		let pc = f.partial.poseidon_config.clone();
		let zero = Fr::zero();
		let (bp0, _) = T932Bp::prove_batch(&f.pk, &f.si, &f.words,
			f.lkup.clone(), &f.partial);
		let (wm, c_star, r_star, v_star) = issue6_unscreened(&f, i);
		let ch = T932Bp::ind_combiner(&pc, &bp0.vcom_vec_r,
			&bp0.vcom_vec_v, r_star, v_star);
		//p_t = reverse((0) || rho_t || rho2_t) = rho2_t + rho_t X, so
		//r_t + ch*p_t(r_t) = r* + ch*v* gives
		//r_t = (r* + ch*v* - ch*rho2_t) / (1 + ch*rho_t)
		let mut t = vec![Fr::zero(), f.si.rands[i], f.si.rands2[i]];
		t.reverse();
		let p_t = poly_from_vec(t).unwrap();
		let (rho_t, rho2_t) = (f.si.rands[i], f.si.rands2[i]);
		use ark_ff::Field;
		let r_t = (r_star + ch * v_star - ch * rho2_t)
			* (Fr::from(1u32) + ch * rho_t).inverse().unwrap();
		let v_t = p_t.evaluate(&r_t);
		assert_eq!(v_t, rho2_t + rho_t * r_t, "empty word is not linear");
		assert_eq!(r_t + ch * v_t, r_star + ch * v_star);
		let mut si2 = f.si.clone();
		si2.vec_r[i] = r_t;
		si2.vec_v[i] = v_t;
		let (bp, _) = T932Bp::prove_batch(&f.pk, &si2, &f.words,
			f.lkup.clone(), &f.partial);
		assert!(T932Bp::verify_batch(&f.vk, None, None, None, None,
			&f.gc, &bp, &pc, false, None, None, "test"),
			"Issue 6b: verify_batch rejects the free r_t");
		let kzg_prf = KZG::<Bn254>::prove_with_challenge(&f.pk.kzg,
			r_star, &wm, &zero, None).unwrap();
		let claim = IndividualClaim::<Bn254>{ i, kzg_word: c_star,
			ref_batch_claim: f.claims[i].ref_batch_claim.clone() };
		//open with the forger's ch, and with the verifier's ch for bp
		let ch_bp = T932Bp::ind_combiner(&pc, &bp.vcom_vec_r,
			&bp.vcom_vec_v, r_star, v_star);
		for (name, c) in [("forger ch", ch), ("verifier ch", ch_bp)] {
			let mut vec_c = si2.vec_r.iter().zip(si2.vec_v.iter())
				.map(|(a,b)| *a + c * *b)
				.collect::<Vec<Fr>>();
			vec_c.push(si2.r_vec_r + c * si2.r_vec_v);
			vec_c.push(si2.r_vec_r2 + c * si2.r_vec_v2);
			let vcom_prf = VecCom::<Bn254>::prove_with_challenge(
				&f.pk.vec, f.pk.vec.get_idx(i), &vec_c, &zero, None)
				.unwrap();
			let prf = IndividualProof::<Bn254>{ vcom_prf,
				v_i: v_star, kzg_prf: kzg_prf.clone() };
			assert!(!T932Bp::verify_individual(&f.vk, i, &claim, &f.gc,
				&bp, &prf, None, "test-6b", false),
				"combiner forgery ACCEPTED ({})", name);
		}
	}

	/// print_size() must equal the true compressed serialized length.
	#[test]
	fn individual_proof_size_matches_serialization(){
		use ark_serialize::CanonicalSerialize;
		let g = G1::generator();
		let p = super::IndividualProof::<Bn254>{
			vcom_prf: super::veccom::Proof{ eval: Fr::zero(), proof: g },
			v_i: Fr::zero(),
			kzg_prf: super::kzg::Proof{ eval: Fr::zero(), proof: g },
		};
		let reported = p.print_size();
		// independent ground truth: serialize each leaf, sum the lengths
		let mut buf = Vec::new();
		p.vcom_prf.eval.serialize_compressed(&mut buf).unwrap();
		p.vcom_prf.proof.serialize_compressed(&mut buf).unwrap();
		p.v_i.serialize_compressed(&mut buf).unwrap();
		p.kzg_prf.eval.serialize_compressed(&mut buf).unwrap();
		p.kzg_prf.proof.serialize_compressed(&mut buf).unwrap();
		assert_eq!(reported, buf.len(),
			"IndividualProof size estimate != serialized bytes");
	}

	/// Same for a fully-populated (part-2 added) BatchProof.
	#[test]
	fn batch_proof_size_matches_serialization(){
		use ark_serialize::CanonicalSerialize;
		use ark_ec::CurveGroup;
		let g = G1::generator();
		let kzg = || super::kzg::Proof::<G1>{ eval: Fr::zero(), proof: g };
		let mut p = super::BatchProof::<Bn254, Groth16<Bn254>>{
			vcom_vec_v: g, kzg_vec_v: g, vcom_vec_r: g, kzg_vec_r: g,
			prf_qa_nizk: super::QaNizkProof{ prf: g },
			ch: Fr::zero(), rc: Fr::zero(),
			agg_kzg_prf: kzg(),
			kzg_all_com1: None, kzg_all_com_prf1: None,
			kzg_all_com2: None, kzg_all_com_prf2: None,
			comE2: None, comW2: None, comF2: None, qa_nizk_prf2: None,
			snark_proof_main: None, snark_proof_cp: None, mainres_hash: None,
			hash_cmF: Fr::zero(),
		};
		// Groth16 Proof has no Default; build from affine generators.
		let a = G1::generator().into_affine();
		let b = ark_bn254::G2Projective::generator().into_affine();
		let g16 = ark_groth16::Proof::<Bn254>{ a, b, c: a, d: a };
		p.add_part2(g, kzg(), g, kzg(),
			g, g, g, super::QaNizkProof{ prf: g },
			g16.clone(), g16, Fr::zero());
		let reported = p.print_size();
		// independent ground truth: serialize each field in print_size order
		let mut buf = Vec::new();
		p.vcom_vec_v.serialize_compressed(&mut buf).unwrap();
		p.kzg_vec_v.serialize_compressed(&mut buf).unwrap();
		p.vcom_vec_r.serialize_compressed(&mut buf).unwrap();
		p.kzg_vec_r.serialize_compressed(&mut buf).unwrap();
		p.prf_qa_nizk.prf.serialize_compressed(&mut buf).unwrap();
		p.ch.serialize_compressed(&mut buf).unwrap();
		p.rc.serialize_compressed(&mut buf).unwrap();
		p.agg_kzg_prf.eval.serialize_compressed(&mut buf).unwrap();
		p.agg_kzg_prf.proof.serialize_compressed(&mut buf).unwrap();
		p.kzg_all_com1.as_ref().unwrap()
			.serialize_compressed(&mut buf).unwrap();
		{ let pr = p.kzg_all_com_prf1.as_ref().unwrap();
			pr.eval.serialize_compressed(&mut buf).unwrap();
			pr.proof.serialize_compressed(&mut buf).unwrap(); }
		p.kzg_all_com2.as_ref().unwrap()
			.serialize_compressed(&mut buf).unwrap();
		{ let pr = p.kzg_all_com_prf2.as_ref().unwrap();
			pr.eval.serialize_compressed(&mut buf).unwrap();
			pr.proof.serialize_compressed(&mut buf).unwrap(); }
		p.comE2.as_ref().unwrap().serialize_compressed(&mut buf).unwrap();
		p.comW2.as_ref().unwrap().serialize_compressed(&mut buf).unwrap();
		p.comF2.as_ref().unwrap().serialize_compressed(&mut buf).unwrap();
		p.qa_nizk_prf2.as_ref().unwrap().prf
			.serialize_compressed(&mut buf).unwrap();
		p.snark_proof_main.as_ref().unwrap()
			.serialize_compressed(&mut buf).unwrap();
		p.snark_proof_cp.as_ref().unwrap()
			.serialize_compressed(&mut buf).unwrap();
		p.mainres_hash.as_ref().unwrap()
			.serialize_compressed(&mut buf).unwrap();
		p.hash_cmF.serialize_compressed(&mut buf).unwrap();
		assert_eq!(reported, buf.len(),
			"BatchProof size estimate != serialized bytes");
	}

	/// S121: the per-word pads and the two vector nonces must be fresh
	/// draws; rayon::iter::repeat clones ONE value into every slot.
	#[test]
	fn snark_advice_nonces_are_distinct(){
		use std::collections::HashSet;
		type CS1E = KZG<'static, Bn254>;
		let mut words = vec![];
		let n_words = 20;
		let mut rng = &mut test_rng();
		for _i in 0..n_words{
			let mut word = vec![];
			for _j in 0..2{ word.push(Fr::rand(&mut rng)); }
			words.push(word);
		}
		let lk = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)), //0, null entry
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]);
		let lkup = Arc::new(lk);

		let keysize = BatchProcessor::<Bn254,
			LookupTableTwoCol_Inst<Fr>, Groth16<Bn254>, CS1E, false>
			::key_size(&words);
		let (pk, _vk) = BatchProcessor::<Bn254,
			LookupTableTwoCol_Inst<Fr>, Groth16<Bn254>, CS1E, false>
			::setup(&mut rng, keysize, n_words,
				poseidon_canonical_config::<Fr>(), 0, &lkup);
		let (_gc, _ic, si) = BatchProcessor::<Bn254,
			LookupTableTwoCol_Inst<Fr>, Groth16<Bn254>, CS1E, false>
			::gen_claims(&pk, &mut rng, &words).unwrap();

		assert_eq!(si.rands.len(), n_words, "rands length changed");
		let uniq: HashSet<Fr> = si.rands.iter().cloned().collect();
		assert_eq!(uniq.len(), n_words,
			"per-word rands are not pairwise distinct");
		assert!(si.r_vec_r != si.r_vec_v,
			"r_vec_r and r_vec_v are the same draw");
		//T933 s9: rands2 and the four second nonces are fresh too
		assert_eq!(si.rands2.len(), n_words, "rands2 length changed");
		let uniq: HashSet<Fr> = si.rands.iter().chain(si.rands2.iter())
			.cloned().collect();
		assert_eq!(uniq.len(), 2*n_words,
			"rands and rands2 are not pairwise distinct");
		let nonces: HashSet<Fr> = [si.r_all_words, si.r_all_words2,
			si.r_kzg_len, si.r_kzg_len2, si.r_vec_r, si.r_vec_r2,
			si.r_vec_v, si.r_vec_v2].into_iter().collect();
		assert_eq!(nonces.len(), 8, "the eight nonces are not distinct");
		//T933 s9 review N1. Distinctness alone lets one zero blind
		//through, which drops a commitment back to one blind.
		assert!(si.rands.iter().chain(si.rands2.iter())
			.chain(nonces.iter()).all(|x| !x.is_zero()),
			"a blind or nonce is zero");
	}

	/// T933 s10 table A, the public table handed to setup.
	fn s10_table_a() -> LookupTableTwoCol_Inst<Fr>{
		LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))])
	}

	/// T933 s10. A cheating prover swaps the public table A for its own
	/// table lk_b. Everything else is honest. It commits lk_b in the
	/// claim exactly as gen_claims commits a table (columns reversed,
	/// blind zero) and proves the batch against lk_b, so the
	/// Fiat-Shamir input and the aggregated KZG opening are consistent.
	/// Returns the verify_batch verdict.
	fn s10_forged_table(lk_b: LookupTableTwoCol_Inst<Fr>,
		ctx: &'static str) -> bool{
		let mut rng = test_rng();
		let words: Vec<Vec<Fr>> = (0..20).map(|_|
			vec![Fr::rand(&mut rng), Fr::rand(&mut rng)]).collect();
		let cfg = poseidon_canonical_config::<Fr>();
		let (pk, vk) = T932Bp::setup(&mut rng, T932Bp::key_size(&words),
			words.len(), cfg.clone(), 0, &s10_table_a());
		let (mut gc, _claims, si) = T932Bp::gen_claims(&pk, &mut rng,
			&words).unwrap();
		let (mut c1, mut c2) = lk_b.get_cols();
		c1.reverse();
		c2.reverse();
		gc.kzg_lk_col1 = KZG::<Bn254>::commit(&pk.kzg, &c1, &Fr::zero())
			.unwrap();
		gc.kzg_lk_col2 = KZG::<Bn254>::commit(&pk.kzg, &c2, &Fr::zero())
			.unwrap();
		let g1 = G1::generator();
		let partial = SnarkRandInput::<Bn254>{
			kzg_all_words: gc.kzg_all_words, kzg_length: gc.kzg_length,
			kzg_lk_col1: gc.kzg_lk_col1, kzg_lk_col2: gc.kzg_lk_col2,
			hash_cmF: Fr::zero(), kzg_vec_r: g1, kzg_vec_v: g1,
			poseidon_config: cfg.clone()};
		let (bp, _) = T932Bp::prove_batch(&pk, &si, &words,
			Arc::new(lk_b), &partial);
		T932Bp::verify_batch(&vk, None, None, None, None, &gc, &bp, &cfg,
			false, None, None, ctx)
	}

	/// T933 s10 (paper Fig 16 (1)). Table B differs from A in one row.
	/// The control run with table A must still pass, so a rejection is
	/// due to the table and not to a broken fixture.
	#[test]
	fn batch_rejects_foreign_lkup(){
		assert!(s10_forged_table(s10_table_a(), "test-s10-ctrl"),
			"T933 s10: honest table A rejected");
		let lk_b = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(2u32))]);
		assert!(!s10_forged_table(lk_b, "test-s10-foreign"),
			"T933 s10: foreign lookup table ACCEPTED");
	}

	/// T933 s10. The two columns of A swapped, proved consistently.
	/// The check must bind each commitment to its column, not the pair
	/// as a set.
	#[test]
	fn batch_rejects_swapped_lkup_cols(){
		let (c1, c2) = s10_table_a().get_cols();
		assert!(c1 != c2, "swap must change the table");
		let lk_sw = LookupTableTwoCol_Inst::new(
			c2.into_iter().zip(c1.into_iter()).collect());
		assert!(!s10_forged_table(lk_sw, "test-s10-swap"),
			"T933 s10: swapped lookup columns ACCEPTED");
	}

	/// T933 s10. driver2 (Phase 2, full mode) builds its batch keys from
	/// LK::new(vec![]). setup must not panic on the empty table.
	#[test]
	fn setup_accepts_empty_lkup(){
		let mut rng = test_rng();
		let (pk, vk) = T932Bp::setup(&mut rng, 8, 2,
			poseidon_canonical_config::<Fr>(), 0,
			&LookupTableTwoCol_Inst::new(vec![]));
		assert!(pk.lk_cm1.is_zero() && pk.lk_cm2.is_zero());
		assert!(vk.lk_cm1 == pk.lk_cm1 && vk.lk_cm2 == pk.lk_cm2);
	}

	/// T933 s9 one-blind guess test on (C, v). g is a guess in
	/// coefficient order with zeros in its blind slots. With one
	/// unknown blind o at X^j, C - [g(s)]_1 = o [s^j]_1 and
	/// v - g(r) = o r^j, so one MSM confirms g. Tried for j < max(k, 1).
	fn t933_x0_hit(kzg: &crate::commitment::kzg::ProverKey<'static, G1>,
		c: G1, v: Fr, r: Fr, g: &Vec<Fr>, k: usize) -> bool{
		use std::ops::Mul;
		use ark_ff::Field;
		let cg = KZG::<Bn254>::commit(kzg, g, &Fr::zero()).unwrap();
		let vg = poly_from_vec(g.clone()).unwrap().evaluate(&r);
		(0..k.max(1)).any(|j| c - cg == kzg.powers_of_g[j]
			.mul((v - vg) * r.pow([j as u64]).inverse().unwrap()))
	}

	/// T933 s9 attacker vector: data with k zero blinds appended, then
	/// reversed (coefficient order), as every KZG vector here.
	fn t933_guess_vec(data: &[Fr], k: usize) -> Vec<Fr>{
		let mut g = data.to_vec();
		g.extend(std::iter::repeat(Fr::zero()).take(k));
		g.reverse();
		g
	}

	/// T933-B1 (Issue 8, F2). The guess test. For 1000 words, the
	/// one-blind test of t933_x0_hit with k = 1..=3 zero blind slots
	/// never confirms the true word or a wrong guess. k = 1 is the
	/// one-blind layout, where the X^0 test confirms every true word. Repeated on the
	/// aggregate opening of the six batch commitments (k = 1..=2), with
	/// each per-word blind taken from (C_i, v_i) as a one-blind attacker
	/// would.
	#[test]
	fn t933_b1_guess_test(){
		let n = 1000;
		let f = t932w_fix(n, 2, 2);
		//not test_rng(): its stream would replay the fixture's words
		use ark_std::rand::{rngs::StdRng, SeedableRng};
		let mut rng = StdRng::seed_from_u64(0x933);
		let si = &f.snark_inp;
		let mut bad: Vec<String> = vec![];
		for k in 1..=3usize{
			let (mut hit_t, mut hit_w) = (0usize, 0usize);
			for i in 0..n{
				let (c, r, v) = (f.ind_claims[i].kzg_word, si.vec_r[i],
					si.vec_v[i]);
				let w = &f.words[i];
				let mut lw = vec![Fr::from(w.len() as u32)];
				lw.extend_from_slice(w);
				if t933_x0_hit(&f.pk.kzg, c, v, r,
					&t933_guess_vec(&lw, k), k) {hit_t += 1;}
				let mut lw2 = vec![Fr::from(w.len() as u32)];
				lw2.extend((0..w.len()).map(|_| Fr::rand(&mut rng)));
				if t933_x0_hit(&f.pk.kzg, c, v, r,
					&t933_guess_vec(&lw2, k), k) {hit_w += 1;}
			}
			if hit_t + hit_w > 0 {bad.push(format!("per-word, {} blind \
				slot(s): {}/{} true words, {}/{} wrong guesses confirmed",
				k, hit_t, n, hit_w, n));}
		}
		//aggregate: sum_j rc^j C_j opened at ch to y = agg eval
		let bp = &f.batch_proof;
		let (ch, rc, y) = (bp.ch, bp.rc, bp.agg_kzg_prf.eval);
		let cms = [f.global_claim.kzg_lk_col1, f.global_claim.kzg_lk_col2,
			f.global_claim.kzg_all_words, f.global_claim.kzg_length,
			bp.kzg_vec_r, bp.kzg_vec_v];
		let lk = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]);
		let (lk1, lk2) = lk.get_cols();
		let mut wrong = f.words.clone();
		wrong[0][0] += Fr::from(1u32);
		//k <= 2: a third slot per word overflows the key
		for k in 1..=2usize{
			for (name, ws) in [("true", &f.words), ("wrong", &wrong)]{
				//each word's blind slots: zeros, then at X^0 the residual
				//v_i - g_i(r_i), which IS the blind in a one-blind layout
				let mut all_w: Vec<Fr> = vec![];
				for (i, w) in ws.iter().enumerate(){
					let mut lw = vec![Fr::from(w.len() as u32)];
					lw.extend_from_slice(w);
					let e = si.vec_v[i] - poly_from_vec(
						t933_guess_vec(&lw, k)).unwrap().evaluate(&si.vec_r[i]);
					all_w.extend_from_slice(w);
					all_w.extend(std::iter::repeat(Fr::zero()).take(k-1));
					all_w.push(e);
				}
				let lens: Vec<Fr> = ws.iter()
					.map(|w| Fr::from(w.len() as u32)).collect();
				let gs = [t933_guess_vec(&lk1, 0), t933_guess_vec(&lk2, 0),
					t933_guess_vec(&all_w, k), t933_guess_vec(&lens, k),
					t933_guess_vec(&si.vec_r, k),
					t933_guess_vec(&si.vec_v, k)];
				let (mut c, mut g, mut f_rc) = (G1::zero(), vec![], Fr::from(1u32));
				for j in 0..6{
					c += cms[j] * f_rc;
					let gj: Vec<Fr> = gs[j].iter().map(|x| *x * f_rc).collect();
					if g.len() < gj.len() {g.resize(gj.len(), Fr::zero());}
					for (a, b) in g.iter_mut().zip(gj.iter()) {*a += b;}
					f_rc *= rc;
				}
				if t933_x0_hit(&f.pk.kzg, c, y, ch, &g, 1) {bad.push(format!(
					"aggregate, {} blind slot(s): {} guess confirmed",
					k, name));}
			}
		}
		assert!(bad.is_empty(), "T933-B1: X^0 guess test confirms: {:?}",
			bad);
	}

	/// T933-B1 (s9), trapdoor half. setup draws the KZG trapdoor s
	/// first, so a fresh test_rng() replays it. Each C_i is
	/// [p(s)]_1 with p = reverse((len, w) || o_1 || o_2). For every
	/// guess g (blind slots zero) the pair o_2 + o_1 X with
	/// o_2 + o_1 s = p(s) - g(s) and o_2 + o_1 r_i = v_i - g(r_i) is
	/// unique (s != r_i) and reproduces (C_i, v_i). For the true word it
	/// is (rands[i], rands2[i]).
	#[test]
	fn t933_b1_trapdoor_unique(){
		use ark_ff::Field;
		use std::ops::Mul;
		use ark_std::rand::{rngs::StdRng, SeedableRng};
		let n = 100;
		let mut wrng = StdRng::seed_from_u64(0x9331);
		let words: Vec<Vec<Fr>> = (0..n).map(|_|
			(0..2).map(|_| Fr::rand(&mut wrng)).collect()).collect();
		let s = Fr::rand(&mut test_rng());
		let mut rng = test_rng();
		let lkup = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(0u32)),
			(Fr::from(1u32), Fr::from(1u32))]);
		let (pk, _vk) = T932Bp::setup(&mut rng, T932Bp::key_size(&words),
			n, poseidon_canonical_config::<Fr>(), 0, &lkup);
		let g0 = pk.kzg.powers_of_g[0];
		assert!(pk.kzg.powers_of_g[1] == g0.mul(s),
			"trapdoor replay failed");
		let (_gc, claims, si) = T932Bp::gen_claims(&pk, &mut rng, &words)
			.unwrap();
		let ev = |v: &Vec<Fr>, x: Fr| poly_from_vec(v.clone()).unwrap()
			.evaluate(&x);
		for i in 0..n{
			let (c, r, v) = (claims[i].kzg_word, si.vec_r[i], si.vec_v[i]);
			let mut lw = vec![Fr::from(2u32)];
			lw.extend_from_slice(&words[i]);
			let mut full = lw.clone();
			full.push(si.rands[i]);
			full.push(si.rands2[i]);
			full.reverse();
			let p_s = ev(&full, s);
			assert!(c == g0.mul(p_s), "T933-B1: C_i is not \
				reverse((len, w) || o_1 || o_2)");
			assert!(s != r);
			let mut lw2 = lw.clone();
			lw2[1] += Fr::from(1u32);
			for (name, gw) in [("true", &lw), ("wrong", &lw2)]{
				let g = t933_guess_vec(gw, 2);
				let (d1, d2) = (p_s - ev(&g, s), v - ev(&g, r));
				let o1 = (d1 - d2) * (s - r).inverse().unwrap();
				let o2 = d1 - o1 * s;
				let mut gb = g.clone();
				gb[0] += o2;
				gb[1] += o1;
				assert!(KZG::<Bn254>::commit(&pk.kzg, &gb, &Fr::zero())
					.unwrap() == c && ev(&gb, r) == v,
					"T933-B1: {} guess has no blind pair", name);
				if name == "true" {
					assert!(o1 == si.rands[i] && o2 == si.rands2[i],
						"T933-B1: true guess pair is not (o_1, o_2)");
				}
			}
		}
	}

	/// T934-6 toy: x public, w = x^2 first (so the range starts at 1),
	/// then a_i (committed when `commit`) and b_i = a_i (a_i + x). mode 1
	/// adds an unconstrained committed wire, mode 2 uses a_0, a_1 only
	/// as a sum: both must trip the R9 setup assert.
	struct T934Toy { commit: bool, mode: u8 }
	impl ark_relations::r1cs::ConstraintSynthesizer<Fr> for T934Toy {
		fn generate_constraints(self, cs: ark_relations::r1cs::ConstraintSystemRef<Fr>)
			-> ark_relations::r1cs::Result<()> {
			use ark_relations::{lc, r1cs::Variable};
			let (xv, av) = (Fr::from(3u64), (1..=4u64).map(Fr::from).collect::<Vec<_>>());
			let x = cs.new_input_variable(|| Ok(xv))?;
			let w = cs.new_witness_variable(|| Ok(xv * xv))?;
			cs.enforce_constraint(lc!() + x, lc!() + x, lc!() + w)?;
			let s0 = cs.num_witness_variables();
			let a = av.iter().map(|v| cs.new_witness_variable(|| Ok(*v)))
				.collect::<Result<Vec<Variable>, _>>()?;
			if self.mode == 1 { cs.new_witness_variable(|| Ok(xv))?; }
			if self.commit { cs.set_committed(s0, cs.num_witness_variables() - s0); }
			let k = if self.mode == 2 {
				let v = cs.new_witness_variable(|| Ok(av[0] + av[1]))?;
				cs.enforce_constraint(lc!() + a[0] + a[1], lc!() + Variable::One, lc!() + v)?;
				2 } else { 0 };
			for i in k..a.len() {
				let b = cs.new_witness_variable(|| Ok(av[i] * (av[i] + xv)))?;
				cs.enforce_constraint(lc!() + a[i], lc!() + a[i] + x, lc!() + b)?;
			}
			Ok(())
		}
	}
	type G16 = Groth16<Bn254>;

	/// T934-6: m = 0 is stock Groth16. The hex is the (A, B, C) that
	/// registry ark-groth16 0.4.0 gives for this toy under test_rng.
	#[test]
	fn t934_fork_m0_matches_stock(){
		use ark_serialize::CanonicalSerialize;
		use ark_snark::SNARK;
		use ark_ec::AffineRepr;
		let mut rng = test_rng();
		let toy = || T934Toy{ commit: false, mode: 0 };
		let pk = G16::generate_random_parameters_with_reduction(toy(), &mut rng).unwrap();
		let p = G16::create_random_proof_with_reduction(toy(), &pk, &mut rng).unwrap();
		let mut buf = vec![];
		(p.a, p.b, p.c).serialize_compressed(&mut buf).unwrap();
		assert_eq!(buf.iter().map(|b| format!("{:02x}", b)).collect::<String>(),
			"3acfa678f25ab9d770350edb0d050c714919b0849ec0d2a6e780e0f305000511e496af15d3d8e19e83e0773dc05d2a0bd7d6e74b67c83fbdba6d90ebce94e1230bdfd3cd3cb27443c916b22b940c617655fed8e80c3cd62b32d3c560b36d07190f09558f5bb895ce0caf2db65a6df1e1fdfb3b06d36995dd239f458356015eab");
		assert!(p.d.is_zero() && pk.n_commit == 0 && G16::verify(&pk.vk, &[Fr::from(3u64)], &p).unwrap());
	}

	/// T934-6: D binds, hides, cannot absorb a public-basis shift, d_pre
	/// reproduces the internal D, and setup / prover asserts fire.
	#[test]
	fn t934_fork_cp(){
		use ark_snark::SNARK;
		use ark_ec::CurveGroup;
		use ark_std::One;
		let mut rng = test_rng();
		let x = Fr::from(3u64);
		let toy = |mode| T934Toy{ commit: true, mode };
		let pk = G16::generate_random_parameters_with_reduction(toy(0), &mut rng).unwrap();
		assert_eq!((pk.commit_start, pk.n_commit, pk.d_query.len()), (1, 4, 4));
		let v = |p: &ark_groth16::Proof<Bn254>, x: Fr| G16::verify(&pk.vk, &[x], p).unwrap();
		let mut prove = || G16::create_random_proof_with_reduction(toy(0), &pk, &mut rng).unwrap();
		let (p1, p2) = (prove(), prove());
		assert!(v(&p1, x) && v(&p2, x) && p1.d != p2.d, "T934-6: honest / hiding");
		let mut t = p1.clone();
		t.d = (t.d + G1::generator()).into_affine();
		assert!(!v(&t, x), "T934-6: tampered D accepted");
		t.d = (p1.d + pk.vk.gamma_abc_g1[1]).into_affine();
		assert!(!v(&t, x - Fr::one()), "T934-6: D shifted by gamma_abc_g1[1] accepted");
		let (r, s, kappa) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
		let d = G16::cp_commit(&pk, &(1..=4u64).map(Fr::from).collect::<Vec<_>>(), kappa);
		let q = G16::create_proof_with_reduction(toy(0), &pk, r, s, kappa, None).unwrap();
		assert!(q == G16::create_proof_with_reduction(toy(0), &pk, r, s, kappa, Some(d)).unwrap()
			&& v(&q, x), "T934-6: d_pre != internal D");
		let d2 = G16::cp_commit(&pk, &(2..=5u64).map(Fr::from).collect::<Vec<_>>(), kappa);
		assert!(!v(&G16::create_proof_with_reduction(toy(0), &pk, r, s, kappa, Some(d2)).unwrap(), x),
			"T934-6: D over another a_S accepted");
		let panics = |f: &dyn Fn(), msg: &str| std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
			.err().map_or(false, |e| e.downcast_ref::<String>().map(String::as_str)
			.or(e.downcast_ref::<&str>().copied()).map_or(false, |s| s.contains(msg)));
		assert!(panics(&|| { let _ = G16::create_random_proof_with_reduction(
			T934Toy{ commit: false, mode: 0 }, &pk, &mut test_rng()); }, "committed range"),
			"T934-6: prover took a circuit whose range != pk");
		for m in [1, 2] {
			assert!(panics(&|| { let _ = G16::generate_random_parameters_with_reduction(toy(m), &mut test_rng()); }, "R9"),
				"T934-6: R9 setup assert missed mode {}", m);
		}
	}

	/// T934 key IO (A2): write / read round trip with the T934 fields, m = 4 and m = 0.
	#[test]
	fn t934_key_io(){
		use ark_snark::SNARK;
		use crate::folding::foldpot::utils::{write_g16_optimized_bn254, read_g16_optimized_bn254};
		let dir = std::env::temp_dir().join(format!("t934_key_io_{}", std::process::id()));
		std::fs::create_dir_all(&dir).unwrap();
		for commit in [true, false] {
			let (mut rng, toy) = (test_rng(), || T934Toy{ commit, mode: 0 });
			let pk = G16::generate_random_parameters_with_reduction(toy(), &mut rng).unwrap();
			let path = dir.join(format!("g16_{}.key", commit));
			write_g16_optimized_bn254(&path, &pk, &pk.vk, Fr::from(5u64));
			let (pk2, vk2, pp) = read_g16_optimized_bn254(&path);
			let p = G16::create_random_proof_with_reduction(toy(), &pk2, &mut rng).unwrap();
			assert!(pk2 == pk && vk2 == pk.vk && pp == Fr::from(5u64) && G16::verify(&vk2, &[Fr::from(3u64)], &p).unwrap(),
				"T934: key IO round trip, commit = {}", commit);
		}
		std::fs::remove_dir_all(&dir).unwrap();
	}

	/// T934 D2 (T-META): write a key at pp_hash X = 5, read it (with the
	/// .meta version patched to `ver` when Some) and check it against `chk`.
	fn t934_meta(tag: &str, chk: Fr, ver: Option<u32>){
		use crate::folding::foldpot::utils::{write_g16_optimized_bn254, read_g16_optimized_bn254, check_g16_pp_hash};
		let dir = std::env::temp_dir().join(format!("t934_meta_{}_{}", tag, std::process::id()));
		std::fs::create_dir_all(&dir).unwrap();
		let pk = G16::generate_random_parameters_with_reduction(T934Toy{ commit: true, mode: 0 }, &mut test_rng()).unwrap();
		let path = dir.join("g16.key");
		write_g16_optimized_bn254(&path, &pk, &pk.vk, Fr::from(5u64));
		if let Some(v) = ver {
			let m = dir.join("g16.key.meta");
			let mut b = std::fs::read(&m).unwrap();
			b[..4].copy_from_slice(&v.to_le_bytes());
			std::fs::write(&m, b).unwrap();
		}
		let r = std::panic::catch_unwind(|| read_g16_optimized_bn254(&path));
		std::fs::remove_dir_all(&dir).unwrap();
		let (pk2, _, pp) = r.unwrap_or_else(|e| std::panic::resume_unwind(e));
		assert!(pk2 == pk, "T934 D2: key round trip");
		check_g16_pp_hash(&path, pp, chk);
	}
	#[test]
	fn t934_meta_ok(){ t934_meta("ok", Fr::from(5u64), None) }
	#[test]
	#[should_panic(expected = "missing or stale")]
	fn t934_meta_pp(){ t934_meta("pp", Fr::from(6u64), None) }
	#[test]
	#[should_panic(expected = "missing or stale")]
	fn t934_meta_v2(){ t934_meta("v2", Fr::from(5u64), Some(2)) }

	/// T940 circuit: inputs x, y and `n` rounds of FpVar arithmetic (nested
	/// symbolic LCs with constants), a bit decomposition every 256 rounds.
	/// `bad` breaks the last row.
	struct T940Circ { n: usize, bad: bool }
	impl ark_relations::r1cs::ConstraintSynthesizer<Fr> for T940Circ {
		fn generate_constraints(self, cs: ark_relations::r1cs::ConstraintSystemRef<Fr>)
			-> ark_relations::r1cs::Result<()> {
			use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, R1CSVar, ToBitsGadget};
			let x = FpVar::new_input(cs.clone(), || Ok(Fr::from(3u64)))?;
			let y = FpVar::new_input(cs.clone(), || Ok(Fr::from(5u64)))?;
			let mut acc = FpVar::new_witness(cs.clone(), || Ok(Fr::from(7u64)))?;
			for i in 0..self.n {
				acc = (&acc + &x) * (&acc - &y + Fr::from(i as u64)) * Fr::from(2u64) + &y;
				if i % 256 == 0 { let _ = acc.to_bits_le()?; }
			}
			let out = FpVar::new_witness(cs, || Ok(acc.value()? + Fr::from(self.bad as u64)))?;
			out.enforce_equal(&acc)
		}
	}

	/// T940: Eager rows equal the matrices times z, the UNSAT verdicts agree,
	/// and `witness_map_from_evals` (input rows included) equals `witness_map`.
	#[test]
	fn t940_eager_rows(){
		use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisMode};
		use ark_groth16::r1cs_to_qap::{evaluate_constraint, LibsnarkReduction, R1CSToQAP};
		type D = ark_poly::GeneralEvaluationDomain<Fr>;
		for (n, bad) in [(3, false), (3, true), (600, false)] {
			let cs_m = ConstraintSystem::<Fr>::new_ref();
			T940Circ{ n, bad }.generate_constraints(cs_m.clone()).unwrap();
			cs_m.finalize();
			let cs_e = ConstraintSystem::<Fr>::new_ref();
			cs_e.set_mode(SynthesisMode::Eager);
			T940Circ{ n, bad }.generate_constraints(cs_e.clone()).unwrap();
			let unsat = cs_e.which_is_unsatisfied().unwrap();
			assert!(unsat == cs_m.which_is_unsatisfied().unwrap() && unsat.is_some() == bad,
				"T940: Eager UNSAT verdict, n = {}, bad = {}", n, bad);
			let (az, bz, cz) = cs_e.borrow_mut().unwrap().take_rows();
			let mats = cs_m.to_matrices().unwrap();
			let m = cs_m.borrow().unwrap();
			let z = [m.instance_assignment.as_slice(), m.witness_assignment.as_slice()].concat();
			let mz = |rows: &Vec<Vec<(Fr, usize)>>| rows.iter()
				.map(|r| evaluate_constraint(r, &z)).collect::<Vec<Fr>>();
			assert!(az == mz(&mats.a) && bz == mz(&mats.b) && cz == mz(&mats.c),
				"T940: Eager rows != matrices * z, n = {}", n);
			drop(m);
			let h_e = LibsnarkReduction::witness_map_from_evals::<Fr, D>(az, bz, cz,
				&cs_e.borrow().unwrap().instance_assignment).unwrap();
			assert!(h_e == LibsnarkReduction::witness_map::<Fr, D>(cs_m).unwrap(),
				"T940: h from Eager rows != h from matrices, n = {}", n);
		}
	}

	/// T940: the Eager prover gives the matrices-path proof for the same r, s,
	/// on a toy and a 2^16+ row circuit, and the proof verifies.
	#[test]
	fn t940_eager_proof_eq(){
		use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
		use ark_snark::SNARK;
		assert!(std::env::var_os("ZKR_G16_NO_EAGER").is_none(), "T940: unset ZKR_G16_NO_EAGER");
		let mut rng = test_rng();
		for n in [3, 20000] {
			let circ = || T940Circ{ n, bad: false };
			let pk = G16::generate_random_parameters_with_reduction(circ(), &mut rng).unwrap();
			let (r, s) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
			let p = G16::create_proof_with_reduction(circ(), &pk, r, s, Fr::zero(), None).unwrap();
			let cs = ConstraintSystem::<Fr>::new_ref();
			circ().generate_constraints(cs.clone()).unwrap();
			cs.finalize();
			let c = cs.borrow().unwrap();
			let z = [c.instance_assignment.as_slice(), c.witness_assignment.as_slice()].concat();
			let q = G16::create_proof_with_reduction_and_matrices(&pk, r, s, &cs.to_matrices().unwrap(),
				c.num_instance_variables, c.num_constraints, &z).unwrap();
			assert!(n < 1000 || c.num_constraints >= 1 << 16, "T940: big circuit too small");
			assert!(p == q && G16::verify(&pk.vk, &[Fr::from(3u64), Fr::from(5u64)], &p).unwrap(),
				"T940: Eager proof != matrices proof, n = {}", n);
		}
	}
}
