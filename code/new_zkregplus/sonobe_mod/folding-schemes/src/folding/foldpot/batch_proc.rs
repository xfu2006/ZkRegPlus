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
	logger::{log_perf, emit_stdout, LOG1},
};
use core::marker::PhantomData;
use crate::folding::foldpot::{
	veccom::{VecCom},
	veccom,
	qa_nizk::{setup_qa_nizk_standard, Matrix, QaNizkProverParams,
		QaNizkVerifierParams, prove_qa_nizk_fast,
		QaNizkProof, verify_qa_nizk},
	sigma_ir1cs::{LookupTableTwoCol},
	decider_eth_circuit_super::{CircPubInput},
	from_field::{AffineFromField},
	utils::{B_DEBUG,get_mem_usage_mb,mb2s},
};
use crate::transcript::AbsorbNonNative;
use crate::utils::vec::poly_from_vec;

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
}


/// The claim: kzg_all_words commits to the concatenation of all words.
/// then the length array decides the words. (1) the total sum of the
/// lengths match the length of combined words. (2) each word
/// is malware free (regarding the regex signatures).
///
/// Note1: it is very likely in practice that the 
/// combined word CONTAINS instances
/// of malware, but none of the individual word does. That's the reason
/// we do the dinvidual proof. 
/// Note2: KZG commitment and vcom_commitment is 1-leaky. It's accomplished
/// by padding a random, just like halo2(plonk) and Lunar. 
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
/// Total: 16G1 + 1G2 +  7F
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
	// for the decider circuit (circ1 part), will be part of i/o of snark prf
	pub kzg_all_com_ch1: Option<E::ScalarField>,
	/// proof kzg_all_com1
	/// the corresponding proof (it contains eval_w_e1)
	pub kzg_all_com_prf1: Option<kzg::Proof<E::G1>>,

	/// kzg of all w and e for circ2
	pub kzg_all_com2: Option<E::G1>,
	// for the decider circuit (circ2 part), will be part of i/o of snark prf
	pub kzg_all_com_ch2: Option<E::ScalarField>,
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
		kzg_all_com_ch1: E::ScalarField,
		kzg_all_com_prf1: kzg::Proof<E::G1>,

		kzg_all_com2: E::G1,
		kzg_all_com_ch2: E::ScalarField,
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
		self.kzg_all_com_ch1 = Some(kzg_all_com_ch1);
		self.kzg_all_com_prf1 = Some(kzg_all_com_prf1);

		self.kzg_all_com2 = Some(kzg_all_com2);
		self.kzg_all_com_ch2 = Some(kzg_all_com_ch2);
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
	/// the nonce for kzg_all_words
	pub r_all_words: F,
	/// the nonce for kzg_len
	pub r_kzg_len: F,
	/// random nonce for vec_r (for vec com)
	pub r_vec_r: F,
	/// random nonce for vec_r (for kzg )
	pub r_vec_r_kzg: F,
	/// nonce for hiding vec_v (for vec_com)
	pub r_vec_v: F,
	/// nonce for hiding vec_v (for kzg)
	pub r_vec_v_kzg: F,
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
			r_all_words: zero,
			r_kzg_len: zero,
			r_vec_r: zero,
			r_vec_r_kzg: zero,
			r_vec_v: zero,
			r_vec_v_kzg: zero,
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
	S: SNARK<F>, 
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
		n
	}

	/// set up the prover and verifier params
	/// max_total_n should be greater than the combined length of all words,
	/// and the lookup table size
	/// `job_id`: The ID of the job being processed.
	pub fn setup(mut rng: impl RngCore, max_total_n: usize, n_words: usize,
		poseidon_config: PoseidonConfig<F>, job_id: usize) 
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
		log_perf(job_id, logl, &format!("BatchProcessor step 2. setting up kzg: {}, INCREASED RAM now: {}. ", max_total_n, mb2s(m2-m1)), &mut gt);
		m1 = m2;

		let kzg_frag = KZG::<E>::pkey_in_affine(&kzg.0, n_words+1);
		//lg is for random blinding factor
		let lg= KZG::<E>::pkey_in_affine(&kzg.0, n_words+2)[n_words+1];

		let vec = VecCom::<E>::setup(&mut rng, n_words + 1).expect("vec setup fails"); 
		let mut vec_frag = VecCom::<E>::pkey_in_affine(&vec.0, n_words+1);
		vec_frag.reverse(); //because it's order is the REVERSE
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 3. setting up veccom: {}, INCREASED RAM: {} ", n_words, mb2s(m2-m1)), &mut gt);
		m1 = m2;

		//of the vector which generates kzg
		let vz = vec![ E::G1::zero().into_affine(); n_words + 1];
		//w will be [vec_r || vec_v]
		let matrix = vec![
			vec![kzg_frag.clone(), vz.clone(),vec![lg]].concat(), //-> kzg_vec_r
			vec![vec_frag.clone(), vz.clone(),vec![lg]].concat(), //-> vecom_vec_r 
			vec![vz.clone(), kzg_frag.clone(),vec![lg]].concat(), // -> kzg_vec_v 
			vec![vz.clone(), vec_frag.clone(),vec![lg]].concat(), // -> vecom_vec_v
		];
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 4. setting up matrix: {}, INCREASED RAM now: {}", (&matrix[0]).len(), mb2s(m2-m1)), &mut gt);
		m1 = m2;
		let mat = Matrix::<E::G1>{rows: matrix.len(), cols: matrix[0].len(), 
			matrix};
		let (pkey_qanizk, vkey_qanizk) = setup_qa_nizk_standard::<E>(&mat, b_debug);
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 5. setting up qa_nizk, INCREASED RAM: {}. ", mb2s(m2-m1)), &mut gt);

		let pkey = BatchProcessorProverParams::<'a, E>{
			kzg: kzg.0, vec: vec.0, 
			poseidon_config: poseidon_config.clone(),
			pk_qa_nizk: pkey_qanizk,
		};

	
		let qa_nizk_vkey_hash = vkey_qanizk.hash(&poseidon_config);
		let vkey = BatchProcessorVerifierParams::<'a, E,CS1E,H>{
			kzg: kzg.1, vec: vec.1, poseidon_config,
			vk_qa_nizk: vkey_qanizk,
			kzg_driver1: None,
			kzg_driver2: None,
			qa_nizk_vkey_hash: qa_nizk_vkey_hash, 
		};
		let m2 = get_mem_usage_mb();
		log_perf(job_id, logl, &format!("BatchProcessor step 5. setting up qa_nizk, INCREASED RAM: {}, TOTAL RAM now: {}. ", mb2s(m2-m0), mb2s(m2)), &mut gt2);
		(pkey, vkey)
	}

	/// return the batch claim, vector of individual claims,
	/// and the snark_input. Note that all vectors are REVERSED
	/// so that in circuit, using Homer's approach is easier.
	pub fn gen_claims(
		pkey: &BatchProcessorProverParams<'a,E>,
		rng: &mut impl RngCore,
		words: &Vec<Vec<F>>,
		lkup: Arc<LK>)
	-> Result<(BatchClaim<E>, Vec<IndividualClaim<E>>, 
		SnarkAdvice<F>), Error>{
		//1. generate the global claim
		let n_words = words.len();
		let (mut lk1, mut lk2) = lkup.get_cols();
		lk1.reverse();
		lk2.reverse();

		let zero = F::zero();
		let rands: Vec<F> = 
			rayon::iter::repeat( <E::G1 as Group>::ScalarField::rand(rng) ).
				take(n_words).collect();
		let r_all_words = <E::G1 as Group>::ScalarField::rand(rng);
		let r_kzg_len = <E::G1 as Group>::ScalarField::rand(rng);
		let all_words = words.concat();
		//here blind: zero (coz default kzg does not take blind anyway)
		let kzg_all_words = {
			let mut all_words2 = all_words.clone();
			all_words2.push(r_all_words);
			all_words2.reverse();
			KZG::<E>::commit(&pkey.kzg, &all_words2, &zero)?
		};
		assert!(words.len()==rands.len());

		let kzg_length = {
			let mut all_len:Vec<F> 
				= words.iter().map(|w| F::from(w.len() as u32)).collect();
			all_len.push(r_kzg_len);
			all_len.reverse();
			KZG::<E>::commit(&pkey.kzg, &all_len, &zero)?
		};
		let kzg_lk_col1 = KZG::<E>::commit(&pkey.kzg, &lk1, &zero)?;
		let kzg_lk_col2 = KZG::<E>::commit(&pkey.kzg, &lk2, &zero)?;
		let batch_claim = BatchClaim::<E>{kzg_all_words, kzg_length, kzg_lk_col1, kzg_lk_col2};

		//2. generate the individual claim
		let vec_idx = (0..n_words).collect::<Vec<usize>>();
		assert!(vec_idx.len()==n_words);
		let vec_kzg_words= words.par_iter().zip(rands.par_iter())
			.map(|(w, r)| {
				let mut w2 = w.clone();
				w2.push(*r);
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
				let mut w2 = w.clone();
				w2.push(r);
				w2.reverse();
				let p_i = poly_from_vec(w2).unwrap();
				let v_i = p_i.evaluate(&r_i);

				(r_i, v_i)
			}).collect::<Vec<(F,F)>>();
		let (vec_r, vec_v): (Vec<F>, Vec<F>) = vec_r_v.into_iter().unzip(); 

		let rs:Vec<E::ScalarField> = 
			rayon::iter::repeat(<E::G1 as Group>::ScalarField::rand(rng))
			.take(4).collect();
		let (r_vec_r, r_vec_r_kzg, r_vec_v, r_vec_v_kzg) =
			(rs[0], rs[1], rs[2], rs[3]);

		let snark_input = SnarkAdvice::<F>{
			rands, 
			r_all_words, r_kzg_len, r_vec_r, r_vec_v, r_vec_r_kzg, r_vec_v_kzg,
			vec_r, vec_v
		};

		Ok( (batch_claim, vec_ind_claims, snark_input) )
	}

	/// generate the individual proof for the i'th word (in SnarkAdvice)
	pub fn prove_individual(pkey: &BatchProcessorProverParams<'a,E>,
		snark_input: &SnarkAdvice<E::ScalarField>,
		words: &Vec<Vec<E::ScalarField>>,
		ind_claim: &IndividualClaim<E>,
		i: usize)->IndividualProof<E>{
		//1. retrieve r_i, v_i and compute ch for batched
		// verification of vec_r[r_i] and vec_v[v_i]
		assert!(i==ind_claim.i);	
		let r_i = snark_input.vec_r[i];
		let v_i = snark_input.vec_v[i];
		let mut sponge= PoseidonSponge::<E::ScalarField> 
			::new(&pkey.poseidon_config);
		//note: r_i is hased from (com_v, com_r, i) already
		sponge.absorb(&vec![r_i, v_i]);
		let ch: E::ScalarField = sponge.squeeze_field_elements(1)[0];

		//2. compute the combined vector
		let zero = E::ScalarField::zero();
		let mut vec = snark_input.vec_r.iter().zip(snark_input.vec_v.iter()).
			map(|(a,b)| *a + ch * *b).collect::<Vec<E::ScalarField>>();
		let last_ele = snark_input.r_vec_r + ch * snark_input.r_vec_v;
		vec.push(last_ele);
		let vcom_prf = 
			VecCom::<'a,E>::prove_with_challenge(&pkey.vec, ch, &vec, 
			&zero, None).expect("vcom proof err");
		let mut wi = words[i].clone();
		wi.push(snark_input.rands[i]);
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
		batch_proof: &BatchProof<E,S>,
		ind_proof: &IndividualProof<E>,
		)->bool{
		//1. verify the generated challenges
		assert!(i==claim.i);	
		let mut sponge= PoseidonSponge::<E::ScalarField> 
			::new(&vkey.poseidon_config);
		let mut arr_fe:Vec<F> = vec![];
		let rc = &claim.ref_batch_claim;
		let (kzg_all_words, kzg_length) = {
			let guard = rc.lock().unwrap();
			(guard.kzg_all_words.clone(), guard.kzg_length.clone())
		};
		let arr_c1 = vec![kzg_all_words, kzg_length, claim.kzg_word.clone()];
		for c in arr_c1{
				c.to_native_sponge_field_elements_as_vec()
					.to_sponge_field_elements(&mut arr_fe);
		}
		sponge.absorb(&F::from(i as u32));
		sponge.absorb(&arr_fe);
		let r_i:F = sponge.squeeze_field_elements(1)[0];
		let v_i = ind_proof.v_i;
		let mut sponge= PoseidonSponge::<E::ScalarField> 
			::new(&vkey.poseidon_config);
		sponge.absorb(&vec![r_i, v_i]);
		let ch: E::ScalarField = sponge.squeeze_field_elements(1)[0];

		//2. verify the vec_com
		let newcm = batch_proof.vcom_vec_r + batch_proof.vcom_vec_v.mul(ch);
		let bres = VecCom::<'a,E>::verify_with_challenge(&vkey.vec, ch, 
			&newcm, &ind_proof.vcom_prf);
		if !bres.is_ok() {
			return false;
		}

		//3. verify the kzg commitment
		let bres = KZG::<'a,E>::verify_with_challenge(&vkey.kzg, r_i,
			&claim.kzg_word, &ind_proof.kzg_prf);
		bres.is_ok()
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
		let mut vec_r = vec![snark_input.vec_r.clone(), 
			vec![snark_input.r_vec_r]].concat();
		let vcom_vec_r = VecCom::<'a,E>::commit(&pkey.vec, &vec_r, &zero)
			.expect("vcom_vec_r error");
		//vec_r[vec_r_len-1] = snark_input.r_vec_r_kzg.clone();
		vec_r.reverse();
		vec_r[0] = snark_input.r_vec_r_kzg.clone();
		let kzg_vec_r = KZG::<'a,E>::commit(&pkey.kzg, &vec_r, &zero)
			.expect("kzg_vec_r error"); 

		//2. vcom and kzg of vec_v
		let mut vec_v = vec![snark_input.vec_v.clone(), 
			vec![snark_input.r_vec_v]].concat();
		let vcom_vec_v = VecCom::<'a,E>::commit(&pkey.vec, &vec_v, &zero)
			.expect("vcom_vec_v error");
		//vec_v[vec_v_len-1] = snark_input.r_vec_v_kzg.clone();
		vec_v.reverse();
		vec_v[0] = snark_input.r_vec_v_kzg.clone();
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

			let mut all_words = words.concat();
			all_words.push(snark_input.r_all_words);
			let mut all_len:Vec<F> 
				= words.iter().map(|w| F::from(w.len() as u32))
				.collect();
			all_words.reverse();

			all_len.push(snark_input.r_kzg_len);
			all_len.reverse();

			let mut vec_r = snark_input.vec_r.clone();
			vec_r.push(snark_input.r_vec_r_kzg);
			vec_r.reverse();

			let mut vec_v = snark_input.vec_v.clone();
			vec_v.push(snark_input.r_vec_v_kzg);
			vec_v.reverse();


			let vec2d = vec![lk1, lk2, all_words, all_len, vec_r, vec_v];
		


			let res = KZG::<E>::batch_prove_with_challenge(&pkey.kzg, ch, &vec2d, rc)
				.expect("kzg batch prove error");
			res
		};
			

		//println!("DEBUG USE 500.9.1 *****: sum_kzv_eval: {}", agg_kzg_prf.eval);
		let batch_prf = BatchProof{
			vcom_vec_r, kzg_vec_r, vcom_vec_v, kzg_vec_v,
			prf_qa_nizk, ch, rc, agg_kzg_prf,

			kzg_all_com1: None,
			kzg_all_com_ch1: None,
			kzg_all_com_prf1: None,
			kzg_all_com2: None,
			kzg_all_com_ch2: None,
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
	/// to the KZG eval of the lkup as a poly. So we use the opt_kzg_sum1
	/// in this case to let the verification pass.
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
		)->bool{
		//0. build rand input for generate Fiat-Shamir randoms
		let b_debug = B_DEBUG;
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
		let bres = verify_qa_nizk::<E>(&x, &prf.prf_qa_nizk, 
			&vkey.vk_qa_nizk);	
		if !bres {
			if b_debug {emit_stdout(
				"qa_nizk verif fails".to_string());}
			return false;
		}

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
		if ch!=prf.ch || rc!=prf.rc {return false;}
		let mut com_all = E::G1::zero();
		let mut factor = E::ScalarField::one();
		for i in 0..coms.len(){
			com_all = com_all + coms[i].mul(factor);
			factor = factor * rc;
		}
		let res = KZG::<E>::verify_with_challenge(&vkey.kzg,
			ch, &com_all, &prf.agg_kzg_prf);
		if !res.is_ok() {
			if b_debug {emit_stdout(
				"kzg verif fails".to_string());}
			return false;
		}

		if b_check_part2{//check the rest part
			assert!(prf.kzg_all_com1.is_some());
			//1. check kzg_all_com1
			let res1 = CS1E::verify_with_challenge(
				&vkey.kzg_driver1.clone().expect("driver 1 kzg ver key null!"),
				*prf.kzg_all_com_ch1.as_ref().expect("com_ch1 empty"),
				&prf.kzg_all_com1.expect("kzg1 empty"),
				&prf.kzg_all_com_prf1.as_ref().expect("prf1 empty"));	
			if !res1.is_ok() {
				if b_debug {emit_stdout(
					"cs1e kzg_all_ocm1 verif fails".to_string());}
				return false;
			}

			//2. check kzg_all_com2
			let res2 = CS1E::verify_with_challenge(
				&vkey.kzg_driver2.clone().expect("driver2 kzg ver null!"),
				*prf.kzg_all_com_ch2.as_ref().expect("com_ch2 empty"),
				&prf.kzg_all_com2.expect("kzg2 empty"),
				&prf.kzg_all_com_prf2.as_ref().expect("prf2 empty"));	
			if !res2.is_ok() {
				if b_debug {emit_stdout(
					"cs1e kzg_all_com2 res2 fails".to_string());}
				return false;
			}

			//3. check qa_nizk_prf2
			let vec_x = vec![
				prf.kzg_all_com2.unwrap().clone(), 
				prf.comW2.unwrap().clone(),
				prf.comE2.unwrap().clone(),
				prf.comF2.unwrap().clone()];
			let bres = verify_qa_nizk::<E>(
				&vec_x, 
				&prf.qa_nizk_prf2.clone().unwrap(), 
				&nova2_qa_nizk_vkey.expect("qanizk vkey empty")
			);	
			if !bres {
				if b_debug {emit_stdout(
					"qanizk2 fails".to_string());}
				return false;
			}

			//4. check the snark proof
			let kzg_sum1 = if opt_kzg_sum1.is_some(){
				opt_kzg_sum1.unwrap() //in NOT check lkup mode
					//the full eval of entire lkup KZG will not work
					//take the circuits' output instead.
			}else{
				prf.agg_kzg_prf.eval //normal mode
			};
			//4.1 verify the maincirc snark proof
			let pub_inp = vec![prf.mainres_hash.unwrap()];
			if b_debug {
				emit_stdout(format!(
					"DEBUG USE 6901.2.0 public input: {}",
					pub_inp[0]));
			}
			let snark_v_main = S::verify(
				&snark_vk_main.expect("snark vkey_main empty"),
				&pub_inp,
				&prf.snark_proof_main.as_ref().clone()
					.expect("snark main empty")
			);
			if b_debug{ emit_stdout(format!(
				"snark main details: {:?}", snark_v_main)); }
			if !snark_v_main.is_ok() || !snark_v_main.unwrap().clone() {
				if b_debug { emit_stdout(
					"snark main fails.".to_string()); }
				return false;
			}

			//4.2 verify te cpcirc snark proof
			let snark_inp = CircPubInput{
				ch1: prf.ch,
				rc1: prf.rc,
				kzg_sum1: kzg_sum1,
				kzg_all_com_ch1: prf.kzg_all_com_ch1.clone()
					.expect("com_ch1 null"),
				eval_w_e1: prf.kzg_all_com_prf1.clone()
					.expect("eval_w_e1 null").eval,
				mainres_hash: prf.mainres_hash.unwrap(),

				kzg_all_com_ch2: prf.kzg_all_com_ch2.clone()
					.expect("com_ch2 null"),
				eval_w_e2: prf.kzg_all_com_prf2.clone()
					.expect("eval_w_e2 null").eval,

				comE2: prf.comE2.expect("com_e2 null").clone(),
				comW2: prf.comW2.expect("com_e2 null").clone(),
				comF2: prf.comF2.expect("com_e2 null").clone(),

				qa_nizk_vkey_hash: nova1_qa_nizk_vkey_hash
					.expect("nova1 qanizk vkey hash empty!"), 

			};
			let public_input: Vec<F> = snark_inp.to_vec().expect("to_vec err");
        	let snark_v_cp= S::verify(
				&snark_vk_cp.expect("snark vkey empty!"), 
				&public_input, 
				&prf.snark_proof_cp.as_ref().clone().expect("snark pf empty"));
					//.map_err(|e| Error::Other(e.to_string())).unwrap();
			if b_debug{emit_stdout(format!(
				"snark_v_cp details: {:?}", snark_v_cp));}
			if !snark_v_cp.is_ok() || !snark_v_cp.unwrap().clone() {
				if b_debug {emit_stdout(
					"snark_v_cp fails.".to_string());}
				return false;
			}
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
   use std::sync::Arc;


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
			poseidon_canonical_config::<Fr>(), 0);
		let (global_claim, ind_claims, snark_inp) = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>, Groth16<Bn254>, CS1E, false>::gen_claims(&pk, &mut rng, &words, lkup.clone()).unwrap();

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
		assert!(BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E, false>::verify_batch(&vk, None, None, None, None, &global_claim, &batch_proof, &poseidon_config, false, None));
		let ind_prf = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E,false>::prove_individual(&pk, 
			&snark_inp, &words, &ind_claims[i], i);
		let res = BatchProcessor::<Bn254,LookupTableTwoCol_Inst<Fr>,Groth16<Bn254>,CS1E,false>::verify_individual(&vk, i,
			&ind_claims[i], &batch_proof, &ind_prf);
		assert!(res, "verify indidivudal proof failed");
   }
}
