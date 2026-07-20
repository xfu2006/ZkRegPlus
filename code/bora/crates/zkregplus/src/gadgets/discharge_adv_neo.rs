// discharge_adv_neo.rs
// Created 2026-07-19.
// Design by the BORA paper author. Code implemented by Claude Opus.
// Code reviewed by the paper author and unit tested.
//
// M3 coexistence stub for the Appendix G.1 constant-queue SDE. This
// stub delegates every SigmaGadget method to DischargeAdvGadget, so the
// neo path is byte-identical to the legacy SDE. The real G.1
// certificates (C/FP/BP/SP over StepQueueNeo) replace the body in M4-M7.

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{SynthesisError, ConstraintSystemRef};
use data_processor::type_def::SubsigStepStore;
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget, WitnessSigmaIR1CSVar,
		WitnessSigmaIR1CSConfig},
	container_config::{ColEle, ContainerConfig},
};
use crate::gadgets::discharge_adv::{DischargeAdvGadget,
	DischargeAdvCapacity};

/// M3 stub wrapping the legacy SDE gadget; forwards all trait methods.
#[derive(Clone, Debug)]
pub struct DischargeAdvNeoGadget<F: PrimeField + ColEle> {
	/// delegate target; replaced by native G.1 state in M4+.
	pub inner: DischargeAdvGadget<F>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// mirrors DischargeAdvGadget::new so the sed_mapper swap is 1:1.
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		capacity: &DischargeAdvCapacity,
		fsm_id: u32,
		prev_cfgs: &Vec<ContainerConfig>,
		store_steps: &SubsigStepStore,
	) -> Self {
		let inner = DischargeAdvGadget::<F>::new(
			b_igc, offset_fsm, capacity, fsm_id, prev_cfgs,
			store_steps);
		Self { inner }
	}
}

impl<F: PrimeField + ColEle> SigmaGadget<F>
	for DischargeAdvNeoGadget<F> {
	fn get_name(&self) -> &str { self.inner.get_name() }

	fn set_job_id(&mut self, job_id: usize) {
		self.inner.set_job_id(job_id);
	}

	fn get_job_id(&self) -> usize { self.inner.get_job_id() }

	fn set_container_cfg(&mut self,
		cfgs_context: std::sync::Arc<Vec<ContainerConfig>>,
		idx: usize) {
		self.inner.set_container_cfg(cfgs_context, idx);
	}

	fn get_container_config(&self) -> ContainerConfig {
		self.inner.get_container_config()
	}

	fn est_cost(&self) -> usize { self.inner.est_cost() }

	fn get_msg_size(&self) -> (usize, usize, usize, usize) {
		self.inner.get_msg_size()
	}

	fn get_to_add_size(&self)
		-> (usize, usize, usize, usize, usize) {
		self.inner.get_to_add_size()
	}

	fn get_stmt_map_instructions(&self)
		-> Vec<(i32, usize, usize, usize)> {
		self.inner.get_stmt_map_instructions()
	}

	fn gen_msg1(&self, stmt_vec: &Vec<F>,
		v_idx: &Vec<(usize, usize)>) -> Vec<F> {
		self.inner.gen_msg1(stmt_vec, v_idx)
	}

	fn gen_msg3(&self, stmt_vec: &Vec<F>,
		stmt_idx: &Vec<(usize, usize)>,
		msg1_vec: &Vec<F>, idx_msg1: usize, len_msg1: usize,
		msg2_vec: &Vec<F>, idx_msg2: usize, len_msg2: usize)
		-> Vec<F> {
		self.inner.gen_msg3(stmt_vec, stmt_idx, msg1_vec,
			idx_msg1, len_msg1, msg2_vec, idx_msg2, len_msg2)
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>,
		wtns: &WitnessSigmaIR1CSVar<F>,
		cfg: &WitnessSigmaIR1CSConfig,
		word_id: FpVar<F>, subsig_id: FpVar<F>)
		-> Result<(), SynthesisError> {
		self.inner.assert_msg3(i, cs, wtns, cfg, word_id,
			subsig_id)
	}
}
