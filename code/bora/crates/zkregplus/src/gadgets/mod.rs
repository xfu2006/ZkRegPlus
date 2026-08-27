/// common functions
pub mod commons;
/// small common traits and structs to build proofs
pub mod traits;
/// word extractor gadget
pub mod word_extract;
/// word extractor gadget (advanced)
pub mod word_extract_adv;
/// finite state machine gadget
pub mod fsm;
/// packing states into final states
pub mod pack;
/// extract signatures from final states
pub mod sigs;
/// advanced fsm gadget which produces compressed (state,loc) info
pub mod fsm_adv;
/// database related proof operations
pub mod db;
/// discharge subsigs
pub mod discharge_adv;
/// discharge subsigs (constant-queue variant)
pub mod discharge_adv_neo;
/// from subsigs to discharged sigs
pub mod compute_sig_adv;
/// discharge a sig via dfa approach
pub mod dfa_adv;
