/* This module mainly consists of gadget mappers related
   to a variety of circuits
*/

/// Top level gadget mapper which contains optional CP, SED, DFA mappers
pub mod composable_gadget_mapper; 
/// gadget mapper for CP discharging algorithm
pub mod cp_mapper;
/// gadget mapper for sed approach
pub mod sed_mapper;
/// gadget mapper for DFA approach
pub mod dfa_mapper;

pub const MIN_BASIS_UNIQUE_STATES: usize = 2;
pub const MIN_SUBSIGS: usize = 145;
pub const MIN_SIGS: usize = 2;
pub const MIN_AVG_PATS_PER_SUBSIG: usize = 2;
pub const MIN_AVG_ACTIVE_PATS_PER_SUBSIG: usize = 2;
pub const MIN_BASIS_PATS_IN_TRACE: usize = 2;
pub const MIN_PERC_PATS_EXPANSION_RATE: usize = 1;
pub const MIN_SIGS_SED: usize = 2;
pub const MIN_PERC_COMP_SUBSIGS: usize = 10;
pub const MIN_BASIS_ACC_STATES: usize = 2;

