/* This module mainly consists of gadget mappers related
   to a variety of circuits
*/

/// Top level gadget mapper which contains optional CP, SED, DFA mappers
pub mod composable_gadget_mapper; 
/// gadget mapper for CP discharging algorithm
pub mod cp_mapper;
/// gadget mapper for sed approach
pub mod sed_mapper;

