import re

with open('../circs/sed_mapper.rs', 'r') as f:
    content = f.read()

# CS replacement
# Find the line: let discharge_adv_advice_cs = DischargeAdvAdvice::<F>\n                        ::new(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32, \n                                subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs)?;
# Replace it with the new definition
# We use regex to match it in case spacing is different
cs_pattern = r'let discharge_adv_advice_cs = DischargeAdvAdvice::<F>[\s]*::new\(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32,[\s]*subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs\)\?;'
cs_replacement = """let locs_cs = fsm_adv_advice_cs.stmt_container.borrow()
                        .search_container("fsm_adv_stmt_cs fsm_acc locs").unwrap()
                        .borrow().to_vec();
                let last_loc_cs = locs_cs[locs_cs.len()-1];
                let discharge_adv_advice_cs = DischargeAdvAdvice::<F>
                        ::new(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32, 
                                subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs, last_loc_cs)?;"""
content = re.sub(cs_pattern, cs_replacement, content)

igc_pattern = r'let discharge_adv_advice_igc = DischargeAdvAdvice::<F>[\s]*::new\(true, 2, &pat_loc_igc, &subsigs_inp_igc, fsm_id_igc as u32,[\s]*subsig_step_store_igc, &da_cap_igc, &inp_steps_queue_obj_igc\)\?;'
igc_replacement = """let locs_igc = fsm_adv_advice_igc.stmt_container.borrow()
                        .search_container("fsm_adv_stmt_igc fsm_acc locs").unwrap()
                        .borrow().to_vec();
                let last_loc_igc = locs_igc[locs_igc.len()-1];
                let discharge_adv_advice_igc = DischargeAdvAdvice::<F>
                        ::new(true, 2, &pat_loc_igc, &subsigs_inp_igc, fsm_id_igc as u32, 
                                subsig_step_store_igc, &da_cap_igc, &inp_steps_queue_obj_igc, last_loc_igc)?;"""
content = re.sub(igc_pattern, igc_replacement, content)

with open('../circs/sed_mapper.rs', 'w') as f:
    f.write(content)

