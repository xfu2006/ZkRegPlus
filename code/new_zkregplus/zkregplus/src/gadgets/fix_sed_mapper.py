import sys

with open('../circs/sed_mapper.rs', 'r') as f:
    content = f.read()

# I will replace the individual calls to DischargeAdvAdvice::new
old_cs = """                let discharge_adv_advice_cs = DischargeAdvAdvice::<F>
                        ::new(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32, 
                                subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs)?;"""

new_cs = """                let locs_cs = fsm_adv_advice_cs.stmt_container.borrow()
                        .search_container("fsm_adv_stmt_cs fsm_acc locs").unwrap()
                        .borrow().to_vec();
                let last_loc_cs = locs_cs[locs_cs.len()-1];
                let discharge_adv_advice_cs = DischargeAdvAdvice::<F>
                        ::new(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32, 
                                subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs, last_loc_cs)?;"""

old_igc = """                let discharge_adv_advice_igc = DischargeAdvAdvice::<F>
                        ::new(true, 2, &pat_loc_igc, &subsigs_inp_igc, fsm_id_igc as u32, 
                                subsig_step_store_igc, &da_cap_igc, &inp_steps_queue_obj_igc)?;"""

new_igc = """                let locs_igc = fsm_adv_advice_igc.stmt_container.borrow()
                        .search_container("fsm_adv_stmt_igc fsm_acc locs").unwrap()
                        .borrow().to_vec();
                let last_loc_igc = locs_igc[locs_igc.len()-1];
                let discharge_adv_advice_igc = DischargeAdvAdvice::<F>
                        ::new(true, 2, &pat_loc_igc, &subsigs_inp_igc, fsm_id_igc as u32, 
                                subsig_step_store_igc, &da_cap_igc, &inp_steps_queue_obj_igc, last_loc_igc)?;"""

if old_cs in content and old_igc in content:
    content = content.replace(old_cs, new_cs)
    content = content.replace(old_igc, new_igc)
    with open('../circs/sed_mapper.rs', 'w') as f:
        f.write(content)
    print("Success")
else:
    print("Not found")
    if old_cs not in content:
        print("old_cs not found")
    if old_igc not in content:
        print("old_igc not found")

