import re
import os

files_to_fix = [
    "zkregplus/src/gadgets/commons.rs",
    "zkregplus/src/gadgets/fsm_adv.rs",
    "zkregplus/src/gadgets/compute_sig_adv.rs",
    "zkregplus/src/gadgets/dfa_adv.rs",
    "zkregplus/src/gadgets/discharge_adv.rs",
    "zkregplus/src/gadgets/sigs.rs",
    "zkregplus/src/gadgets/db.rs",
    "zkregplus/src/gadgets/fsm.rs"
]

def fix_file(filepath):
    if not os.path.exists(filepath):
        print(f"File not found: {filepath}")
        return

    with open(filepath, 'r') as f:
        content = f.read()
        
    orig_content = content

    # 1. Ensure read_global_config is imported if RANGE2_BIT is used or read_global_config is going to be used
    if 'read_global_config' not in content and re.search(r'\bRANGE2_BIT\b', content):
        # Find where to add the import
        if 'use utils::consts::' in content:
            content = re.sub(r'use utils::consts::\{([^}]*)\};', r'use utils::consts::{\1, read_global_config};', content)
        else:
            content = "use utils::consts::read_global_config;\n" + content

    # 2. Replace RANGE2_BIT
    content = re.sub(r'\bRANGE2_BIT\b', 'read_global_config().range2_bit', content)

    # 3. Fix known formatting errors by regex or exact match
    
    # In commons.rs
    content = content.replace('println!("===  ====", msg);', 'println!("=== {} ====", msg);')
    content = content.replace('println!("   ", x);', 'println!("   {}", x);')
    content = content.replace('println!("   => ", i, v[i]);', 'println!("   {} => {}", i, v[i]);')
    content = content.replace('println!("ERROR: failed checkdisjoint for ", msg);', 'println!("ERROR: failed checkdisjoint for {}", msg);')
    content = content.replace('format!("assert_encode_cols_in_range. n: , cs: "', 'format!("assert_encode_cols_in_range. n: {}, cs: {}"')
    content = content.replace('println!(" ### gen_assert_sidcol_for_diff: n: , cs: "', 'println!(" ### gen_assert_sidcol_for_diff: n: {}, cs: {}"')
    content = content.replace('println!("=====  ====", name);', 'println!("===== {} ====", name);')
    content = content.replace('print!("  ", tbl[j][i]);', 'print!("  {}", tbl[j][i]);')
    content = content.replace('tbl[0][i]: , tbl[2][i]: , tbl2[i][i-1]: .', 'tbl[0][i]: {}, tbl[2][i]: {}, tbl2[i][i-1]: {}.')
    content = content.replace('"n: lower than tuples.len(): ",n,tuples.len()', '"n: lower than tuples.len(): {} {}",n,tuples.len()')
    content = content.replace('println!("--- verify_inverse: len: , cs: "', 'println!("--- verify_inverse: len: {}, cs: {}"')
    content = content.replace('println!("--- verify_logup_inverse: len1: , len2: , cs: "', 'println!("--- verify_logup_inverse: len1: {}, len2: {}, cs: {}"')
    content = content.replace('println!("STOP HERE 3333: "', 'println!("STOP HERE 3333: {}"')
    content = content.replace('format!("check eq  fails: "', 'format!("check eq  fails: {} {}"')
    content = content.replace('format!("ERR on imply: "', 'format!("ERR on imply: {}"')
    content = content.replace('format!("verif_2dlkup step 0. build witness. n_q: , n_l: , cs: "', 'format!("verif_2dlkup step 0. build witness. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_2dlkup step 1. build witness. n_q: , n_l: , cs: "', 'format!("verif_2dlkup step 1. build witness. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_2dlkup step 3.1 logup_check. n_q: , n_l: , cs: "', 'format!("verif_2dlkup step 3.1 logup_check. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_2dlkup step 3.2 logup_check. n_q: , n_l: , cs: "', 'format!("verif_2dlkup step 3.2 logup_check. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_2dlkup TOTAL . n_q: , n_l: , cs: "', 'format!("verif_2dlkup TOTAL . n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_1dlkup step 0. build witness. n_q: , n_l: , cs: "', 'format!("verif_1dlkup step 0. build witness. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_1dlkup step 1. build witness. n_q: , n_l: , cs: "', 'format!("verif_1dlkup step 1. build witness. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_1dlkup step 3.2 logup_check. n_q: , n_l: , cs: "', 'format!("verif_1dlkup step 3.2 logup_check. n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('format!("verif_1dlkup TOTAL . n_q: , n_l: , cs: "', 'format!("verif_1dlkup TOTAL . n_q: {}, n_l: {}, cs: {}"')
    content = content.replace('println!("ok: res: "', 'println!("ok: res: {}"')

    # Fix other common missing {} patterns found in other files (based on cargo output)
    content = re.sub(r'println!\("\t\t", ([^;]+)\);', r'println!("\\t\\t {} {} {}", \1);', content)
    content = content.replace('format!(" fsm_acc locs"', 'format!("{} fsm_acc locs"')
    content = content.replace('println!("DEBUG USE 6901.5: last_loc: , cost:  ms"', 'println!("DEBUG USE 6901.5: last_loc: {}, cost: {} ms"')
    content = content.replace('println!("PERF 102: discharge_adv: TOTAL n"', 'println!("PERF 102: discharge_adv: TOTAL n {}"')
    content = content.replace('println!("DEBUG USE 6700: discharge_info for sig: "', 'println!("DEBUG USE 6700: discharge_info for sig: {}"')
    content = content.replace('"inp_subsigs_cs.len:  should be <= capacity', '"inp_subsigs_cs.len: {} should be <= capacity {}')
    content = content.replace('"inp_subsigs_igc.len:  should be <= capacity', '"inp_subsigs_igc.len: {} should be <= capacity {}')
    content = content.replace('println!("DEBUG USE 6701 -- list of inp_subsigs, b_igc: "', 'println!("DEBUG USE 6701 -- list of inp_subsigs, b_igc: {}"')
    content = content.replace('println!(" -- i: , subsig: "', 'println!(" -- i: {}, subsig: {}"')
    content = content.replace('Some(format!(" bwd_steps_queue sq_res2",sname)),', 'Some(format!("{} bwd_steps_queue sq_res2",sname)),')
    content = content.replace('format!("comp_sig', 'format!("{} comp_sig')
    content = content.replace('&format!("cannot find info for subsig: "', '&format!("cannot find info for subsig: {}"')
    content = content.replace('println!("DEBUG USE 6702: res for subsig:  is NOT false. max_step: , last_step[i]: "', 'println!("DEBUG USE 6702: res for subsig: {} is NOT false. max_step: {}, last_step[i]: {}"')
    content = content.replace('&format!("cannot find step info', '&format!("{} cannot find step info')
    content = content.replace('println!("DEBUG USE 6703: i: , b_igc: , subsig: , raw_res: {:?}, count_res: {:?}",', 'println!("DEBUG USE 6703: i: {}, b_igc: {}, subsig: {}, raw_res: {:?}, count_res: {:?}",')
    content = content.replace('&format!("Can\'t find info for su', '&format!("{} Can\'t find info for su')
    content = content.replace('println!("*** DEBUG USE 6704: subsig:  comp: , res: {:?}, cnt_true: , cnt_maybe: , min_req: "', 'println!("*** DEBUG USE 6704: subsig: {} comp: {}, res: {:?}, cnt_true: {}, cnt_maybe: {}, min_req: {}"')
    content = content.replace('println!("DEBUG USE 9003: perc_comp_subsigs: , subsigs_cs: , subsigs_igc: , scc_prf_subsig.len: , get_scc_prf_size:', 'println!("DEBUG USE 9003: perc_comp_subsigs: {}, subsigs_cs: {}, subsigs_igc: {}, scc_prf_subsig.len: {}, get_scc_prf_size: {}')
    content = content.replace('1, "Adjust perc_comp_subsig in Config! Needed scc_prf len:  < current_tuples: "', '1, "Adjust perc_comp_subsig in Config! Needed scc_prf len: {} < current_tuples: {}"')
    content = content.replace('&format!("sid_",names[i])', '&format!("sid_{}",names[i])')
    content = content.replace('&format!("cannot find sig:', '&format!("cannot find sig: {}')
    content = content.replace('1, "cannot find or duplicate entries for "', '1, "cannot find or duplicate entries for {}"')
    content = content.replace('&format!("cannot find sig: "', '&format!("cannot find sig: {}"')
    content = content.replace('println!("*** DEBUG USE 6708 found bad subsig_id: , in sig: , real_id: , details: "', 'println!("*** DEBUG USE 6708 found bad subsig_id: {}, in sig: {}, real_id: {}, details: {}"')
    content = content.replace('println!(" -- subsig: , res', 'println!(" -- subsig: {}, res: {}')
    content = content.replace('&format!("cannot find subsig_id: "', '&format!("cannot find subsig_id: {}"')
    content = content.replace('println!("DEBUG USE 6706: WILL REPORT ERROR on subsig: , res: "', 'println!("DEBUG USE 6706: WILL REPORT ERROR on subsig: {}, res: {}"')
    content = content.replace('e, "ERROR: subsig_id: , res:  is not false"', 'e, "ERROR: subsig_id: {}, res: {} is not false"')
    content = content.replace('&format!("sid_",n)', '&format!("sid_{}",n)')
    content = content.replace('println!(" ### validate_eval_subsig_by_sq_combo: subsigs: , sq_res.len: , cost: "', 'println!(" ### validate_eval_subsig_by_sq_combo: subsigs: {}, sq_res.len: {}, cost: {}"')
    content = content.replace('println!(" -- i: , subsig:  => "', 'println!(" -- i: {}, subsig: {} => {}"')
    content = content.replace('println!("DEBUG USE 6300: i: , subsig: "', 'println!("DEBUG USE 6300: i: {}, subsig: {}"')
    content = content.replace('println!("DEBUG USE 6311: same_subsig: , diff: , col2d[5][i]: , is_raw_true: , col2d[5][i-1]:', 'println!("DEBUG USE 6311: same_subsig: {}, diff: {}, col2d[5][i]: {}, is_raw_true: {}, col2d[5][i-1]: {}')
    content = content.replace('println!("DEBUG USE 6312: prev_subsig: , vec_count[i-1]: , col2d[2][i-1]: , max: , col2d[5][i]: , is_raw_true: , col2d[7][i]: , is_raw_maybe:', 'println!("DEBUG USE 6312: prev_subsig: {}, vec_count[i-1]: {}, col2d[2][i-1]: {}, max: {}, col2d[5][i]: {}, is_raw_true: {}, col2d[7][i]: {}, is_raw_maybe: {}')
    content = content.replace('println!(" --i: , subsig: , res: "', 'println!(" --i: {}, subsig: {}, res: {}"')
    content = content.replace('println!(" ### validate_syntehsis_subsig_combo: subsigs: , scc_tbl_size: , cost: "', 'println!(" ### validate_syntehsis_subsig_combo: subsigs: {}, scc_tbl_size: {}, cost: {}"')
    content = content.replace('println!(" --i: , sig: "', 'println!(" --i: {}, sig: {}"')
    content = content.replace('println!(" ### validate_discharge_sig_combo: sigs: , subsig: , cost: "', 'println!(" ### validate_discharge_sig_combo: sigs: {}, subsig: {}, cost: {}"')
    content = content.replace('1, "capacity.subsigs:  < inp_subsigs: . adjust DfaCapacity.subsigs"', '1, "capacity.subsigs: {} < inp_subsigs: {}. adjust DfaCapacity.subsigs"')
    content = content.replace('s, "increase capacity.sigs:  to cover inp_sigs: "', 's, "increase capacity.sigs: {} to cover inp_sigs: {}"')
    content = content.replace('=nlen, "nibbles: , nlen: "', '=nlen, "nibbles: {}, nlen: {}"')
    content = content.replace('println!("DEBUG USE 6735.9.1: DFA: , idx: , ch: , dst: "', 'println!("DEBUG USE 6735.9.1: DFA: {}, idx: {}, ch: {}, dst: {}"')
    content = content.replace('println!("DEBUG USE 6735.9: DFA  FOUND final state:  at idx:  (start_idx: , seg_id: )"', 'println!("DEBUG USE 6735.9: DFA  FOUND final state: {} at idx: {} (start_idx: {}, seg_id: {})"')
    content = content.replace('e, "ERR dfa_adv: for subsig: , it\'s result is "', 'e, "ERR dfa_adv: for subsig: {}, it\'s result is {}"')
    content = content.replace('&format!("si_",n)', '&format!("si_{}",n)')
    content = content.replace('println!(" ### validate_mul_fsm_acc_container: m: , nlen: . cost: "', 'println!(" ### validate_mul_fsm_acc_container: m: {}, nlen: {}. cost: {}"')
    content = content.replace('println!(" ### check discharge_subsig: sig: , subsigs: , cost: "', 'println!(" ### check discharge_subsig: sig: {}, subsigs: {}, cost: {}"')
    content = content.replace('println!(" ### dfa_adv: sigs: , subsigs: , nlen', 'println!(" ### dfa_adv: sigs: {}, subsigs: {}, nlen: {}')
    
    # Generic replacement for any "xxx: , yyy: " style issues missed above
    content = re.sub(r'([A-Za-z0-9_]+): ,', r'\1: {},', content)

    # Some manual fixes for CapErr
    content = content.replace('format!("target_size::hashmap_2col"', 'format!("target_size::hashmap_2col: target_size {}, actual {}"')
    content = content.replace('format!("target_size::2col_left_join"', 'format!("target_size::2col_left_join: {}"')
    content = content.replace('format!("target_size::hashmap_2col_wide"', 'format!("target_size::hashmap_2col_wide: {}"')

    if orig_content != content:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed {filepath}")
    else:
        print(f"No changes for {filepath}")

for file in files_to_fix:
    fix_file(file)

