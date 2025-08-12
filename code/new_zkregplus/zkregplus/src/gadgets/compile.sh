# quick check
# cargo check --tests 2>&1 | less

# test
#RUST_BACKTRACE=1 
#cargo test -- tests_word_extract_adv --show-output --nocapture
#cargo test -- tests_fsm_adv_gadget --show-output --nocapture
cargo test -- tests_discharge_adv_gadget --show-output --nocapture
#cargo test -- test_dfa_adv --show-output --nocapture
#cargo test -- test_compute_sig_adv --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_bwd_prf --show-output --nocapture
#RUST_BACKTRACE=1 

#cargo test -- tests_word_extract_gadget --show-output --nocapture
#cargo test -- tests_fsm_gadget --show-output --nocapture
#cargo test -- tests_pack_gadget --show-output --nocapture
#cargo test -- tests_sigs_gadget --show-output --nocapture

#cargo test -- test_encode --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_tbl_left_join --show-output --nocapture
#cargo test -- tests_db --show-output --nocapture
#cargo test -- tests_fsm_adv --show-output --nocapture
#RUST_BACKTRACE=1 
# cargo test -- test_assert_wellformed_sorted --show-output --nocapture
# cargo test -- test_sorted_set --show-output --nocapture
#cargo test -- test_gen_m_tbl --show-output --nocapture
