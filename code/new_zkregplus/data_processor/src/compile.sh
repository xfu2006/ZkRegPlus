# compile
#cargo check --tests 2>&1 | less

# test
#cargo test -- test_load_clam_db
#cargo test -- test_word_to_accept_id
cargo test -- tests_hex_acdfa 
#cargo test hex_acdfa::tests_hex_acdfa::debug_hex_dfa -- --show-output
