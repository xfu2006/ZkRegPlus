# compile
#cargo check --tests 2>&1 | less

# test
#cargo test -- tests_clam_db
#cargo test -- tests_clamav
#cargo test -- tests_pcre
cargo test -- tests_hex_acdfa  -- --show-output
