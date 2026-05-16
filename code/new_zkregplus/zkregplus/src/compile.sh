# quick build 
#cargo check --tests 2>&1 | more 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more 

# test zkpsmall example
#RUST_MIN_STACK=8388608
# 2026-05-16: switched the active line from test_zkreg_main to
# test_full_debug_main for full_debug_watch.py (single job, 4
# server-failing samples, b_folding_only=true so no g16 keys
# needed). Swap back to test_zkreg_main for deadlock_detect.py or
# other flows.
RUST_BACKTRACE=1 cargo test --lib --release -- test_full_debug_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib --release -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=full cargo test -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_zkreg_main --show-output --nocapture

# small example 
#RUST_BACKTRACE=1 cargo run --release --example zkreg small 
#RUST_BACKTRACE=1 

# foldpot example
#RUST_BACKTRACE=1 cargo run --release --example foldpot 


# test zkpsmall example SLOW
# RUST_BACKTRACE=1 cargo test -- test_word_extract_adv --show-output --nocapture
