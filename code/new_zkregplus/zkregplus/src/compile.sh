# quick build 
#cargo check --tests 2>&1 | more 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more 

# test zkpsmall example
#RUST_MIN_STACK=8388608
# 2026-05-18: active line is test_full_debug_main for
# full_debug_watch.py (4-file binexec_debug.dat scan exercising the
# original MULTISET_MISMATCH scenario with suspect sigs
# 34602/35386/35701, now under the pad-invariant rework). Swap to
# test_small_debug_main for the small_data + max_word=2 pad
# validation, or test_zkreg_main for the original small_data
# (max_word=1, sub-F pad only).
#RUST_BACKTRACE=1 cargo test --lib --release -- test_full_debug_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib --release -- test_small_debug_main --show-output --nocapture

#RUST_BACKTRACE=1 cargo test --lib --release -- test_zkreg_main --show-output --nocapture
# collect Figure-9 tier-discharge stats -> dump for data/scripts/eval generator
RUST_BACKTRACE=1 cargo test --lib --release -- test_collect_assess_tier_data --show-output --nocapture 2>&1 | tee /tmp/eval_effective.txt
# discharge FULL clean Enron intl list (~515K) -> full/pass/fail lists
#RUST_BACKTRACE=1 cargo test --lib --release -- collect_enron_list --nocapture 2>&1 | tee /tmp/collect_enron.log
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
