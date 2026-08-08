//! Non-daemonizing CLI wrapper around bora_data_driver's functions, for
//! NEW_PAPER_DATA.py to shell out to. Parses argv and dispatches -- no
//! business logic here.
//!
//! Usage: bora_data_driver lkup <perc> <dest_path>

use zkregplus::bora_data_driver::collect_lookup_stats_adv;

fn main() {
	let args: Vec<String> = std::env::args().collect();
	match args.get(1).map(|s| s.as_str()) {
		Some("lkup") => {
			let perc: usize = args.get(2)
				.expect("bora_data_driver lkup: missing <perc>")
				.parse().expect("bora_data_driver lkup: <perc> not usize");
			let dest_path = args.get(3)
				.expect("bora_data_driver lkup: missing <dest_path>");
			collect_lookup_stats_adv(perc, dest_path);
		}
		other => panic!("bora_data_driver: unknown subcommand: {:?}", other),
	}
}
