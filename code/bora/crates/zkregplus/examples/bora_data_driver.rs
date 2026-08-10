//! Non-daemonizing CLI wrapper around bora_data_driver's functions,
//! for NEW_PAPER_DATA.py to shell out to. Argv parsing lives in
//! bora_data_driver::parse_args; no business logic here.

use zkregplus::bora_data_driver::{collect_lookup_stats_adv,
	collect_scale_dlp_neo, full_dlp_neo, parse_args, Cmd};

fn main() {
	let args: Vec<String> = std::env::args().skip(1).collect();
	match parse_args(&args) {
		Cmd::Lkup { perc, dest_path } =>
			collect_lookup_stats_adv(perc, &dest_path),
		Cmd::FullDlp { perc_db, perc_samples, num_circs, num_jobs,
			numa_num, part_id, b_light_test, b_ladder_only } => {
			full_dlp_neo(perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_light_test, b_ladder_only);
		}
		Cmd::ScaleDlp { corpus_idx, vec_count } =>
			collect_scale_dlp_neo(corpus_idx, &vec_count),
	}
}
