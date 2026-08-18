//! bora_cli: non-daemonizing CLI wrapper around bora_data_driver's
//! functions. Backend of scripts/PAPER_DATA.py -- run that
//! driver instead; direct invocation is for debugging only.

use zkregplus::bora_data_driver::{collect_assess_tier_data_adv,
	collect_lookup_stats_adv, collect_scale_clamav_neo,
	collect_scale_dlp_neo, full_clamav_neo, full_dlp_neo,
	full_dna_neo, parse_args, small_full_dlp_neo, Cmd, USAGE};

fn main() {
	let args: Vec<String> = std::env::args().skip(1).collect();
	if args.is_empty() || args[0] == "--help" || args[0] == "-h" {
		println!("{}", USAGE);
		return;
	}
	match parse_args(&args) {
		Cmd::Lkup { perc, dest_path } =>
			collect_lookup_stats_adv(perc, &dest_path),
		Cmd::Effective { perc, dest_path } =>
			collect_assess_tier_data_adv(perc, &dest_path),
		Cmd::FullDlp { perc_db, perc_samples, num_circs, num_jobs,
			numa_num, part_id, b_dry_run, b_ladder_only } => {
			full_dlp_neo(perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_dry_run, b_ladder_only);
		}
		Cmd::FullDna { perc_db, perc_samples, num_circs, num_jobs,
			numa_num, part_id, b_dry_run, b_ladder_only,
			tune_v2 } => {
			full_dna_neo(perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_dry_run, b_ladder_only,
				tune_v2);
		}
		Cmd::FullClam { perc_db, perc_samples, num_circs, num_jobs,
			numa_num, part_id, b_dry_run, b_ladder_only,
			tune_v2 } => {
			full_clamav_neo(perc_db, perc_samples, num_circs,
				num_jobs, numa_num, part_id, b_dry_run,
				b_ladder_only, tune_v2);
		}
		Cmd::SmallFullDlp { perc_db, perc_samples, num_circs,
			num_jobs, numa_num, part_id, b_dry_run,
			b_ladder_only } => {
			small_full_dlp_neo(perc_db, perc_samples, num_circs,
				num_jobs, numa_num, part_id, b_dry_run,
				b_ladder_only);
		}
		Cmd::ScaleDlp { corpus_idx, vec_count, b_dry_run } =>
			collect_scale_dlp_neo(corpus_idx, &vec_count, b_dry_run),
		Cmd::ScaleClam { corpus_idx, vec_count, b_dry_run } =>
			collect_scale_clamav_neo(corpus_idx, &vec_count,
				b_dry_run),
	}
}
