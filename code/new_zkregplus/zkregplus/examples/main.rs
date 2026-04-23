use ark_bn254::{constraints::{GVar, PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
use ark_ff::PrimeField;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
use ark_groth16::Groth16;
use cli_table::{format::Justify, Cell, Style, Table};
use daemonize::Daemonize;
use dialoguer::{Select, theme::ColorfulTheme};
use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};
use std::fs::File;
use std::path::PathBuf;

use utils::{
    consts::{get_global_config, read_global_config},
    logger::{ERR, LOG1, LOG2, LOG3, LOG4, LOG5, LOG6, LOG7, WARN},
    os::proj_root,
};

use zkregplus::{
    circs::{cp_mapper::CpCapacity, dfa_mapper::DfaCapacity, sed_mapper::SedCapacity},
    zkp_driver::{zkp_driver, zkp_driver_adv},
};

// --- Setup Curves and Fields ---
type CS1 = Pedersen<Projective>;
type CS1E = KZG<'static, Bn254>;
type CS2 = Pedersen<Projective2>;
type C1 = Projective;
type C2 = Projective2;
type GC1 = GVar;
type GC2 = GVar2;
type S = Groth16<Bn254>;
type C2G2 = ProjectiveG2;

// --- Options Definition ---
struct RunOption {
    name: &'static str,
    desc: &'static str,
    ram: &'static str,
    time: &'static str,
    jobs: usize,
    func: fn(bool),
}

const OPTIONS: [RunOption; 5] = [
    RunOption {
        name: "small_data",
        desc: "Each cat of signatures got one sample, one 2-Fr word.",
        ram: "7 GB",
        time: "36 sec",
        jobs: 1,
        func: small_data::<Fr>,
    },
    RunOption {
        name: "small_data_par",
        desc: "Small data processed in parallel.",
        ram: "11 GB",
        time: "44 sec",
        jobs: 4,
        func: small_data_par::<Fr>,
    },
    RunOption {
        name: "full_clamav_setup",
        desc: "Sets up snark keys using 16 1M samples. RUN THIS BEFORE #4/#5.",
        ram: "128 GB",
        time: "Est. Hours",
        jobs: 8,
        func: full_clamav_setup::<Fr>,
    },
    RunOption {
        name: "full_clamav_light",
        desc: "Tests full clamav signatures against linux executables. Needs #3.",
        ram: "128 GB",
        time: "Est. Hours",
        jobs: 8,
        func: full_clamav_light::<Fr>,
    },
    RunOption {
        name: "full_clamav_full",
        desc: "Tests full clamav signatures against linux executables. Needs #3.",
        ram: "894 GB",
        time: "Est. Hours",
        jobs: 8,
        func: full_clamav_full::<Fr>,
    },
];

const LOG_LEVELS: [(&str, usize); 9] = [
    ("ERR", ERR),
    ("WARN", WARN),
    ("LOG1", LOG1),
    ("LOG2", LOG2),
    ("LOG3", LOG3),
    ("LOG4", LOG4),
    ("LOG5", LOG5),
    ("LOG6", LOG6),
    ("LOG7", LOG7),
];

// --- Implementation Logic from zkp_driver.rs ---

fn small_data<F: PrimeField>(b_check_lkup: bool) {
    get_global_config().snark_cache_dir = "small_20".to_string();
    get_global_config().b_read_snark_cache = false;
    get_global_config().b_write_snark_cache = false;
    get_global_config().b_light_test = true;
    get_global_config().range2_bit = 8;
    get_global_config().b_read_cache = false;
    let b_write_cache = !read_global_config().b_read_cache;
    let set1 = "data/debug/small_data_set/config_dfa";
    let max_word = 1;
    let sigs = 2;
    let subsigs = 4;
    let avg_pats_per_subsig = 3;
    let avg_active_pats_per_subsig = 2;
    let perc_comp_subsigs = 26;
    let basis_unique_states = 23 * 100;
    let basis_acc_states = 646;
    let basis_pats_in_trace = 1291;
    let perc_pats_expansion_rate = 100;

    let vec_decrease_level = vec![];
    let num_circs = 1;

    let init_cp_cap = CpCapacity {
        max_word_len: max_word,
        basis_unique_states,
        subsigs,
        avg_pats_per_subsig,
    };
    let init_sed_cap = SedCapacity::new(
        max_word,
        read_global_config().range2_bit,
        subsigs,
        avg_pats_per_subsig,
        avg_active_pats_per_subsig,
        basis_pats_in_trace,
        perc_pats_expansion_rate,
        sigs,
        perc_comp_subsigs,
        basis_unique_states,
        basis_acc_states,
    );
    let init_dfa_cap = DfaCapacity::new(max_word, sigs, subsigs);

    zkp_driver::<Bn254, PairingVar, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S>(
        0,
        &format!("{}/sigs.dat", set1),
        &format!("{}/binexec.dat", set1),
        "data/small_data_set/reports/report.dat",
        b_write_cache,
        "small_20",
        &format!("{}/dfa.dat", set1),
        &format!("{}/ised.dat", set1),
        &format!("{}/ised_igc.dat", set1),
        max_word,
        &init_cp_cap,
        &init_sed_cap,
        &init_dfa_cap,
        &vec_decrease_level,
        num_circs,
        b_check_lkup,
    );
}

fn small_data_par<F: PrimeField>(b_check_lkup: bool) {
    get_global_config().snark_cache_dir = "small_20".to_string();
    get_global_config().b_read_snark_cache = false;
    get_global_config().b_write_snark_cache = false;
    get_global_config().range2_bit = 18;
    get_global_config().b_read_cache = false;
    let b_write_cache = !read_global_config().b_read_cache;
    let set1 = "data/debug/small_data_set/config_dfa";
    let max_word = 1;
    let sigs = 2;
    let subsigs = 4;
    let avg_pats_per_subsig = 3;
    let avg_active_pats_per_subsig = 2;
    let perc_comp_subsigs = 26;
    let basis_unique_states = 25 * 100;
    let basis_acc_states = 807;
    let basis_pats_in_trace = 1500;
    let perc_pats_expansion_rate = 114;

    let init_cp_cap = CpCapacity {
        max_word_len: max_word,
        basis_unique_states,
        subsigs,
        avg_pats_per_subsig,
    };
    let init_sed_cap = SedCapacity::new(
        max_word,
        read_global_config().range2_bit,
        subsigs,
        avg_pats_per_subsig,
        avg_active_pats_per_subsig,
        basis_pats_in_trace,
        perc_pats_expansion_rate,
        sigs,
        perc_comp_subsigs,
        basis_unique_states,
        basis_acc_states,
    );
    let init_dfa_cap = DfaCapacity::new(max_word, sigs, subsigs);

    let scan_files: Vec<String> = (1..=4)
        .map(|i| format!("{}/binexec_p{}.dat", set1, i))
        .collect();

    zkp_driver_adv::<Bn254, PairingVar, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S>(
        0,
        &format!("{}/sigs.dat", set1),
        scan_files,
        "data/small_data_set/reports/report.dat",
        b_write_cache,
        "small_20",
        &format!("{}/dfa.dat", set1),
        &format!("{}/ised.dat", set1),
        &format!("{}/ised_igc.dat", set1),
        max_word,
        &init_cp_cap,
        &init_sed_cap,
        &init_dfa_cap,
        &init_cp_cap,
        &init_sed_cap,
        &vec![1],
        2,
        b_check_lkup,
    );
}

fn full_clamav_setup<F: PrimeField>(b_check_lkup: bool) {
    full_clamav::<F>(b_check_lkup, true, true);
}

fn full_clamav_light<F: PrimeField>(b_check_lkup: bool) {
    preflight_full_clamav_cache_or_exit();
    full_clamav::<F>(b_check_lkup, true, false);
}

fn full_clamav_full<F: PrimeField>(b_check_lkup: bool) {
    preflight_full_clamav_cache_or_exit();
    full_clamav::<F>(b_check_lkup, false, false);
}

/// Verify the cache files produced by #3 (full_clamav_setup) exist.
/// If anything is missing, print an alert and exit before daemonizing.
fn preflight_full_clamav_cache_or_exit() {
    let root = proj_root();
    let required: [&str; 3] = [
        "data/cache/full_data/vec_sigs.txt",
        "data/cache/full_clamav/g16_main.key",
        "data/cache/full_clamav/g16_cp.key",
    ];
    let missing: Vec<PathBuf> = required
        .iter()
        .map(|p| PathBuf::from(&root).join(p))
        .filter(|p| !p.exists())
        .collect();
    if !missing.is_empty() {
        eprintln!();
        eprintln!("ERROR: Required cache files not found:");
        for p in &missing {
            eprintln!("  - {}", p.display());
        }
        eprintln!();
        eprintln!("Please run option #3 (full_clamav_setup) first to");
        eprintln!("generate the snark keys and data caches.");
        eprintln!();
        std::process::exit(1);
    }
}

fn full_clamav<F: PrimeField>(b_check_lkup: bool, b_light_test: bool,
    b_setup: bool) {
    get_global_config().snark_cache_dir = "full_clamav".to_string();
    get_global_config().b_write_snark_cache = b_setup;
    get_global_config().b_read_snark_cache = !b_setup;
    get_global_config().range2_bit = 26;
    get_global_config().b_light_test = b_light_test;
    get_global_config().min_subsigs = 150;
    get_global_config().min_basis_unique_states = 32;
    get_global_config().min_avg_pats_per_subsig = 6;
    get_global_config().n_par_snark = 2;
    get_global_config().n_par_snark_cp = 2;
    get_global_config().n_par_batch_claim = 8;

    get_global_config().b_read_cache = true;
    let b_write_cache = !read_global_config().b_read_cache;
    let set1 = "data/debug/full_clamav/config/";
    let max_word = 512 * 4;
    let sigs = 400;
    let subsigs = 580;
    let avg_pats_per_subsig = 8;
    let avg_active_pats_per_subsig = 2;
    let perc_comp_subsigs = 20;
    let vec_decrease_level = vec![2, 1];
    let num_circs = 3;
    let basis_unique_states = 2000;
    let basis_acc_states = 1260;
    let basis_pats_in_trace = 1400;
    let basis_acc_states_igc = basis_acc_states;
    let basis_pats_in_trace_igc = basis_pats_in_trace;
    let dfa_sigs = 6;
    let dfa_subsigs = 6;
    let perc_pats_expansion_rate = 104;
    let perc_pats_expansion_rate_igc = 2;

    let init_cp_cap = CpCapacity {
        max_word_len: max_word,
        basis_unique_states,
        subsigs,
        avg_pats_per_subsig,
    };
    let init_sed_cap = SedCapacity::new(
        max_word,
        read_global_config().range2_bit,
        subsigs,
        avg_pats_per_subsig,
        avg_active_pats_per_subsig,
        basis_pats_in_trace,
        perc_pats_expansion_rate,
        sigs,
        perc_comp_subsigs,
        basis_unique_states,
        basis_acc_states,
    );
    let init_dfa_cap = DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
    let init_cp_cap_igc = CpCapacity {
        max_word_len: max_word,
        basis_unique_states,
        subsigs: subsigs / 2,
        avg_pats_per_subsig,
    };
    let init_sed_cap_igc = SedCapacity::new(
        max_word,
        read_global_config().range2_bit,
        subsigs,
        avg_pats_per_subsig,
        avg_active_pats_per_subsig,
        basis_pats_in_trace_igc,
        perc_pats_expansion_rate_igc,
        sigs,
        perc_comp_subsigs,
        basis_unique_states,
        basis_acc_states_igc,
    );

    let scan_files: Vec<String> = if b_setup {
        (0..16)
            .map(|i| format!("{}/sample_1M_{}.dat", set1, i))
            .collect()
    } else {
        (0..8)
            .map(|i| format!("{}/binexec_p{}.dat", set1, i))
            .collect()
    };

    zkp_driver_adv::<Bn254, PairingVar, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S>(
        0,
        &format!("{}/main.dat", set1),
        scan_files,
        "data/debug/full_clamav/reports/report2.dat",
        b_write_cache,
        "full_data",
        &format!("{}/main_dfa.dat", set1),
        &format!("{}/needs_ised.dat", set1),
        &format!("{}/needs_ised_igc.dat", set1),
        max_word,
        &init_cp_cap,
        &init_sed_cap,
        &init_dfa_cap,
        &init_cp_cap_igc,
        &init_sed_cap_igc,
        &vec_decrease_level,
        num_circs,
        b_check_lkup,
    );
}

// --- Main Application ---

fn run_setup() -> (usize, usize) {
    println!("\n========================================================");
    println!("🔔 REMINDER: For optimal performance, you should run this");
    println!("   example with release profile:");
    println!("   cargo run --example main --release");
    println!();
    println!("   NOTE: Options #4 (light) and #5 (full) require the");
    println!("   snark keys and caches produced by #3 (setup). Run #3");
    println!("   first if you haven't already.");
    println!("========================================================\n");

    let mut table = Vec::new();
    let mut names = Vec::new();

    for opt in OPTIONS.iter() {
        table.push(vec![
            opt.name.cell(),
            opt.desc.cell(),
            opt.ram.cell().justify(Justify::Right),
            opt.time.cell().justify(Justify::Right),
            opt.jobs.cell().justify(Justify::Right),
        ]);
        names.push(opt.name);
    }

    let display_table = table
        .table()
        .title(vec![
            "Option".cell().bold(true),
            "Description".cell().bold(true),
            "RAM".cell().bold(true),
            "Est. Time".cell().bold(true),
            "Jobs".cell().bold(true),
        ])
        .bold(true);

    println!("Available Options:");
    println!("{}", display_table.display().unwrap());

    let selected_opt_idx = Select::with_theme(&ColorfulTheme::default())
        .with_prompt("Select an option to run")
        .default(0)
        .items(&names)
        .interact()
        .unwrap();

    let level_names: Vec<&str> = LOG_LEVELS.iter().map(|(name, _)| *name).collect();
    let default_level_idx = LOG_LEVELS.iter().position(|(_, level)| *level == LOG6).unwrap_or(7);

    println!("\nLog Levels:");
    let selected_log_idx = Select::with_theme(&ColorfulTheme::default())
        .with_prompt("Select a log level")
        .default(default_level_idx)
        .items(&level_names)
        .interact()
        .unwrap();

    (selected_opt_idx, LOG_LEVELS[selected_log_idx].1)
}

fn main() {
    let (selected_opt_idx, selected_log_level) = run_setup();

    // Set Global Config properties
    get_global_config().log_level = selected_log_level;

    let opt = &OPTIONS[selected_opt_idx];

    // Preflight checks for options that require prior setup.
    // Done here (before daemonize) so errors are visible on the terminal.
    if opt.name == "full_clamav_light" || opt.name == "full_clamav_full" {
        preflight_full_clamav_cache_or_exit();
    }

    println!("\nRunning configuration:");
    println!("  Option: {}", opt.name);
    println!("  Log Level: {}", LOG_LEVELS.iter().find(|(_, val)| *val == selected_log_level).unwrap().0);
    println!("\nExecution is switching to the background.");
    println!("All stdout and stderr will be redirected to /tmp/zkregplus.log");
    println!("Check the job execution logs at /tmp/log_job_<id>.txt.");
    println!("Config files for the jobs are available in their respective directories.");
    println!("Exiting main process...\n");

    let log_file = File::create("/tmp/zkregplus.log").unwrap();
    let log_file_err = log_file.try_clone().unwrap();

    let project_root = proj_root();
    let daemonize = Daemonize::new()
        .working_directory(project_root)
        .stdout(log_file)
        .stderr(log_file_err);

    match daemonize.start() {
        Ok(_) => {
            // We are now in the background child process
            println!("Background process started. Running option: {}", opt.name);
            (opt.func)(false); // Calling the function with b_check_lkup = false
            println!("Background process finished successfully.");
        }
        Err(e) => {
            eprintln!("Error starting daemon: {}", e);
        }
    }
}
