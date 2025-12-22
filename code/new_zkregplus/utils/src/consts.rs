/// Constants system wide
///
/// Created 01/04/2024

//pub const CLAMAV_SRC:&str = "./data/clamav/src/main.ldb";
//pub const CLAMAV_SRC:&str = "./data/clamav/src/test.ldb";
pub const TEST_MODE:bool = true; //if true disable the check of zero length pattern
pub const CLAMAV_GEN_REGEX:&str = "./data/clamav/categories/all_others.dat";
pub const CLAMAV_PCRE_REGEX:&str = "./data/clamav/categories/pcre.dat";
pub const CLAMAV_GEN_REGEX_SAMPLES:&str = "./data/clamav/categories/all_others_samples.dat";
pub const CLAMAV_PM_REGEX:&str = "./data/clamav/categories/pm_reg.dat";
pub const CLAMAV_PM_REGEX_SMALL:&str = "./data/clamav/categories/pm_reg_small.dat";
pub const SNORT_PCRE_REGEX:&str = "./data/snort/snort.ldb";
pub const B_DEBUG:bool = false;
//pub const CLAMAV_PM_REGEX:&str = "./data/clamav/categories/pm_reg_small.dat";
pub const CLAMAV_DST:&str = "./data/clamav/dest/";
pub const CRIT_PAT_FILE_PM:&str = "./data/clamav/dest/crit_pat_pm.dat";
pub const ALL_PAT_FILE_PM:&str = "./data/clamav/dest/all_pat_pm.dat";
pub const SIG_FILE_PM:&str = "./data/clamav/dest/sigs_pm.dat";
pub const CRIT_PAT_FILE_GENERAL:&str = 
	"./data/clamav/dest/crit_pat_general.dat";
pub const ALL_PAT_FILE_GENERAL:&str = "./data/clamav/dest/all_pat_general.dat";
pub const SIG_FILE_GENERAL:&str = "./data/clamav/dest/sigs_general.dat";
pub const LIST_EXEC:&str = "./data/list_exec.txt";
pub const LIST_EXEC_SAMPLE:&str = "./data/list_exec_sample.txt";
pub const LIST_EMAIL:&str = "./data/email_all.txt";
pub const B_SINGLE_JOB_MODE:bool = true;
/// always reload a data file even if it exists
pub const ALWAYS_INIT:bool = true;

pub const ADD_CHAIN_SIZE: usize = 64;

pub const ERR:usize = 0;
pub const WARN:usize = 1;
pub const LOG1:usize = 2;
pub const LOG2:usize = 3;
pub const LOG3:usize = 4;
pub const LOG4:usize = 5;
pub const LOG5:usize = 6;
pub const LOG6:usize = 7;
pub const LOG_LEVEL:usize = LOG1;

pub const DEFAULT_ACDFA_DA_BITS:usize = 2;
pub const DEFAULT_ACDFA_STATE_PART_BITS:usize=24;

/// limit of exact concat of disjuncted terms, e.g.,
/// given (a|b|c)(d|e|f) if the limit is 10, we will get
/// (ad|ae|af|bd...|cf), but if the limit is 8, we will retain
/// the original sequence
pub const COMBINATION_LIMIT:usize = 127; 
/// sometimes numbered repetions creates too long string
/// for fixed number reps, e.g., [^"]{1000, 2000}, the char
/// class has 255 chars, and the long string is repeated for many times
/// in this case, when length exceeding the limit, approximate the
/// substr with .
pub const REPEAT_LEN_LIMIT:usize = 1024*6; 
pub const RANGE_MAX: usize = 1<<31;
/// maximum number of PM sections
pub const MAX_PM_SECTIONS: usize = 32;
/// MIN len required for being a bag word
//pub const MIN_BAG_WORD_LEN:usize = 4;
pub const MIN_BAG_WORD_LEN:usize = 6;
pub const MIN_PM_WORD_LEN:usize = 4;
