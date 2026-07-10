//! Module data processing which provides parsers for ClamAV signatures,
//! and various logical operations (discharging methods)

/// data structures and type definitions
pub mod type_def;

/// AC-DFA customized for hex nibbles 
pub mod hex_acdfa;

/// string related utlity functions (split, validation, search related)
pub mod strings;

/// automata (DFA, NFA, ACDFA) related functions
pub mod fsa_utils;

/// preprocessor for (modifiers, decorators) of Clamav sig, mainly string
/// replacement operations.
pub mod preprocess;

/// pcre regex parser related functions
pub mod pcre;

/// clamav sig parser 
pub mod clamav;

/// discharge proofs (for discharging a file against collection of sigs)
pub mod discharge_proof;

/// A database of parsed Clamav signatures with preprocessed ACDFA information
pub mod clam_db;

/// Prover functions that generate discharge proof (i.e., prove
/// a file is free of malware per signature set)
pub mod discharge_prover;
