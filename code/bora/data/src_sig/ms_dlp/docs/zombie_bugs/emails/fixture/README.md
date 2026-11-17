# Same-sample Dlp e-mail set (Zombie vs BORA)

Drawn 2026-11-16 at repo HEAD 1cb9ba90 by scratch scripts in ../scripts/.

Pool. Raw Enron e-mails only (data/samples/email/src/maildir/...). An e-mail
is in the pool when it is in all three lists below.
- code/bora/data/src_sig/ms_dlp/docs/enron_list/pass_clean_enron_list.txt
  (non-e-mail lines such as README.md dropped).
- passed_clean_email.txt inside data/paper_data/dlp/cfg/corpus.tgz. This is
  BORA's own Dlp discharge verdict per e-mail, written 11/13 by
  gen_email_corpus_for_full_dlp (aggressive mode, main_data_dlp_internationl.dat,
  which is byte-identical to regex_bora_international/main_full.dat).
- data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz (the paper run list,
  which also drops 872 high-NEEDS e-mails).

Bands (bytes, inclusive). 1,000 arm 900 to 1,000. 2,000 arm 1,900 to 2,000.
4,000 arm 3,800 to 4,000.

Filters. The e-mail has CR LF CR LF. RE2 (case-insensitive, dot-all, Latin-1)
finds no hit for the 194 Zombie units (via run_zombie.extract_parts and
assemble_parts) or for the 10,166 BORA PCRE subsignatures of main_full.dat,
on the original, the padded copy, and the original wrapped in spaces.

Draw. Python random.Random(20261116). For arm 1000, then 2000, then 4000,
rng.sample(eligible sorted by path, 32) with the same rng object.

Padding. Each padded copy is the original followed by 0x0A bytes up to
exactly the arm length.

Files. emails/orig/<id>.eml, emails/padded/<id>.eml, ids.tsv (id, source
path, original bytes, arm, sha256 of original, sha256 of padded),
zombie_check.tsv (per e-mail count of the 194 unchanged Zombie units whose
circuit rejects the padded copy, from a direct evaluator of the generated
.zok files).
