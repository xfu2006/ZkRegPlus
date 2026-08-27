*******
run `python3 scripts/INSTALL.py` from the project root folder.
Do not run any python files here directly
*******

START HERE -- paper_data/ is the only folder here that holds RESULTS.
Every table and figure in the paper is generated from it.  Everything
else is reproduction INPUT (signature corpora, scan samples, test
fixtures) or a cache, and none of it has to be read to check the paper.

paper_data: the paper's result data.  Its run_data/data/raw_data/ is
	delivered by paper_data_backup/bora_paper_data.tgz, not by git --
	only the .gitkeep markers are committed.
paper_data_backup: the offline copy of that tarball, plus a README
	explaining it.  INSTALL.py unpacks it and re-downloads it from the
	pinned Zenodo record if it is missing.  Nothing to read here.
src_sig: source signatures (it CONTAINS the information of about 1 dozen
	sigs that are removed and why)
	-- note: the main.ldb and removed.ldb and README in its folder
	-- are in git.
	-- the signature sources are in git under src_sig/clamav/ and
	-- src_sig/ms_dlp/; nothing has to be downloaded for them.
	-- src_sig/chr17_variants/ is the exception: it is bulk genomic
	-- data, so INSTALL.py fetches it with the dna dataset.
samples: sample files to be scanned (CentOS binary execs and Enron
	emails).  Installed by INSTALL.py; not kept in git.
debug: per-experiment test FIXTURES (DFA tables and scan configs) read by
	the Rust code and its tests.  Despite the name these are real
	inputs, not throwaway debug output -- 318 fixtures are tracked on
	purpose, spread over 17 subdirectories.  (`git ls-files data/debug`
	lists 320: those 318 plus debug/.gitignore and debug/README.md.)
	-- see debug/README.md for the group-by-group breakdown.
manifest: per-file provenance for the binexec corpus (sha256, originating
	RPM, upstream URL) plus PACKAGES.tsv mapping each source package to
	its licence and source RPM. Installed by INSTALL.py.
	-- see manifest/DATASET_BINEXEC.md for what the corpus contains
	--  and where each category came from.
licenses: licence texts for every redistributed component of the binexec
	corpus. Installed by INSTALL.py from the Zenodo deposit; not kept
	in git.
cache: cache files for DFA and keys. Not included in git
bigfiles: present only in the anonymous 4open snapshot.  Holds the xz
	pack of the 13 fixtures that are over 4open's 8 MB serving limit,
	plus their sha256 list; INSTALL.py restores them from it.  A normal
	git checkout has those fixtures loose and no bigfiles/ at all.
scripts: the data-preparation generators.  INSTALL.py copies gen_data.py
	into samples/ and runs it there -- do not run it from here.
	-- scripts/gen_data.py is NOT the same file as
	--  src_sig/clamav/scripts/gen_data.py, which generates the ClamAV
	--  pattern-match list.  They only share a name.
