*******
run `python3 scripts/INSTALL.py` from the project root folder.
Do not run any python files here directly
*******

src_sig: source signatures (it CONTAINS the information of about 1 dozen
	sigs that are removed and why)
	-- note: the main.ldb and removed.ldb and README in its folder
	-- are in git.
	-- the signature sources are in git under src_sig/clamav/ and
	-- src_sig/ms_dlp/; nothing has to be downloaded for them.
	-- src_sig/chr17_variants/ is the exception: it is bulk genomic
	-- data, so INSTALL.py fetches it with the dna dataset.
	-- (the old main_cvd folder and its 7z download are retired --
	--  see attic/scripts/DOWNLOAD.py)
config: containing list of file samples and other config info.
samples: sample files to be scanned (CentOS binary execs and Enron emails)
licenses: licence texts for every redistributed component of the binexec
	corpus. Installed by INSTALL.py from the Zenodo deposit.
manifest: per-file provenance for the binexec corpus (sha256, originating
	RPM, upstream URL) plus PACKAGES.tsv mapping each source package to
	its licence and source RPM. Installed by INSTALL.py.
	-- see DATASET_BINEXEC.md for what the corpus contains and where
	--  each category came from.
paper_data: running result
cache: cache files for DFA and keys. Not included in git


