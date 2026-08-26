Offline backup of the paper's raw run data.  Nothing here needs to be
read to check the paper -- the results themselves live in ../paper_data/.

bora_paper_data.tgz
	The raw run logs and per-experiment archives that fill
	../paper_data/run_data/data/raw_data/.  Only the .gitkeep markers
	of that tree are committed, so this tarball (or a fresh download of
	it) is what puts the numbers there.

	sha256  851bf9434c450af2696a2add9e55189764f3f4d6e8f4607bd5dda77aefab7bb0
	source  https://doi.org/10.5281/zenodo.22057943  (concept DOI)

	scripts/INSTALL.py verifies this digest, unpacks the raw-run folders
	into ../paper_data/, and keeps the tarball here as the offline copy
	so a re-install costs no network.  If the file is absent INSTALL.py
	downloads it again from the pinned Zenodo version record, so losing
	it is not fatal.

	The tarball also carries its own BORA_PAPER_DATA_README.txt, which
	INSTALL.py unpacks into this folder.

Note for artifact reviewers: this folder is omitted from the anonymous
4open.science snapshot -- at 37 MB the tarball is far over what that
service will serve, and INSTALL.py fetches it from Zenodo instead.
