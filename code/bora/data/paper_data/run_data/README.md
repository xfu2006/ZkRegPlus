When PAPER_DATA.py completes a full run, it will put raw tgz into
task_tgz for all tasks, and then extract the data like data/raw_data
needed by scripts to generate figures, and it places all generated 
figures into figs, and compiles a single PDF (../pdf/list_figures.pdf)
that has all figures embedded.

-- scripts (the scripts that copied from paper folder to generate tables)
-- data (simulate the data folder in paper - once generated will be copied
	over to paper folder)
-- scratch (all temporary log files for each task will be placed here 
	and will be cleaned up once a task is completed)
-- task_tgz (full tgz file for each task - later python code will extract
	them and put the corresponding specific data.tgz into the
	data folder)
-- figs (the generated LaTeX figure/table fragments, one per gen_*.py)
