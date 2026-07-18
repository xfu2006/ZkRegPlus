When PAPER_DATA.py completes a full run, it will put raw tgz into
task_tgz for all tasks, and then extract the data like data/raw_data
needed by scripts to generate figures, and it places all generated 
figures into list_figs, and compile a single PDF that has all figures
embedded.

-- scripts (the scripts that copied from paper folder to generate tables)
-- data (simulate the data folder in paper - once generated will be copied
	over to paper folder)
-- scratch (all temporary log files for each task will be placed here 
	and will be cleaned up once a task is completed)
-- task_tgz (full tgz file for each task - later python code will extract
	them and put the corresponding specific data.tgz into the
	data folder)
-- list_figs (a simple pdf that has all figures generated)
