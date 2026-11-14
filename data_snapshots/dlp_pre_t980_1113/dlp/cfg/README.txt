DLP working set  (data/paper_data/dlp/cfg)
==========================================

Inputs, capacity configs, and outputs for the DLP discharge experiments.
Mainly serve: full_dlp(), required by the paper.
 But for experimental purpose, this also consists files needed for
 	full_dlp_sample1,2,3() which runs smaller job
	but they share the same regex set.

Subfolders
----------

regex_pat/   The DLP regex-pattern DB.  SHARED by full_dlp and
             full_dlp_sample1/2/3.
               main_data_dlp_internationl.dat  source signatures
               main_dfa.dat                    list of sigs that need DFA
               needs_ised.dat                  list of sigs needs ised
               needs_ised_igc.dat              igc version of above
			   main_fanout.dat					sigs that need extra fanout

config/      Capacity-config files for circuits

jobs/        Splits of the corpus emails into parallel / smaller scan
             jobs.  
			 * final_enron_list.txt.gz
			 use run_full_dlp.py --jobs 8 (or any number) it will
			 split jobs automatically by reading 

corpus/      Information about the email corpus.
			 *  source.tgz which contains the following
               clean_enron_email.list      emails passing the zombie check
               pass_clean_enron_list.txt  Enron emails in pass_clean_email.list
			   							  that discharge clean
               fail_clean_enron_list.txt  Enron emails that fail discharge
               prune_high_cost.dat        high-cost files pruned from runs
			   * so final list is generated as main_data_dlp_international.dat
			   	  in the regex_pat/ folder. In summary
				  	Enron Emails (after zombie regex screen)
					  -> lean_email.list [eval_zombie.py in src_sig/dlp]
					  -> pass_clean_enron_list.txt [collect_discharge_fail]
					  -> prune_high_cost.dat [remove too high NEEDS configs]
			   => this folder is costly in disk and is compressed to tgz
			   => this folder is GENERATED AND COMPRESSED BY calling
			* full_dlp_email_list.dat
			   	  

