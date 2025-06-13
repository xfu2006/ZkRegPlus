#---------------------------------------------------------
# Created 01/12/2024
# Completed 01/17/2024
# Revised: 06/08/2024: fix the MIN_PATTERN_LOGIC
# Revised: 07/11/2024: final version for the data set
#
# It generates all categories of data and place the generated .dat (sig)
# files into ../categories
# --------------------------------------------------------
# Classifying signatures based on processing algorithm.
# The signatures are classified and saved to seprate files:
# (1) pm_reg.dat (pattern matching regex)
# (2) others.dat (including all of the following)
# (3) mods.dat (those excluded from pm_reg for modifiers of fullword a and
#    and more than 2 combinations)
# (5) expr_ops.dat (for complex expr ops such as [^..] and (a|b|c) types)
# (6) pcre.dat (for pcre regex)
# (7) small_pm_reg (those having small items to be excluded to improve
#     performance)
# ----------------------------------------------
# (8) non_reg.dat (for other ops: those that cannot be handled by regex due to
#    content based position related constraint)
# --------------------------------------------------------
# -- ALL sigs EXCEPT two (already filtered that raise fase positives
# - see README  in data/clamav/new_src/README
# are stored in main.dat
# *** do not be mislead by "filter" - in main.dat we actually
# *** still handle all the signatures. this python file simplily
# *** classifies the signatures into different types (that are easy to handle)
# --------------------------------------------------------
import sys;
import re;
from ahocorasick import *;

SRC = "../new_src/main.ldb"
LOG1 = 1;
LOG2 = 2;
LOG3 = 3;
LOG_LEVEL = LOG2;

# dump only when right log level set
def log(log_level, msg):
	if log_level<=LOG_LEVEL: print( msg + "\n")

# assert b_cond other exit and print msg
def myassert(b_cond, msg):
	if not b_cond: 
		print("ERROR: " + msg);
		sys.exit(1);

# parse the record
# record (line, {"name", "expr", "arr_sigs"})
def line_to_rec(line):
	myassert(line[0]!="#", "record line cannot start with #");	
	arr = line.split(";");
	d1 = {"name": arr[0], "desc": arr[1], "expr": arr[2], "arr_sigs": arr[3:]};
	return (line, d1);

# get all raw records
def get_all_records(src):
	arr_raw = [];
	f1 = open(SRC);
	lines = f1.readlines();
	f1.close();
	
	for line in lines:
		if line[0]=="#": continue;
		arr_raw.append( line_to_rec(line) );
	return arr_raw;

# filter out PCRE regex
def filter_pcre(arr_rec):
	arr_new = [];
	for (line, d1) in arr_rec:
		b_pcre = False;
		for sig in d1["arr_sigs"]:
			if sig.find("/")>=0:
				b_pcre = True;
		if not b_pcre: arr_new.append( (line, d1) );
		if b_pcre: log(LOG3, "filter PCRE: " + line);
	return arr_new;

# filter out those !(043...) type which has more than 3 hex nibbles in
# neg pattern (we do NOT handle it at this moment), but can be handled later.
def filter_by_neg_op(arr_rec):
	arr_new = [];
	r1 = re.compile("\!\([0-9a-f][0-9a-f][0-9a-f].*\)");
	for (line, d1) in arr_rec:
		b_ignore = False;
		for sig in d1["arr_sigs"]:
			if len(r1.findall(sig))>0:
				log(LOG3, "FOUND multi-byte negation: " + sig);
				b_ignore = True;
		if not b_ignore: arr_new.append( (line, d1) );
		if b_ignore: log(LOG3, "filter multi-byte negation: " + line);
	return arr_new;

# expand every 2 hex digit to wide
def expand_to_wide(s):
	s2 = "";
	cur_byte = "";
	cur_byte_id = 0;
	b_alpha_mode = True;
	for id in range(len(s)):
		c = s[id];
		if (c>="a" and c<="f") or (c>="0" or c<="9"):
			if b_alpha_mode:
				if cur_byte_id==0:
					cur_byte_id = 1;
					cur_byte = c;
				elif cur_byte_id==1:
					cur_byte_id = 0;
					cur_byte += c + "00";
					s2 += cur_byte;
				else:
					myassert(False,"ERROR: processing id: " + str(id) + " in: " + s);
			else:
				s2 += c;
		elif c=="*" or  c=="?":
			s2 += c;
		elif c=="{":
			s2 += c;
			b_alpha_mode = False;
		elif c=="}":
			s2 += c;
			b_alpha_mode = True;
		else:
			myassert(False, "ERROR unknown char: " + c);

	return s2;
	
# filter out by subsignature modifiers
# for w: expand each 2 hex digit with a 0000 (extra byte)
# for i: for i, add attribute case insensitive
# we only allow wi (disallow any other combination more than 2 modifiers)
# for f: we do not process for engineering convenience (fullword mode,
#   delinearated by non-alpha-nuumeirc chars)
# for a: we do not handle both aw case for engineering convenience
# Ref: see "modifiers" in https://docs.clamav.net/manual/Signatures/LogicalSignatures.html
def filter_mod(arr_rec):
	arr_new = [];
	for (line, d1) in arr_rec:
		b_remove = False;
		b_changed = False;
		b_case_ins = [False] * len(d1["arr_sigs"]);
		b_one_case_ins = False;
		for id in range(len(d1["arr_sigs"])):
			sig = d1["arr_sigs"][id].lower();
			arr = sig.split("::");
			new_str = arr[0];
			arrs = new_str.split(":");
			new_str = arrs[len(arrs)-1]; # to chop off the ":"
			if len(arr)>1:
				mod_str = arr[1].strip();
				if len(mod_str)>2: 
					log(LOG3, "filter by mod >2: " + mod_str);
					b_remove = True;
					break;
				if mod_str.find("f")>=0:
					log(LOG3, "filter by fullword mod: " + mod_str);
					b_remove = True;
					break;
				if mod_str.find("a")>=0 and mod_str.find("w")>=0:
					log(LOG3, "filter by both a and w: " + mod_str);
					b_remove = True;
					break;
				# NOW handle
				if mod_str.find("i")>=0:
					log(LOG3, "add ignore case: " + mod_str);
					b_case_ins[id] = True;
					b_one_case_ins = True;
					b_changed = True;
				if mod_str.find("w")>=0:
					new_str = expand_to_wide(new_str);
					b_changed = True;
					log(LOG3, "expand from : " + arr[0] + " -> " + new_str);
			d1["arr_sigs"][id] = new_str;
		d1["b_case_ins"] = b_case_ins;
		if not b_remove: arr_new.append( (line, d1) );
		if b_remove: log(LOG3, "filter by mod: " + line);
	return arr_new;

# has to remove all content position decorators
# such as EP, Sl+...
# only "\d+" is allowed (which stands for absolute offset from
# the beginning of string) and rewrite it as .{num}
# this also INCLUDES expression with , operator such as (1>2,3)
# which we cannot handle easily by re-writing
def filter_pos(arr_rec):
	arr_new = [];
	r1 = re.compile("^[0-9]+$");
	for (line, d1) in arr_rec:
		b_filter = False;
		for id in range(len(d1["arr_sigs"])):
			sig = d1["arr_sigs"][id];
			arr = sig.split("::");
			sig = arr[0];
			arr = sig.split(":");
			if len(arr)>1:
				pos_str = arr[0];
				if pos_str=="*" or len(r1.findall(pos_str))>0:
					log(LOG3, "pos_str pass: " + pos_str);
				else:
					log(LOG3, "pos_str filered: " + pos_str);
					b_filter = True;
		if d1["expr"].find(",")>=0:
				log(LOG3, "special expr containing , filered: " + d1["expr"]);
				b_filter= True;
		if not b_filter: arr_new.append( (line, d1) );
		else: log(LOG3, "filter by pos_str: " + line);
	return arr_new;

# filter those which has (, ), | and other operators
def filter_others(arr_rec):
	arr_new = [];
	r1 = re.compile("^[0-9a-f*?{}-]+$");
	for (line, d1) in arr_rec:
		b_filter = False;
		for id in range(len(d1["arr_sigs"])):
			sig = d1["arr_sigs"][id];
			if len(r1.findall(sig))==0:
				log(LOG3, "filter by unhandled ops: " + sig);
				b_filter = True;
		if not b_filter: arr_new.append( (line, d1) );
		else: log(LOG3, "filter by other ops: " + line);
	return arr_new;

# format and remove all special ops such as {..} by ?
# only non-alpha-numeric char would be ?
def reformat_str(s):
	old_s = s + "";
	s = re.sub(r"{.*?}", "?", s);
	s  = re.sub(r"\[.*?\]", "?", s);
	s = re.sub(r"\*", "?", s);
	if s!=old_s:
		log(LOG3, "reformat " + old_s + " => " + s)
	return s;

def extract_pattern_from_sig(sig):
	res = set([]);
	r1 = re.compile("^[0-9a-f?]+$");
	r2 = re.compile("[0-9a-f]+")
	sig = reformat_str(sig);
	myassert(len(r1.findall(sig))>0, "invalid sig: " + sig);
	matches = r2.findall(sig);
	for x in matches:
		res.add(x);
	return res;

# return set of words from a record
def extract_patterns(rec):
	(line, d1) = (rec);
	r1 = re.compile("^[0-9a-f?]+$");
	r2 = re.compile("[0-9a-f]+")
	res = set([]);
	for sig in d1["arr_sigs"]:
		res1 = extract_pattern_from_sig(sig);
		res = res.union(res1);
	return res;

def extract_all_patterns(arr_rec):
	set_all = set([]);
	for rec in arr_rec:
		words = extract_patterns(rec);
		set_all = set_all.union(words);
	return set_all;

# return the new arr_rec by filter
# require: pattern cannot be contained in the avoid set, 
# if any pattern has length less than min_pattern_len, ignore the 
# the entire record; if total number of patterns greater than
# the bar ignore the entire record
def filter_by_patterns(arr_rec, avoid_set, max_num_pattern, min_pattern_len, freq_bar):
	arr_new = [];
	for rec in arr_rec:
		fix_words = extract_patterns(rec);
		b_ignore = False;
		if len(fix_words)>max_num_pattern*len(rec[1]):
			log(LOG3, "IGNORE for |patterns|>" + str(max_num_pattern) +  ", Details: " + str(rec) + ", num_patterns: " + str(len(fix_words)) + ", patterns: " + str(fix_words));
			b_ignore = True;
		max_pat_len = 0;
		max_pat = "";
		for x in fix_words:
			if len(x)>max_pat_len: max_pat_len = len(x);
		if max_pat_len<min_pattern_len:
			log(LOG1, "IGNORE for pattern len < "+ str(min_pattern_len) + ", Details: " + max_pat  + ", Sig: " + str(rec) + ", patterns: " + str(fix_words));
			b_ignore = True;
		if len(fix_words.intersection(avoid_set))>0:
			log(LOG3, "IGNORE for containing: " + str(fix_words.intersection(avoid_set)) +  ", Details: " + str(rec));
			b_ignore = True;
		if not b_ignore: arr_new.append(rec);
	log(LOG2, "*************************\n" + "Filter by patterns: " + "freq bar: " + str(freq_bar) + " => avoid_set: " + str(len(avoid_set)) + ", max_num_pattern: " + str(max_num_pattern) + ", min_pattern_len: " + str(min_pattern_len) + "\n" + "Original Sigs: " + str(len(arr_rec)) + " ==> " + str(len(arr_new)) + "\n*************************\n");
	return arr_new;


# filter those constraints that that need to count
# on patterns that ARE NOT SINGLE WORD PATTERN
# also those containing "," (like 1>1,2) expressions
def filter_by_expr(arr_rec):
	arr_new = [];
	r1 = re.compile("\d+[=><]\d+");
	r2 = re.compile("^[0-9a-f]+$");
	r3 = re.compile("(\(\d+([|&]\d+)*\)[=><]\d+)");
	for (line, rec) in arr_rec:
		expr = rec["expr"];
		b_ignore = False;
		if expr.find(",")>=0: b_ignore=True;
		if expr.find("<")>=0 or expr.find(">")>=0 or expr.find("=")>=0:
			arrm = r1.findall(expr);
			for m in arrm:
				arr = re.split(r"[=<>]", m);
				myassert(len(arr)==2, "ERROR in split: " + m);
				id = int(arr[0]);
				sig = rec["arr_sigs"][id];
				if len(r2.findall(sig))>0:
					log(LOG3, "PASS sig: " + sig + ", line: " + line);
				else:
					log(LOG3, "FAIL complex sig: " + sig + ", line: " + line);
					b_ignore = True;
		if len(r3.findall(expr))>0:
			for m in r3.findall(expr):
				r4 = re.compile("\d+");
				nums = r4.findall(m[0]);
				for id in nums[0:-1]:
					i_id = int(id);
					sig = rec["arr_sigs"][i_id];
					if len(r2.findall(sig))>0:
						log(LOG3, "PASS sig: " + sig + ", line: " + line);
					else:
						log(LOG3, "FAIL complex sig: " + sig + ", line: " + line);
						b_ignore = True;

		if not b_ignore: arr_new.append( (line, rec) );
	return arr_new;


# return all bin file path
def get_all_binfile():
	arrlines = open("./list_exec.txt").readlines();
	# REMOVE LATER -----------
	#arrlines = arrlines[0:10];
	# REMOVE LATER ----------- ABOVE
	res = [];
	for line in arrlines:
		res.append( line.strip() );
	return res;

# convert one byte to string
def byte_to_str(bt):
	low = bt % 16;
	high = bt //16;
	#s = hex(low)[2:] + hex(high)[2:];
	s = hex(high)[2:] + hex(low)[2:];
	return s;

# return hex of every 4 bites
def read_binfile(fpath):
	f1 = open(fpath, "rb");
	s = "";
	data = f1.read();
	for bt in data:
		s += byte_to_str(bt);
	f1.close();
	return s;

# return the AC-DFA
def build_ac_dfa(set_words):
	log(LOG2, "build AC-DFA for wordset: " + str(len(set_words)));
	fsa = Automaton();
	for idx, key in enumerate(set_words):
		fsa.add_word(key, (idx, key));
	fsa.make_automaton();
	log(LOG2, "AC-DFA stats: " + str(fsa.get_stats()) );
	return fsa;


# run string over fsa
# report stats
# return (set_max_pat, d1)
# set_max_pat: those patterns that appear more frequently than bar
#  (note: set_max_pat is RESTRICTED by the set of patterns of related sigs)
# d1 has the following data: file_len, num_final_states, set_sigs, total_steps 
def run_file(fsa, s, fname, bar, set_critical_pat, d_critical, db_sig):
	log(LOG3, "run_file: " + fname + ", length: " + str(len(s)));
	dict1 = {};
	set_max_pats = set([]);

	#1. compute the list final states
	arr = fsa.iter(s);
	arr_final_states = [];
	set_patterns = set([]);
	set_sigs = set([]);
	for (idx, (last_idx, word))  in arr:
		arr_final_states.append(last_idx);
		set_patterns.add(word);
		if word in dict1:
			dict1[word] +=1;
		else:
			dict1[word] = 1;
	set_critical_collected = set_critical_pat.intersection(set_patterns);
	for x in set_critical_collected:
		set_sigs = set_sigs.union( d_critical[x] ); 

	#2. collect max pats above bar
	for x in dict1.keys():
		val = dict1[x];
		if val>bar:
			set_max_pats.add(x);

	#3. compute the total steps
	total_steps = 0;
	for sig_name in set_sigs:
		rec = db_sig[sig_name];
		steps = get_total_steps(rec);
		total_steps += steps;

	#4. build up data
	dres = {"file_len" : len(s), "packed_acc_path_len" : len(arr_final_states),  "set_sigs" : set_sigs, "total_steps" : total_steps};
	log(LOG3, str(dres));
	return (set_max_pats, dres);


# return (arr_dict, set_max_sigs)
# arr_dict is an array of dict which contains the matching of sigs
# set_max_sigs contains the max_signature contained in each file
# set_critical_pat are critical patterns
# d_critical maps set_critical to related signatures
def run_all_files(set_words, bar, set_critical, d_critical, db_sig):
	files = get_all_binfile();
	fsa = build_ac_dfa(set_words);
	arr_dict = [];
	freq_pats = set([]);
	for fpath in files:
		print("processing: " + fpath);
		s = read_binfile(fpath);
		(s1, dict1) = run_file(fsa, s, fpath, bar, set_critical, d_critical, db_sig);
		arr_dict.append(dict1);
		freq_pats = freq_pats.union(s1);
	return (arr_dict, freq_pats);

# assume array are numbers
def report_arr(title, arr):
	print(title + ": AVG: " + str(sum(arr)/len(arr)) + ", MIN: " + str(min(arr)) + ", MAX: " + str(max(arr)));

# report stats
def summarize(title, arr_res, set_exclude_patterns, used_patterns, arr_rec):
	print(" ================================= ");
	print("       " + title);
	print("FILES:", len(arr_res), "Excluded Patterns: " + str(len(set_exclude_patterns)) + ", Used Patterns: " + str(len(used_patterns)));
	print(" ================================= ");

	arr_len = [];
	arr_acc_len = [];
	arr_sigs = [];
	arr_total_steps = [];
	for x in arr_res:
		arr_len.append( x["file_len"] );
		arr_acc_len.append( x["packed_acc_path_len"] );
		arr_sigs.append( len(x["set_sigs"]) );
		arr_total_steps.append( x["total_steps"] );
	report_arr("File Size", arr_len);
	report_arr("Packed Acc Path of Final States", arr_acc_len);
	report_arr("Number of NearMiss Signatures", arr_sigs);
	report_arr("Total Steps in Circuit", arr_total_steps);
	print(" =============================== \n");
		

			

# return the frequency of words
def analyze_pat(set_words, arr_rec, top_n):
	dict1 = {}
	dict2 = {};
	#1. establish dictionary map from each pattern to arr_rec 
	for (line, d1) in arr_rec:
		name = d1["name"];
		pats = extract_patterns( (line, d1) );
		for x in pats:
			if x in dict1.keys():
				dict1[x].add(name);
			else:
				dict1[x] = set([name]);

	#2. establish dict2
	for x in dict1.keys():
		dict2[x] = len(dict1[x]);
	dict3 = dict(sorted(dict2.items(), reverse=True, key=lambda item: item[1]))
	#print(dict3);

	#3. show the topn
	id = 0
	if top_n>0: log(LOG2, "===== Top " + str(top_n) + " patterns ======"); 
	for x in dict3.keys():
		id+=1;
		if id>top_n: break;
		#print(x + ": " + str(dict3[x]) + ", Details: " + str(dict1[x]));
		print(x + ": " + str(dict3[x]));

	return dict3;


# return a set of words
# for each signature, extract the longest word for each subsig
# except the =0 case and <x case subsigs
# return (set_words, dictionary that map each word to number of related sigs)
def get_critical_pat(rec, dict_words):
	(line, d1) = rec;
	set_res = set([]);
	set_bad_ids = set([]);
	r1 = re.compile("(\d+)<\d+");
	r2 = re.compile("(\d+)=0");
	arr_bad_ids = r1.findall(d1["expr"]);
	#if len(arr_bad_ids)>0: print("DEBUG USE 102", arr_bad_ids, d1["expr"]);
	for x in arr_bad_ids: set_bad_ids.add( int(x) );
	arr_bad_ids = r2.findall(d1["expr"]);
	#if len(arr_bad_ids)>0: print("DEBUG USE 102", arr_bad_ids, d1["expr"]);
	for x in arr_bad_ids: set_bad_ids.add( int(x) );

	n = len(d1["arr_sigs"]);
	arr_id = [];
	for id in range(n): arr_id.append(id);
	set_arr_id = set(arr_id);
	set_ids = set_arr_id - set_bad_ids;

	b_and_mode = d1["expr"].find("|")<0;
	for x in set_ids:
		sig = d1["arr_sigs"][x];
		pats = extract_pattern_from_sig(sig);
		best_u = "";
		id = 0;
		for u in pats:
			if id==0: best_u = u;
			if dict_words[u]<dict_words[best_u]: best_u = u;
			id += 1;
		set_res.add(best_u);

	if b_and_mode: # juse need to pick one
		id = 0;
		best_u = "";
		for x in set_res:
			if id==0: best_u = x;
			if dict_words[x]<dict_words[best_u]: best_u = x;
			id += 1;
		set_res = set([best_u]);

	return set_res;
		
# return (set_critical_patterns, dict of appearance of each pattern)
# dict_words has the frequency of word patterns for making selection
def get_all_critical_pat(arr_rec, dict_words):
	b_debug = True;
	top_n = 0;
	set_res = set([]);
	d1 = {};

	for rec in arr_rec:
		set1 = get_critical_pat(rec, dict_words);
		set_res = set_res.union(set1);
		for x in set1:
			if x in d1.keys():
				d1[x].add(rec[1]["name"]);
			else:
				d1[x] =set([rec[1]["name"]]);
	
	dict1 = {};
	for x in d1: dict1[x] = len(d1[x]);

	dict2 = dict(sorted(dict1.items(), reverse=True, key=lambda item: item[1]))
	max_sigs = 0;
	total = 0;
	for x in dict2.keys(): 
		total+=dict2[x];
		if dict2[x]>max_sigs: max_sigs = dict2[x];

	log(LOG2, " *** AVG each criticial pat has related # sigs: " + str(total/len(dict2.keys())) + ", max # sigs: " + str(max_sigs));

	if top_n>0:
		id = 0;
		print("\n ----- top " + str(top_n) + " critical rules " + " -------");
		for x in dict2.keys():
			id+=1;
			if id>top_n: break;
			log(LOG2, x + ": " + str(dict2[x]));
		total = 0;
		print(" ------------------------------ ");
	
	return (set_res, d1);

# return a dictionary of records so that 
# info can be easily processed
def build_sig_db(arr_rec):
	res = {}
	for (line, rec) in arr_rec:
		rec["line"] = line;
		res[rec["name"]] = rec;
	return res;

# for a signature, estimate the total number of
# steps in arithmetic circuit (total sum of components)
def get_total_steps(rec):
	total = 0;
	for sig in rec["arr_sigs"]:
		sig = reformat_str(sig);
		pats = extract_pattern_from_sig(sig);
		total += len(pats);
	return total;

# collect the set of names
def get_names(arr1):
	res = set([]);
	for (line, rec) in arr1:
		name = rec["name"];
		res.add(name);
	return res;

# get the difference of two records
def diff(arr1, arr2):
	res = [];
	names_2 = get_names(arr2)
	for (line, rec) in arr1:
		name = rec["name"];
		if not name in names_2:
			res.append( (line, rec) );
	return res;

# write the flie
def write_file(fpath, line1, arr):
	f1 = open(fpath, "w");
	f1.write(line1 + "\n");
	for (line, rec) in arr:
		f1.write(line);
	f1.close();

# -----------------
# MAIN FUNCTION
# -----------------
MAX_NUM_PATTERN = 50000; # has >MAX_NUM_PATTERN per subsig be removed (unused)
MIN_PATTERN_LEN = 20; # <MIN_PATTERN_LEN will be removed 
FREQ_BAR = 64*1024; # if appears more than FREQ_BAR, will be removed from pattern set

arr_raw = get_all_records(SRC);
# --- REMOVE LATER ------
#arr_raw = arr_raw[0:1000];
# --- REMOVE LATER ------ ABOVE
log(LOG1, "RAW Records: " + str( len(arr_raw)) );

arr_new = filter_pcre(arr_raw);
log(LOG2, "After filter " + str( len(arr_raw) - len(arr_new) ) + " PCRE sigs: " + str( len(arr_new) ) );
arr_pcre = diff(arr_raw, arr_new);

arr_new2 = filter_pos(arr_new);
log(LOG2, "After filter " + str( len(arr_new) - len(arr_new2) ) + " pos: " + str( len(arr_new2) ) );
arr_pos = diff(arr_new, arr_new2);

arr_new3 = filter_mod(arr_new2);
log(LOG2, "After filter " + str( len(arr_new2) - len(arr_new3) ) + " mods: " + str( len(arr_new3) ) );
arr_mods = diff(arr_new2, arr_new3);

arr_new3_5 = filter_by_neg_op(arr_new3);
log(LOG2, "After filter " + str( len(arr_new3) - len(arr_new3_5) ) + " by neg multi-byte ops: " + str( len(arr_new3) ) );
arr_other_neg_mul_byte_ops = diff(arr_new3, arr_new3_5);

arr_new4 = filter_others(arr_new3_5);
log(LOG2, "After filter " + str( len(arr_new3_5) - len(arr_new4) ) + " by other ops: " + str( len(arr_new4) ) );
arr_other_ops = diff(arr_new3_5, arr_new4);

arr_new5 = filter_by_expr(arr_new4);
log(LOG2, "After filter " + str( len(arr_new4) - len(arr_new5) ) + " by expr ops: " + str( len(arr_new5) ) );
arr_expr = diff(arr_new4, arr_new5);

set_words = extract_all_patterns(arr_new5);
dict_words = analyze_pat(set_words, arr_new5, 0);
(set_critical, d_critical) = get_all_critical_pat(arr_new5, dict_words);
db_sig = build_sig_db(arr_new5); 
(arr_dict1, set_freq_pat) = run_all_files(set_words, FREQ_BAR, set_critical, d_critical, db_sig);
summarize("BEFORE remove freq patterns", arr_dict1, set([]), set_words, arr_new5);
set_freq_pat = [];
arr_new6 = filter_by_patterns(arr_new5, set_freq_pat, MAX_NUM_PATTERN, MIN_PATTERN_LEN, FREQ_BAR);
log(LOG2, "After filter " + str( len(arr_new5) - len(arr_new6) ) + " by extracted pattern constraints and small crit patterns: " + str( len(arr_new6) ) );

set_words = extract_all_patterns(arr_new6);
db_sig = build_sig_db(arr_new5); 
(arr_dict2, set_freq_pat2) = run_all_files(set_words, FREQ_BAR, set_critical, d_critical, db_sig);
summarize("AFTER remove freq patterns", arr_dict2, set_freq_pat, set_words, arr_new6);
arr_small_pm_reg = diff(arr_new5, arr_new6);


# WRITE the file
path = "../categories/";
write_file(path + "pcre.dat", "# Those containing PCRE exprs", arr_pcre);
write_file(path + "pos.dat", "# Those not regular due to pos constraints", arr_pos);
write_file(path + "mods.dat", "# Those have complex modifiers such as fullwords and combinations more than 2 modifiers", arr_mods);
write_file(path + "other_ops.dat", "# Those have ops in sigs such as (a|b|c) or [^..] that are not supported by PM-Reg", arr_other_ops);
write_file(path + "expr.dat", "# Those have pattern needs but counting is not a fixed word pattern, so that they cannot be conveniently omdeled by PM-Reg ", arr_expr);
write_file(path + "small_pm.dat", "# Those have small patterns that affect performance ", arr_small_pm_reg);
write_file(path + "pm_reg.dat", "# PM Reg data set", arr_new6);
write_file(path + "neg_op.dat", "# negative operators", arr_other_neg_mul_byte_ops);

# exclude arr_pos because it CANNOT be handled by Regex anyway
# also exclude neg_mul_byte (but it can be handled later) - we do not
#    handle it now for engineering convenience
arr_all_others = arr_mods + arr_other_ops + arr_expr + arr_small_pm_reg;
#compared with all_others: main_data it has pcre, pm_reg.dat 
# and arr_pos as extra, and also arr_other_neg_mult_byte 
# in summary it has all the signatures from main.ldb
main_data = arr_new6 + arr_pcre + arr_pos + arr_mods + arr_other_ops + arr_expr + arr_small_pm_reg + arr_other_neg_mul_byte_ops; 
#
write_file(path + "all_others.dat", "# All other regex other than PM-Regex data set", arr_all_others);
write_file(path + "main.dat", "#ALL signatures (already manually excluded two that causes false positives, see data/clamav/new_src/README", main_data);


