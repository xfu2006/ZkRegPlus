# ----------------------------
# Measure the DFA size
# Created: Dr. Xiang
# 06/30/2024
#
# Rust cannot deal with memout nicely.
# We have to run multiple "threads" in multi-proces model
# ----------------------------
import subprocess;
import re;
import queue;
import threading;

# -----------------------------
# Utility functions
# -----------------------------

# return an array of numbers
def parse_arr(s_arr):
	s_arr = s_arr.replace('[', '');
	s_arr = s_arr.replace(']', '');
	s_arr = s_arr.replace(',', ' ');
	arr = s_arr.split();
	res = [];
	for x in arr: res.append( int(x));
	return res;

# retrieve all sigs from sig file
def get_sigs(sigfile):
	f1 = open(sigfile, "r");
	arrlines = f1.readlines();
	f1.close();
	res = [];
	for line in arrlines:
		if line[0]!="#":
			res.append(line);
	return res;

# retrieve the name of the sig
def get_name(sigline):
	arr = sigline.split(";");
	return arr[0];

# get the signautre idx in the sigfile
# run with timeout (input signame is for verification)
# return [filename, true/false for success, [.... data ....]
def run_dfa(sig_file, idx, timeout, signame):
	cmds = ["./target/release/zkregplus", "dfa_size", sig_file, str(idx), str(timeout)]; 
	res = subprocess.run(cmds, stdout=subprocess.PIPE);
	sres = str(res.stdout);
	r1 = re.compile("SIZE: (.*), (.*), \[(.*?)\]", re.DOTALL|re.MULTILINE); 
	matches = r1.findall(sres);
	if len(matches)>0:
		fname = matches[0][0];
		s_bres = matches[0][1];
		arr_sizes = matches[0][2];
		b_res = s_bres=="true";
		arr = parse_arr(arr_sizes);
		if fname!=signame:
			print("ERROR: signame:", signame, "extracted:", fname);
		return [b_res, fname, arr];
	else:
		return [False, signame, []]


# worker for work out the details of run_dfa
# takes out computing task one by one
# NOTE: work with q_tasks and q_results 
class Worker(threading.Thread):
	def __init__(self, id):
		super(Worker, self).__init__();
		self.id= id;
	
	def run(self):
		while not q_tasks.empty():
			mytask = q_tasks.get();
			res = run_dfa(SIG_FILE, mytask, TIMEOUT, get_name(arr_sigs[mytask]));
			print("WORKER ", self.id, " DONE one task: ", res);
			q_results.put( res );
	

# -----------------------------
# Main 
# -----------------------------
SIG_FILE = "data/clamav/categories/pcre.dat";
TIMEOUT = 20; #timeout in SECONDS
N_WORKERS = 5;

#1. produce the tasks
arr_sigs = get_sigs(SIG_FILE);
n = len(arr_sigs);
n = 10; # REMOVE LATER
q_tasks = queue.Queue(n); 
q_results = queue.Queue(n);
for x in range(n): q_tasks.put(x);

#2. consumer threads takes the tasks one by one
print("THREADS working now ...");
threads = [];
for id in range(N_WORKERS):
	threads.append( Worker(id) );
for th in threads:
	th.start();
for th in threads:
	th.join();

#3. summarize the results
total_subsigs = 0;
total_size = 0;
total_suc = 0;
total_fail = 0;
vec_failed = [];
for i in range(n):
	res = q_results.get();
	if res[0]==True:
		total_suc +=1;
		for x in res[2]: total_size += x;
		total_subsigs += len(res[2]);
	else:
		total_fail +=1;
		vec_failed.append(res[1]);

print("==== SUMMARY DFA Stats =====");
print("Failed:", total_fail, "Success:", total_suc);
print("Subsis (Success):", total_subsigs, "AVG DFA size:", total_size/total_subsigs);
print("----- Failed List -------");
for x in vec_failed:
	print(x);

