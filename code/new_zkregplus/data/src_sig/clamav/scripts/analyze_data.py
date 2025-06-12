# -------------------------
# Analyze the NON PM-Reg (general regex) patterns
# data and extract the all patterns
# NOTE to run this file: has to be single job mode
# change src/util/consts: B_SINGLE_JOB_MODE
#
# Input: data/clamav/categories/all_others.dat
# Output: easy.ldb (dat) and failed.ldb (dat)
# -------------------------
import re;
import os;

# return elements in arr2 but not in arr1
def diff(arr1, arr2):
	res = [];
	for x in arr1:
		if not x in arr2:
			res.append(x);
	return res;

#1. read all to processed
all_lines = open("data/clamav/categories/all_others.dat").readlines()[1:];
cmd = "target/release/zkregplus > dump.txt";

processed= 0;
successed = 0;
failed = 0;
round_id = 0;
fd = open("data/clamav/work/easy.ldb", "w");
fd.close();
fd = open("data/clamav/work/failed.ldb", "w");
fd.close();
f2 = open("data/clamav/work/easy.ldb", "w");
f3 = open("data/clamav/work/failed.ldb", "w");
f4 = open("data/clamav/work/easy.dat", "w");
f5 = open("data/clamav/work/complex.ldb", "w");
f6 = open("data/clamav/work/complex.dat", "w");
f2.write("# SUCCESSED \n");
f3.write("# FAILED \n");
#2. while loop until all processed
while processed<len(all_lines):
	round_id += 1;
	#2.0 rewrite the to_process.txt
	print("ROUND ID: ", round_id, "processed:", processed);

	#2.1 run the file, assuming single job mode
	# zkregexplus has timeout set in side - check utils/consts.rs
	cmd = "target/release/zkregplus automaton_time " + str(processed) + " > dump.txt";
	os.system(cmd);

	#2.2 analyze the file
	f1 = open("./dump.txt");
	lines = f1.readlines();
	arr_start = [];
	arr_success = [];
	arr_easy= []; #single NFA
	arr_complex= []; #complex MODE of DFAs
	r1 = re.compile('TO automaton"(.*?)"');
	r2 = re.compile("FINAL SIZE of NFA_easy: *(.*?):");
	r3 = re.compile("FINAL SIZE of NFA_complex: *(.*?):");
	for line in lines:
		m1 = r1.findall(line);
		m2 = r2.findall(line);
		m3 = r3.findall(line);
		if len(m1)>0: 
			arr_start.append(m1[0]);
			print("  -- process: ", line);
		if len(m2)>0: 
			arr_success.append(m2[0]);
			arr_easy.append(m2[0]);
			f4.write(line);
		if len(m3)>0: 
			arr_success.append(m3[0]);
			arr_complex.append(m3[0]);
			f6.write(line);
	processed += len(arr_start);
	successed += len(arr_success);
	for line in diff(arr_start, arr_success):
		print(" ## failed: ", line);
		f3.write(line + "\n");
	for line in lines:
		if line.find("FINAL SIZE")>=0:
			print("DEBUG USE 200: ", line);
			r4 = re.compile("FINAL SIZE.*: (.*):");
			fname = r4.findall(line)[0];
			#print("fname: ", fname, "line: ", line );
			if fname in arr_easy:
				print(" ## success easy: ", line);
				f2.write(fname + "\n");
			else:
				print(" ## success complex: ", line);
				f5.write(fname + "\n");
	print("ROUND ", round_id, "Processed:", len(arr_start), "Success:", len(arr_success), "Total Processed:", processed);

#3. close
print("-- ALL PROCESSED. Total: ", len(all_lines), "Success:", successed, "Failed", len(all_lines)-successed);
f1.close();
f2.close();
f3.close();
f4.close();
f5.close();
f6.close();


	


