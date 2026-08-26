# ----------------------------------------
# BORA paper author
# Created 06/06/2025
#
# This is used to merge small binary executables into larger files
# for more efficient folding.
# ----------------------------------------
import os;
import sys;

# return all files info sorted first by size and then
# by file name.
def get_file_info(dir_path):
	#1. get all file info
	entries = os.scandir(dir_path);
	vec_all = [];
	for e in entries:
		if e.is_file():
			file_size = e.stat().st_size;
			info = {"name":e.name, "file_size":file_size};
			vec_all.append(info);

	#2. sort all entries based on file size first and then name 
	for i in range(len(vec_all)):
		for j in range(len(vec_all)-1):
			if vec_all[j]["file_size"]>vec_all[j+1]["file_size"] or (vec_all[j]["file_size"]==vec_all[j+1]["file_size"] and vec_all[j]["name"]>vec_all[j+1]["name"]):
				temp = vec_all[j];
				vec_all[j] = vec_all[j+1];
				vec_all[j+1] = temp;

	return vec_all;

# compute the total sum of file sizes
def sum_filesize(vec_finfo):
	s = 0;
	for rec in vec_finfo: s+= rec["file_size"];
	return s;

# assert a condition
def my_assert(bcond, msg):
	if not bcond:
		print("ERROR: " + msg);
		sys.exit(1);

# return the merge plan (for files smaller than the given target size)
# try merge at the best effort following the ascending list
# return {"target_fname", list_src} when list_files len() is 1,
# target_fname must match the only file in the list.
def get_merge_plan(f_info, target_size):
	start = 0;
	res = [];
	while start < len(f_info):
		#1. search the next list and merge small files
		# if the file is already large enough (>target_size), just add one file
		list_src = [];
		end = start;
		while sum_filesize(list_src) + f_info[end]["file_size"]<target_size:
			list_src.append(f_info[end]);
			end += 1;
		if len(list_src)==0: # add single file (allow greater than target_size)
			list_src.append(f_info[end]);
			end+=1;

		my_assert(len(list_src)>0, "list_src len is 0");
		if len(list_src)>1: #merged files must be smaller than target size
			my_assert(sum_filesize(list_src)<=target_size, "sumfilesize > target!");

		#2. determine target_name
		nameid = len(res);
		if len(list_src)>1:
			target_name = "merged_" + str(nameid);
		else:
			target_name = list_src[0]["name"];
		entry = {"target_name": target_name, "list_src": list_src};
		res.append(entry);

		#3. advance
		start = end;

	#check and return
	total_files = 0;
	for rec in res:
		total_files += len(rec["list_src"]);
	print("Merged: total_files:", total_files, "len(f_info)", len(f_info));
	my_assert(total_files==len(f_info), "total_files!=f_info");
	return res;

# execute merge plan
# execute the plan by taking files from src_dir and put results in
# dest dir. Split size is the size to split a file
def exec_merge_plan(src_dir, dest_dir, plan, split_size):
	frec = open("merge_records/"+src_dir+".txt", "w");
	for item in plan:
		if len(item["list_src"])>1:
			cmd = "cat ";
			srec = item["target_name"] + ": ";
			for rec in item["list_src"]:
				cmd += " " + src_dir +"/" + rec["name"];
				srec += " " + rec["name"];
			cmd += " > " + dest_dir + "/" + item["target_name"];
			print("MERGE cmd: " + cmd);
			os.system(cmd);
			frec.write(srec + "\n");
		if len(item["list_src"])==1:
			rec = item["list_src"][0];
			if rec["file_size"]<split_size:
				cmd = "cp " + src_dir + "/" + rec["name"] + " " + dest_dir;
				print("COPY cmd: " + cmd);
				os.system(cmd);
			else:
				cmd = "split -b " + str(split_size) + " --numeric-suffixes=0 --suffix-length=2 " + src_dir + "/" + rec["name"] + " " + dest_dir + "/" + rec["name"]+"__";
				print("SPLIT cmd: " + cmd);
				os.system(cmd);

	

#------------------------------
# MAIN function 
#------------------------------
TARGET_SIZE = 128*1024; 
TARGET_DIR = "binexec_merged128k";
SRC_DIR = "binexec";
SPLIT_SIZE = 32 * 1024 * 1024 - 100 * 1024; #leave a little room less than 32M
	# the reason is that in the last segment when we perform
	# the calcluation of allowed positions (cur_pos + allowed_range)
	# if we cut the size to 32M - allowed_range this saves
	# conditional assignment cost in the discharge_sig.rs component.
	# we know that allowed_range is no more than 100kb in data.

os.system("rm -fr " + TARGET_DIR);
os.system("mkdir " + TARGET_DIR);

mylist = get_file_info("binexec");
plan = get_merge_plan(mylist, TARGET_SIZE);
exec_merge_plan(SRC_DIR, TARGET_DIR, plan, SPLIT_SIZE);
print("Destination: " + TARGET_DIR, "Src: " + SRC_DIR);
print("MERGE files with size < " + str(TARGET_SIZE) + ", and split large files size > " + str(SPLIT_SIZE));
print("DATA merge completed.");





