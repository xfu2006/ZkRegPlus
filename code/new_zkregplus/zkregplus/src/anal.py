import re;

f1 = open("6651.5xt", "r");
text = f1.read();
f1.close();

r1 = re.compile("DEBUG USE 6651.LEFT.Details.*?inv_left: (.*?),");
arr_left = r1.findall(text);
dict_left = {};
for x in arr_left:
	if not x in dict_left.keys():
		dict_left[x] = 1;
	else:
		dict_left[x] += 1;

r2 = re.compile("DEBUG USE 6651.RIGHT.Details:.*?m_i: (.*?), wtns: (.*?),");
arr_right = r2.findall(text);
dict_right = {};
for rec in arr_right:
	wd = rec[1];
	if rec[0]=="":
		cnt = 0;
	else:
		cnt = int(rec[0]);
	if cnt!=0:
		if wd in dict_right.keys():
			if dict_right[wd] != cnt:
				print("ERROR duplicates for wd: ", wd, "old count: ", dict_right[wd], "new count", cnt);
		else:
			dict_right[wd] = cnt;

print("dict_left: ", len(dict_left), ", dict_right", len(dict_right));
print("--- check left side ---");
for x in dict_left.keys():
	leftval = dict_left[x];
	rightval = dict_right[x];
	if leftval!=rightval:
		print("KEY: ", x, "leftval: ", leftval, "rightval", rightval);
print("--- check right side ---");
for x in dict_right.keys():
	leftval = dict_left[x];
	rightval = dict_right[x];
	if leftval!=rightval:
		print("KEY: ", x, "leftval: ", leftval, "rightval", rightval);
	
