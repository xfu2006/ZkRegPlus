import re;

s = open("dump2.txt", "r").read();
arr_str = re.findall(r'sig: (.*?),', s);
unique_sigs = set(arr_str);
for x in unique_sigs:
	print(x);
print("NUMBER of sigs:", len(unique_sigs));
