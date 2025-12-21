import re;

f1 = open("dump2.txt", "r");
s = f1.read();
f1.close();

def analyze(pat):
	print("\n=== analyze: " + pat + " ====");
	r1 = re.compile(pat +": ([0-9]+)");
	arr = r1.findall(s);
	for i in range(len(arr)):
		arr[i] = int(arr[i]);
	print("ENTRIES: ", len(arr));
	isum = 0;
	for x in arr: isum += x;
	print("AVG", isum/len(arr));
	print("MAX", max(arr));
	cnt = 0;
	for x in arr: 
		if x>10*1000: cnt+=1;
	print("NUM greater than 10k:", cnt);

analyze("e1");
analyze("e2");
#analyze("e3");
#analyze("e4");
#analyze("e5");
