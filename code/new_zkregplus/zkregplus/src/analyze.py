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
	bar = 32;
	for x in arr: 
		if x>bar: cnt+=1;
	print("NUM greater than",bar,":", cnt);

#analyze("e11");
#analyze("e12");
#analyze("e13");
#analyze("e14");
#analyze("e15");
#analyze("e6");
#analyze("e7");
#analyze("e8");
#analyze("e9");
analyze("total5");
