f = open("dump4.txt");
setlines = [];
for line in f.readlines():
	if not line in setlines:
		setlines.append(line);
for x in setlines:
	if "false" in x:
		print(x);

