import re;
lines = open("dump.txt").readlines();
r1 = re.compile("---- subsig: ([0-9]+)");
last_subsig = "";
last_line = 1;
dict_subsig = {};
id = 0;
for line in lines:
    id += 1;
    if line.find("---- subsig:")>=0:
        if last_subsig!="":
            if last_subsig in dict_subsig.keys() and dict_subsig[last_subsig]<id-last_line:
                dict_subsig[last_subsig] = id - last_line;

            else:
                dict_subsig[last_subsig] = id - last_line;
        last_subsig = r1.findall(line)[0];
        last_line = id;

print("SUBSIG 36598786: ", dict_subsig["36598786"]);
from operator import itemgetter;

sorted_dict = dict(
    sorted(dict_subsig.items(), key=itemgetter(1), reverse=True)
)

print(sorted_dict)


