import re;

def analyze(name):
	lines = open("dump2.txt").readlines();
	fmax = 0.0;
	r1 = re.compile(name + " (.+)");
	maxline = "";
	for line in lines:
	    matches = r1.findall(line);
	    if len(matches)>0:
	        if float(matches[0])>fmax: 
	                fmax = float(matches[0]);
	                maxline = line;
	print("max " + name, fmax);

arr_names = [
    "step queue: sq_inp, b_igc: true usage:",
    "step queue: sq_to_add, b_igc: true usage:",
    "step queue: sq_res, b_igc: true usage:",
    "StepFwdPrf: prf_fwd, b_igc: true usage:",
    "step queue: sq_to_del, b_igc: true usage:",
    "step queue: sq_res2, b_igc: true usage:",
    "StepBwdPrf: prf_bwd, b_igc: true usage:",
    "step queue: temp, b_igc: false usage:",
    "step queue: temp, b_igc: true usage:",
    "step queue: sq_inp, b_igc: false usage:",
    "step queue: sq_to_add, b_igc: false usage:",
    "step queue: sq_res, b_igc: false usage:",
    "StepFwdPrf: prf_fwd, b_igc: false usage:",
    "step queue: sq_to_del, b_igc: false usage:",
    "step queue: sq_res2, b_igc: false usage:",
    "StepBwdPrf: prf_bwd, b_igc: false usage:",
    "step queue: sq_inp, b_igc: true usage:",
    "step queue: sq_to_add, b_igc: true usage:",
    "step queue: sq_res, b_igc: true usage:",
    "StepFwdPrf: prf_fwd, b_igc: true usage:",
    "step queue: sq_to_del, b_igc: true usage:",
    "step queue: sq_res2, b_igc: true usage:",
];
for name in arr_names: 
        analyze(name);
