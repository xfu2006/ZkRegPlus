import os
import re

files_to_fix = [
    "sonobe_mod/folding-schemes/src/folding/foldpot/batch_proc.rs",
    "sonobe_mod/folding-schemes/src/folding/foldpot/mod_super.rs",
    "sonobe_mod/folding-schemes/src/folding/foldpot/qa_nizk.rs",
    "sonobe_mod/folding-schemes/src/folding/foldpot/decider_eth_circuit_super.rs",
    "sonobe_mod/folding-schemes/src/folding/foldpot/circuits_super.rs"
]

for file_path in files_to_fix:
    with open(file_path, 'r') as f:
        content = f.read()

    # Replace log_perf(log_level, with log_perf(job_id, log_level,
    content = re.sub(r'log_perf\(\s*log_level\s*,', 'log_perf(job_id, log_level,', content)
    # Replace log_perf(logl, with log_perf(job_id, logl,
    content = re.sub(r'log_perf\(\s*logl\s*,', 'log_perf(job_id, logl,', content)
    # Replace log(log_level, with log(job_id, log_level,
    content = re.sub(r'log\(\s*log_level\s*,', 'log(job_id, log_level,', content)
    # Replace log(logl, with log(job_id, logl,
    content = re.sub(r'log\(\s*logl\s*,', 'log(job_id, logl,', content)

    with open(file_path, 'w') as f:
        f.write(content)

print("Done replacing in files.")
