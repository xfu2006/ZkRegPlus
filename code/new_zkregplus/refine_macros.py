import re

with open("sonobe_mod/folding-schemes/src/folding/foldpot/sigma_ir1cs.rs", "r") as f:
    content = f.read()

# gen_cmF function body search and replace
# We find fn gen_cmF and replace the FIRST lock_unwrap!(self.gadget_mapper) inside it
pattern = r'(fn gen_cmF.*?)\block_unwrap!\(self\.gadget_mapper\)'
replacement = r'\1lock_map!(self.gadget_mapper)'

content = re.sub(pattern, replacement, content, count=1, flags=re.DOTALL)

with open("sonobe_mod/folding-schemes/src/folding/foldpot/sigma_ir1cs.rs", "w") as f:
    f.write(content)

print("Refinement completed.")
