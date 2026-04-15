import re

with open("sonobe_mod/folding-schemes/src/folding/foldpot/sigma_ir1cs.rs", "r") as f:
    content = f.read()

# Insert macros after the first import or at the top
macros = """
macro_rules! lock_map {
    ($mutex:expr) => {
        $mutex.lock().map_err(|e| crate::Error::PoisonError(format!("Mutex poisoned at {}:{}: {}", file!(), line!(), e)))?
    };
}

macro_rules! lock_unwrap {
    ($mutex:expr) => {
        $mutex.lock().unwrap_or_else(|e| panic!("Mutex poisoned at {}:{}: {}", file!(), line!(), e))
    };
}
"""

if "macro_rules! lock_map" not in content:
    content = content.replace("use std::sync::{Arc, Mutex};", "use std::sync::{Arc, Mutex};\n" + macros)

# We have specific occurrences. Let's find them using regex.
# e.g., self.gadget_mapper.lock().unwrap() -> lock_unwrap!(self.gadget_mapper)
# We need to match the preceding expression. Since it's rust, it could be `g`, `g_mapper`, `self.gadget_mapper`, `self.get_mapper()`, etc.
# We'll use a regex that matches `([a-zA-Z0-9_.\(\)]+)\.lock\(\)\.unwrap\(\)` but handle whitespace if needed.

# Let's list the known targets and their preferred replacements based on context
# 1. g_mapper in gen_configs and new_adv (returns Result)
content = re.sub(r'g_mapper\s*\.lock\(\)\.unwrap\(\)', 'lock_map!(g_mapper)', content)

# 2. gadgets.iter().map(|g| g.lock().unwrap() -> lock_unwrap!(g)
content = re.sub(r'g\s*\.lock\(\)\.unwrap\(\)', 'lock_unwrap!(g)', content)

# 3. self.gadget_mapper.lock().unwrap()
# Depending on context, mostly lock_unwrap! except inside gen_cmF
# We'll just replace all self.gadget_mapper with lock_unwrap!(self.gadget_mapper) except one we know is in gen_cmF.
# Let's just use lock_unwrap! for all self.gadget_mapper because it's always safe and correct when the trait signature doesn't strictly require matching the Result error type or when not using ?.
content = re.sub(r'self\.gadget_mapper\s*\.lock\(\)\.unwrap\(\)', 'lock_unwrap!(self.gadget_mapper)', content)

# 4. self.get_mapper().lock().unwrap()
content = re.sub(r'self\.get_mapper\(\)\s*\.lock\(\)\.unwrap\(\)', 'lock_unwrap!(self.get_mapper())', content)

# 5. mapper.lock().unwrap() in test functions
content = re.sub(r'mapper\s*\.lock\(\)\.unwrap\(\)', 'lock_unwrap!(mapper)', content)

with open("sonobe_mod/folding-schemes/src/folding/foldpot/sigma_ir1cs.rs", "w") as f:
    f.write(content)
print("Replacement script generated and run.")
