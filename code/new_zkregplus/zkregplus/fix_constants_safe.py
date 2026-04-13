import os

files = [
    "zkregplus/src/gadgets/commons.rs",
    "zkregplus/src/gadgets/fsm_adv.rs",
    "zkregplus/src/gadgets/compute_sig_adv.rs",
    "zkregplus/src/gadgets/dfa_adv.rs",
    "zkregplus/src/gadgets/discharge_adv.rs",
    "zkregplus/src/gadgets/sigs.rs",
    "zkregplus/src/gadgets/db.rs",
    "zkregplus/src/gadgets/fsm.rs"
]

for file_path in files:
    if not os.path.exists(file_path):
        continue
    with open(file_path, "r") as f:
        content = f.read()

    # Add import if missing and RANGE2_BIT used
    if "RANGE2_BIT" in content:
        if "use utils::consts::read_global_config;" not in content:
            content = "use utils::consts::read_global_config;\n" + content
    
    # Remove RANGE2_BIT from imports
    content = content.replace("RANGE2_BIT,", "")
    content = content.replace(",RANGE2_BIT", "")
    
    # Replace the remaining uses
    content = content.replace("RANGE2_BIT", "read_global_config().range2_bit")

    # Fix bits > 19 mismatch
    content = content.replace("bits>19", "bits>F::from(19u32)")

    # Write back
    with open(file_path, "w") as f:
        f.write(content)
        
print("Replaced constants securely.")
