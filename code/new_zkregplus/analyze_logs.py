import re

def get_templates(file_path):
    templates = set()
    started = False
    try:
        with open(file_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                
                # Check for start marker
                if not started:
                    if re.search(r'-+ Job \d+ starts -+', line, re.IGNORECASE):
                        started = True
                    continue
                
                original_line = line
                # 1. Normalize [job 0] to [job X]
                line = re.sub(r'\[job \d+\]', '[job X]', line)
                
                # 2. Identify the "data field" truncation point.
                # A "data field" integer is usually preceded by a space or colon 
                # and NOT followed by a colon (which would indicate a label like Step 10:).
                # We also want to avoid truncating at LOG1, LOG2, etc.
                
                # Regex explanation:
                # (?<!LOG)      -> Not preceded by "LOG" (to protect LOG1)
                # (?<!Step\s)   -> Not preceded by "Step " (to protect Step 10)
                # \b\d+\b       -> A whole number
                # (?!:)         -> Not followed by a colon
                
                match = re.search(r'(?<!LOG)(?<!Step\s)\b\d+\b(?!:)', line)
                
                if match:
                    template = line[:match.start()].strip()
                else:
                    template = line
                
                # Clean up trailing spaces/colons if we truncated too aggressively
                # but keep the structure if it's meaningful.
                
                # Ignore the start message itself
                if "starts" in template.lower() and "Job X" in template:
                    continue
                    
                templates.add(template)
    except FileNotFoundError:
        print(f"Warning: {file_path} not found.")
    
    if not started:
        print(f"Warning: Start marker not found in {file_path}")
        
    return templates

def analyze():
    log0_path = "/tmp/log_job_0.txt"
    log1_path = "/tmp/log_job_1.txt"

    set0 = get_templates(log0_path)
    set1 = get_templates(log1_path)

    all_distinct = sorted(list(set0.union(set1)))
    print(f"--- All Distinct Message Templates (Post-Start) ({len(all_distinct)}) ---")
    for t in all_distinct:
        print(f"  - {t}")
    
    print("\n" + "="*50)
    print("COMPARISON REPORT")
    print("="*50)

    only_in_0 = sorted(list(set0 - set1))
    if only_in_0:
        print(f"\n[!] Templates in Job 0 but MISSING in Job 1 ({len(only_in_0)}):")
        for t in only_in_0:
            print(f"  - {t}")
    else:
        print("\n[+] All Job 0 templates (after start) are present in Job 1.")

    only_in_1 = sorted(list(set1 - set0))
    if only_in_1:
        print(f"\n[!] Templates in Job 1 but MISSING in Job 0 ({len(only_in_1)}):")
        for t in only_in_1:
            print(f"  - {t}")
    else:
        print("\n[+] All Job 1 templates (after start) are present in Job 0.")

if __name__ == "__main__":
    analyze()
