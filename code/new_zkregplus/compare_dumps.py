import sys

def extract_debug_lines(filename):
    lines = []
    try:
        with open(filename, 'r') as f:
            for line in f:
                if 'DEBUG USE 65431.6' in line:
                    lines.append(line.strip())
    except FileNotFoundError:
        print(f"Error: {filename} not found")
        return None
    return lines

def compare_debug_logs(file1, file2):
    print(f"Loading {file1}...")
    lines1 = extract_debug_lines(file1)
    print(f"Loading {file2}...")
    lines2 = extract_debug_lines(file2)

    if lines1 is None or lines2 is None:
        return

    print(f"File 1 debug lines: {len(lines1)}")
    print(f"File 2 debug lines: {len(lines2)}")

    # We only compare up to the shorter length to account for the crash in Run 2
    min_len = min(len(lines1), len(lines2))
    
    match = True
    for i in range(min_len):
        if lines1[i] != lines2[i]:
            print(f"\nDIFFERENCE FOUND at line index {i}:")
            print(f"Run 1: {lines1[i]}")
            print(f"Run 2: {lines2[i]}")
            match = False
            break
    
    if match:
        print(f"\nSUCCESS: The first {min_len} debug lines are perfectly identical.")
        if len(lines1) != len(lines2):
            print(f"Note: Run 1 has {len(lines1)} lines total, Run 2 has {len(lines2)} lines total (it stopped early).")

if __name__ == "__main__":
    compare_debug_logs('zkregplus/src/dump.txt', 'zkregplus/src/dump2.txt')
