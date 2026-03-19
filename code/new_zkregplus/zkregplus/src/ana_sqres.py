import sys
import re

def analyze_subsig(file_path, target_subsig):
    with open(file_path, 'r') as f:
        lines = f.readlines()

    # Patterns to identify blocks and sections
    block_pattern = re.compile(r'^========== DEBUG USE (202|203|204|205|301|302|303|304)')
    seg_id_pattern = re.compile(r'seg_id:\s*(\d+)')
    subsig_header_pattern = re.compile(r'^\s*---- subsig: (\d+)')
    # Handles "loc 0: 123" and "i: 0, loc: 123"
    loc_pattern = re.compile(r'(?:loc \d+: (\d+)|i: \d+, loc: (\d+))')
    
    # We'll group by "segment cycle"
    # From grep output, a cycle is: 202, 203, 204, 205, [intermediate lines], 301, 302, 303, 304
    # The seg_id is in 301.
    
    # Let's collect all blocks for a "cycle".
    # A cycle ends at 304.
    
    cycles = []
    current_cycle_blocks = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        block_match = block_pattern.match(line)
        if block_match:
            block_type = block_match.group(1)
            block_header = line.strip()
            i += 1
            block_content = []
            while i < len(lines) and not block_pattern.match(lines[i]):
                block_content.append(lines[i])
                i += 1
            
            current_cycle_blocks.append((block_header, block_content))
            
            if block_type == "304":
                cycles.append(current_cycle_blocks)
                current_cycle_blocks = []
        else:
            i += 1
    
    # Handle the last cycle if it didn't end with 304
    if current_cycle_blocks:
        cycles.append(current_cycle_blocks)

    last_output_seg_id = None
    
    for cycle in cycles:
        # Find seg_id for this cycle (should be in 301)
        seg_id = "unknown"
        for header, _ in cycle:
            if "DEBUG USE 301" in header:
                seg_match = seg_id_pattern.search(header)
                if seg_match:
                    seg_id = seg_match.group(1)
                    break
        
        cycle_output = []
        for header, content in cycle:
            # Check if target_subsig is in this block
            subsig_indices = [idx for idx, l in enumerate(content) if subsig_header_pattern.match(l)]
            
            for start_idx in subsig_indices:
                subsig_match = subsig_header_pattern.match(content[start_idx])
                if subsig_match.group(1) == target_subsig:
                    # Collect output for this subsig section
                    cycle_output.append(header)
                    cycle_output.append(content[start_idx].strip())
                    
                    loc_numbers = []
                    k = start_idx + 1
                    # Stop at next subsig or end of content
                    while k < len(content) and not subsig_header_pattern.match(content[k]):
                        line_k = content[k].strip()
                        loc_match = loc_pattern.search(line_k)
                        if loc_match:
                            val = loc_match.group(1) if loc_match.group(1) is not None else loc_match.group(2)
                            loc_numbers.append(val)
                        else:
                            if loc_numbers:
                                for m in range(0, len(loc_numbers), 6):
                                    cycle_output.append("        " + ", ".join(loc_numbers[m:m+6]))
                                loc_numbers = []
                            cycle_output.append(content[k].rstrip())
                        k += 1
                    
                    if loc_numbers:
                        for m in range(0, len(loc_numbers), 6):
                            cycle_output.append("        " + ", ".join(loc_numbers[m:m+6]))

        if cycle_output:
            if seg_id != last_output_seg_id:
                print(f"\n\n***** segid: {seg_id} ****")
                last_output_seg_id = seg_id
            for line in cycle_output:
                print(line)

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python ana_sqres.py <file_path> <target_subsig>")
        sys.exit(1)
    
    file_path = sys.argv[1]
    target_subsig = sys.argv[2]
    analyze_subsig(file_path, target_subsig)
