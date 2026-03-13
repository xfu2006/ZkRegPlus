import os
import re

def process_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    idx = 0
    new_content = ""
    changed = False
    
    pattern = re.compile(r'\bCol\s*(?:::\s*<[^>]+>\s*)?::\s*new\s*\(')
    
    last_end = 0
    for match in pattern.finditer(content):
        start = match.start()
        end = match.end()
        
        new_content += content[last_end:end]
        
        paren_count = 1
        curr = end
        while curr < len(content) and paren_count > 0:
            if content[curr] == '(':
                paren_count += 1
            elif content[curr] == ')':
                paren_count -= 1
            curr += 1
            
        inner_args = content[end:curr-1]
        new_content += inner_args + ", None)"
        last_end = curr
        changed = True

    new_content += content[last_end:]

    if changed:
        print(f"Updated {filepath}")
        with open(filepath, 'w') as f:
            f.write(new_content)

for root, dirs, files in os.walk('.'):
    for file in files:
        if file.endswith('.rs'):
            process_file(os.path.join(root, file))
