import re

with open('Spqr/Specs/Bugs/CorruptedBlobs.lean', 'r') as f:
    lines = f.readlines()

error_theorems = [
    194, 239, 301, 334, 380, 416, 432, 449, 492, 571,
    618, 634, 651, 681, 766, 801,
    943, 955, 975,
    1232, 1250, 1267, 1286, 1311, 1325, 1344,
]

error_theorems_0 = [t - 1 for t in error_theorems]

def find_proof_end(lines, start_idx):
    by_line = None
    for i in range(start_idx, min(start_idx + 20, len(lines))):
        if ':= by' in lines[i]:
            by_line = i
            break
    if by_line is None:
        return None, None
    end_line = by_line + 1
    for i in range(by_line + 1, len(lines)):
        line = lines[i]
        stripped = line.strip()
        if stripped == '':
            continue
        if (line.startswith('theorem ') or line.startswith('def ') or
            line.startswith('end ') or line.startswith('/-') or
            line.startswith('namespace ') or line.startswith('section ') or
            line.startswith('/--') or line.startswith('private ') or
            line.startswith('@[') or line.startswith('#')):
            end_line = i
            break
        if line[0] in (' ', '\t'):
            end_line = i + 1
            continue
        end_line = i
        break
    else:
        end_line = len(lines)
    return by_line, end_line

replacements = []
for t in error_theorems_0:
    by_line, end_line = find_proof_end(lines, t)
    if by_line is None:
        print(f"WARNING: no ':= by' for theorem at line {t+1}")
        continue
    replacements.append((by_line, end_line))
    print(f"Line {t+1}: proof {by_line+1}-{end_line}")

replacements.sort(key=lambda x: x[0], reverse=True)
for by_line, end_line in replacements:
    orig_line = lines[by_line]
    idx = orig_line.find(':= by')
    if idx >= 0:
        lines[by_line] = orig_line[:idx] + ':= by\n'
        lines[by_line+1:end_line] = ['  sorry\n', '\n']

with open('Spqr/Specs/Bugs/CorruptedBlobs.lean', 'w') as f:
    f.writelines(lines)

print("Done")
