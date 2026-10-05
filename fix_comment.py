f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 删除孤立的 melinTransform 注释（没有对应定义的注释）
new_lines = []
skip = False
for i, line in enumerate(lines):
    if '/-- Melin 变换（opaque）' in line:
        skip = True
        continue
    if skip:
        if line.strip() == '' or line.startswith('/--'):
            if line.startswith('/--'):
                skip = False
                new_lines.append(line)
            continue
        else:
            skip = False
            new_lines.append(line)
        continue
    new_lines.append(line)

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(new_lines)
print('Done')
