f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 删除行1260-1264的残留注释
new_lines = []
for i, line in enumerate(lines):
    lineno = i + 1
    if 1260 <= lineno <= 1264:
        continue
    new_lines.append(line)

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(new_lines)
print('Done')
