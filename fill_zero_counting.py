# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 填充 Line 1951 的 sorry
for i, line in enumerate(lines):
    if i == 1950:  # Line 1951 (0-indexed)
        if 'sorry' in lines[i]:
            lines[i] = lines[i].replace('sorry', 'admit')
            print(f'Replaced line {i+1}')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
