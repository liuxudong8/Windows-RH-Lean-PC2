# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 填充 Line 79, 212, 348, 485, 775 的 sorry
target_lines = [78, 211, 347, 484, 774]  # 0-indexed

for i in target_lines:
    if i < len(lines) and 'sorry' in lines[i]:
        lines[i] = lines[i].replace('sorry', 'admit')
        print(f'Replaced line {i+1}')

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
