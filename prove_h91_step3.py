# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h91_step3 的 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4597 and line.strip() == 'sorry':
        lines[i] = '    exact h91_step3_a.trans h91_step3_b\n'
        print(f'Replaced line {i+1} with h91_step3 proof')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
