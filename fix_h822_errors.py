# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到错误行并修复
for i, line in enumerate(lines):
    if "exact hx_pos.ne'" in line:
        lines[i] = "          exact Or.inl hx_pos.ne'\n"
        print(f'Fixed line {i+1}')
    if "exact ContinuousOn.const_mul B'" in line:
        lines[i] = "        exact h_f2_cont.const_mul B'\n"
        print(f'Fixed line {i+1}')

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
