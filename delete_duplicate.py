# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 end OrderPreservingBijection 的行号
end_line_idx = None
for i, line in enumerate(lines):
    if 'end OrderPreservingBijection' in line:
        end_line_idx = i
        break

print(f"end OrderPreservingBijection at line {end_line_idx + 1}")

# 删掉 end 后面的所有内容
new_lines = lines[:end_line_idx + 1]

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.writelines(new_lines)

print('Done!')
