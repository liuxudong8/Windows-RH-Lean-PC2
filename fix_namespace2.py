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

# 找到我们加的代码的开始和结束
# 我们加的代码从 "/-- 微分算子 D = x d/dx" 开始
our_code_start = None
for i, line in enumerate(lines):
    if '/-- 微分算子 D = x d/dx' in line:
        our_code_start = i
        break

print(f"Our code starts at line {our_code_start + 1}")

# 我们加的代码到文件末尾
our_code_end = len(lines) - 1

print(f"Our code ends at line {our_code_end + 1}")

# 现在，我们需要把我们的代码移到 end_line_idx 之前
# 首先，把我们的代码从原来的位置去掉
our_code = lines[our_code_start:our_code_end + 1]
# 去掉空行
while our_code and our_code[0].strip() == '':
    our_code = our_code[1:]
while our_code and our_code[-1].strip() == '':
    our_code = our_code[:-1]

# 然后，把我们的代码插入到 end_line_idx 之前
new_lines = lines[:end_line_idx] + our_code + ['\n', '\n'] + lines[end_line_idx:]

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.writelines(new_lines)

print('Done!')
