# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 2232 (index 2231)
print(f'Line 2232 before: {lines[2231].strip()}')
lines[2231] = lines[2231].replace('|(nontrivialZeroEnum n).im|) ^ 2) ≤', '|(nontrivialZeroEnum n).im|) ^ 2 ≤')
print(f'Line 2232 after: {lines[2231].strip()}')

# 修复 Line 2234 (index 2233)
print(f'Line 2234 before: {lines[2233].strip()}')
lines[2233] = lines[2233].replace('|(nontrivialZeroEnum n).im|) ^ 2', '|(nontrivialZeroEnum n).im| ^ 2')
print(f'Line 2234 after: {lines[2233].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
