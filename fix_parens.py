# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 2232 (index 2231)
print(f'Line 2232 before: {lines[2231].strip()}')
lines[2231] = lines[2231].replace('|(nontrivialZeroEnum n).im|) ^ 2) ≤', '|(nontrivialZeroEnum n).im| ^ 2 ≤')
print(f'Line 2232 after: {lines[2231].strip()}')

# 修复 Line 2392 (index 2391)
print(f'Line 2392 before: {lines[2391].strip()}')
lines[2391] = lines[2391].replace('|(nontrivialZeroEnum n).im|) ^ 2) ≤', '|(nontrivialZeroEnum n).im| ^ 2 ≤')
print(f'Line 2392 after: {lines[2391].strip()}')

# 修复 Line 4741 (index 4740)
print(f'Line 4741 before: {lines[4740].strip()}')
lines[4740] = lines[4740].replace('|(nontrivialZeroEnum n).im|) ^ 2', '|(nontrivialZeroEnum n).im| ^ 2')
print(f'Line 4741 after: {lines[4740].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
