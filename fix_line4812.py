# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 4812 (index 4811)
print(f'Line 4812 before: {lines[4811].strip()}')
lines[4811] = lines[4811].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4812 after: {lines[4811].strip()}')

# 修复 Line 4817 (index 4816)
print(f'Line 4817 before: {lines[4816].strip()}')
lines[4816] = lines[4816].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4817 after: {lines[4816].strip()}')

# 修复 Line 4818 (index 4817)
print(f'Line 4818 before: {lines[4817].strip()}')
lines[4817] = lines[4817].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4818 after: {lines[4817].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
