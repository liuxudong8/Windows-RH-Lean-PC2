# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 4827 (index 4826)
print(f'Line 4827 before: {lines[4826].strip()}')
lines[4826] = lines[4826].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4827 after: {lines[4826].strip()}')

# 修复 Line 4833 (index 4832)
print(f'Line 4833 before: {lines[4832].strip()}')
lines[4832] = lines[4832].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4833 after: {lines[4832].strip()}')

# 修复 Line 4834 (index 4833)
print(f'Line 4834 before: {lines[4833].strip()}')
lines[4833] = lines[4833].replace(
    'C / (1 + |(nontrivialZeroEnum n).im|) ^ 2',
    'C / |(nontrivialZeroEnum n).im| ^ 2'
)
print(f'Line 4834 after: {lines[4833].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
