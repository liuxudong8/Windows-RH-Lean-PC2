# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 2392 (index 2391)
print(f'Line 2392 before: {lines[2391].strip()}')

# 应该是：Summable (fun n => ... / |...im| ^ 2) := by
# 现在是：Summable (fun n => ... / |...im|)^2) := by
lines[2391] = lines[2391].replace(
    '/ |(nontrivialZeroEnum n).im|)^2) := by',
    '/ |(nontrivialZeroEnum n).im| ^ 2) := by'
)

print(f'Line 2392 after: {lines[2391].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
