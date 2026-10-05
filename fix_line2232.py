# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 2232 (index 2231)
# 原来的问题是少了一个右括号
print(f'Line 2232 before: {lines[2231].strip()}')

# 应该是：((zeroMultiplicity ...) / |...im|) ^ 2 ≤
lines[2231] = lines[2231].replace(
    '((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤',
    '((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im|) ^ 2 ≤'
)

print(f'Line 2232 after: {lines[2231].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
