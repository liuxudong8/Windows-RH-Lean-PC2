# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 把所有的 (1 + |...im|) ^ 2 改成 |...im| ^ 2
# 但我们要小心，只改我们需要的地方

# 先看看有多少个 (1 + | 出现
count = content.count('(1 + |')
print(f'Found {count} occurrences of (1 + |')

# 替换所有的 (1 + | 为 |
content = content.replace('(1 + |', '|')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('Done')
