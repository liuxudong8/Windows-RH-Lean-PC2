# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 把 |(nontrivialZeroEnum n).im|^2 改回 (1 + |(nontrivialZeroEnum n).im|)^2
content = content.replace(
    '|(nontrivialZeroEnum n).im|^2',
    '(1 + |(nontrivialZeroEnum n).im|)^2'
)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('Done')
