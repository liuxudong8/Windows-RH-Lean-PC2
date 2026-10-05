# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Line 4478 (index 4477) 是 have h_goal : ...
# 我们要把它改成 have h91' : ...

# 打印一下看看
print(f'Line 4478: {lines[4477].strip()}')

# 修改这一行
lines[4477] = lines[4477].replace('have h_goal :', "have h91' :")

print(f'Modified: {lines[4477].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
