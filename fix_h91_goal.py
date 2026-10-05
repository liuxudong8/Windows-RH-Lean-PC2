# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 4482 (index 4481) - 删除多余的 exact h_goal
print(f'Line 4482 before: {lines[4481].strip()}')
del lines[4481]
print(f'Deleted line 4482')

# 修复 Line 4485 (现在是 Line 4484) - 把 h91' 改成 h_goal
print(f'Line 4484 before: {lines[4483].strip()}')
lines[4483] = lines[4483].replace('h91\'', 'h_goal')
print(f'Line 4484 after: {lines[4483].strip()}')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
