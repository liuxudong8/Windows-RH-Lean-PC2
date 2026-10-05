# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 去掉 axiom 后面的 := by sorry
content = content.replace(
    '''‖melinTransform hT.toTestFunction ρ‖ ≥ c * M := by
  sorry''',
    '''‖melinTransform hT.toTestFunction ρ‖ ≥ c * M'''
)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
