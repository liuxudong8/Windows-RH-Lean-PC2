f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 提取 heatOperator 块（行162-186，索引161-185）
# 从注释开始到 heatKernel_commutes_laplacian 结束
block_start = None
block_end = None
for i, line in enumerate(lines):
    if '/-- 热核算子（定义）' in line:
        block_start = i
    if block_start is not None and 'heatOperator t (laplacian_M f) = laplacian_M (heatOperator t f)' in line:
        block_end = i + 1
        break

print(f'heatOperator block: lines {block_start+1} to {block_end}')
heat_block = lines[block_start:block_end]

# 删除原位置
del lines[block_start:block_end]

# 找到 laplacian_M 之后的位置
lap_m_idx = None
for i, line in enumerate(lines):
    if 'opaque laplacian_M : L2Function ManifoldM' in line:
        lap_m_idx = i
        break

# 找到 laplacian_M 之后的空行或下一个声明
insert_idx = lap_m_idx + 1
while insert_idx < len(lines) and lines[insert_idx].strip() == '':
    insert_idx += 1

print(f'Insert after laplacian_M at line {insert_idx+1}')
lines[insert_idx:insert_idx] = heat_block

# 标记 geometricKernelTrace 为 noncomputable
for i, line in enumerate(lines):
    if 'def geometricKernelTrace (f : TestFunction) : ℂ :=' in line:
        lines[i] = 'noncomputable def geometricKernelTrace (f : TestFunction) : ℂ :=\n'
        print(f'Marked geometricKernelTrace as noncomputable at line {i+1}')
        break

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(lines)
print('Done')
