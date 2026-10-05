with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 删除 mellin_interval_linear_independence 公理 + mellin_finite_surjectivity 定理
block1_start = '/-- 区间指示函数的 Mellin 变换非零族'
block1_end = '  simpa [L, v] using h2\n\n\n/-- 点集可分离性'

if block1_start in content and block1_end in content:
    idx1 = content.index(block1_start)
    idx2 = content.index(block1_end)
    # 保留 "/-- 点集可分离性" 开始的部分
    content = content[:idx1] + '/-- 点集可分离性' + content[idx2 + len('/-- 点集可分离性'):]
    print("删除 block1 成功")
else:
    print("未找到 block1")

# 删除 mellin_finite_set_surjectivity 定理
block2_start = '/-- Mellin 变换的有限集满射性（定理，由区间指示函数基'
block2_end = '  exact hh i\n\n/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零，带统一范数估计'

if block2_start in content and block2_end in content:
    idx1 = content.index(block2_start)
    idx2 = content.index(block2_end)
    content = content[:idx1] + '/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零，带统一范数估计' + content[idx2 + len('/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零，带统一范数估计'):]
    print("删除 block2 成功")
else:
    print("未找到 block2")

with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
