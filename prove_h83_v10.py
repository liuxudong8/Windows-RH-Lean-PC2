# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4574 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 步骤1：集合积分转区间积分
''',
            '''      have h1 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = ∫ x in ε₀..R₀, B' * x^(s.re + 1) := by
''',
            '''        rw [integral_over_Icc]
''',
            '''        <;> linarith
''',
            '''      -- 步骤2：提取积分外的常数 B'
''',
            '''      have h2 : ∫ x in ε₀..R₀, B' * x^(s.re + 1) = B' * ∫ x in ε₀..R₀, x^(s.re + 1) := by
''',
            '''        rw [intervalIntegral.const_mul]
''',
            '''      -- 步骤3：应用 Mathlib 标准幂函数积分公式
''',
            '''      have h3 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
''',
            '''        rw [intervalIntegral.integral_rpow hε₀_pos hε₀_lt_R₀]
''',
            '''        <;> field_simp
''',
            '''        <;> ring_nf
''',
            '''      -- 步骤4：串联所有等式完成证明
''',
            '''      rw [h1, h2, h3]
''',
            '''      <;> ring
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
