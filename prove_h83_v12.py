# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4574 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 步骤 0：把 ε₀ < R₀ 转换成 ε₀ ≤ R₀
''',
            '''      have hε₀_le_R₀ : ε₀ ≤ R₀ := by linarith
''',
            '''      -- 步骤 1：集合积分转区间积分
''',
            '''      have h1 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = ∫ x in ε₀..R₀, B' * x^(s.re + 1) := by
''',
            '''        have h11 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = ∫ x in Set.Ioc ε₀ R₀, B' * x^(s.re + 1) := by
''',
            '''          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
''',
            '''        have h12 : ∫ x in ε₀..R₀, B' * x^(s.re + 1) = ∫ x in Set.Ioc ε₀ R₀, B' * x^(s.re + 1) := by
''',
            '''          rw [intervalIntegral.integral_of_le hε₀_le_R₀]
''',
            '''        rw [h11, ← h12]
''',
            '''      rw [h1]
''',
            '''      -- 步骤 2：常数提取
''',
            '''      have h2 : ∫ x in ε₀..R₀, B' * x^(s.re + 1) = B' * ∫ x in ε₀..R₀, x^(s.re + 1) := by
''',
            '''        rw [intervalIntegral.integral_const_mul]
''',
            '''      rw [h2]
''',
            '''      -- 步骤 3：幂函数积分公式（明确给出 Or.inl 参数）
''',
            '''      have h3 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
''',
            '''        rw [integral_rpow (Or.inl (by linarith))]
''',
            '''      rw [h3]
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
