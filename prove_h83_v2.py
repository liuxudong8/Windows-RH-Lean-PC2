# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4574 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 步骤 1：把集合积分转换成区间积分
''',
            '''      have h_set_to_interval : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = ∫ x in ε₀..R₀, B' * x^(s.re + 1) := by
''',
            '''        rw [intervalIntegral.integral_of_le hε₀_lt_R₀]
''',
            '''      rw [h_set_to_interval]
''',
            '''      -- 步骤 2：把常数 B' 提出来
''',
            '''      have h_const_mul : ∫ x in ε₀..R₀, B' * x^(s.re + 1) = B' * ∫ x in ε₀..R₀, x^(s.re + 1) := by
''',
            '''        rw [intervalIntegral.integral_const_mul]
''',
            '''      rw [h_const_mul]
''',
            '''      -- 步骤 3：用 integral_rpow 计算积分
''',
            '''      rw [integral_rpow (Or.inl (by linarith))]
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
