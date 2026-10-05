# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h92 的 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4643 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 证明 ‖s‖ * ‖s + 1‖ ≥ |s.im| ^ 2
''',
            '''      have h1 : ‖s‖ * ‖s + 1‖ ≥ |s.im| ^ 2 := by
''',
            '''        -- 展开复数范数
''',
            '''        have h2 : ‖s‖ = Real.sqrt ((s.re)^2 + (s.im)^2) := by
''',
            '''          simpa [Complex.norm_eq_abs, Complex.abs] using rfl
''',
            '''        have h3 : ‖s + 1‖ = Real.sqrt ((s.re + 1)^2 + (s.im)^2) := by
''',
            '''          simpa [Complex.norm_eq_abs, Complex.abs] using rfl
''',
            '''        rw [h2, h3]
''',
            '''        -- 两边平方
''',
            '''        have h4 : 0 ≤ |s.im| ^ 2 := by positivity
''',
            '''        have h5 : Real.sqrt ((s.re)^2 + (s.im)^2) * Real.sqrt ((s.re + 1)^2 + (s.im)^2) ≥ Real.sqrt (|s.im| ^ 2 * |s.im| ^ 2) := by
''',
            '''          apply Real.sqrt_le_sqrt
''',
            '''          -- 证明乘积 ≥ (s.im)^4
''',
            '''          have h6 : ((s.re)^2 + (s.im)^2) * ((s.re + 1)^2 + (s.im)^2) ≥ (s.im)^4 := by
''',
            '''            nlinarith
''',
            '''          exact h6
''',
            '''        have h7 : Real.sqrt (|s.im| ^ 2 * |s.im| ^ 2) = |s.im| ^ 2 := by
''',
            '''          have h8 : 0 ≤ |s.im| ^ 2 := by positivity
''',
            '''          rw [← Real.sqrt_mul h8]
''',
            '''          rw [Real.sqrt_sq_eq_abs]
''',
            '''          <;> ring
''',
            '''        rw [h7] at h5
''',
            '''        exact h5
''',
            '''      -- 两边取倒数
''',
            '''      have h_pos1 : 0 < ‖s‖ * ‖s + 1‖ := by positivity
''',
            '''      have h_pos2 : 0 < |s.im| ^ 2 := by positivity
''',
            '''      exact one_div_le_one_div_of_le h_pos1 h1
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
