# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h91 的 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4599 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 先证明 R₀^(s.re + 2) ≤ R₀^3 + 1
''',
            '''      have h_pow_le : R₀^(s.re + 2) ≤ R₀^3 + 1 := by
''',
            '''        by_cases hR₀_ge_one : R₀ ≥ 1
''',
            '''        · -- 情况 1：R₀ ≥ 1
''',
            '''          have h1 : s.re + 2 ≤ (3 : ℝ) := by linarith
''',
            '''          have h2 : R₀^(s.re + 2) ≤ R₀^(3 : ℝ) := by
''',
            '''            exact Real.rpow_le_rpow_of_exponent_le hR₀_ge_one h1
''',
            '''          have h3 : R₀^(3 : ℝ) = R₀^3 := by
''',
            '''            norm_cast
''',
            '''          rw [h3] at h2
''',
            '''          linarith
''',
            '''        · -- 情况 2：R₀ < 1
''',
            '''          have hR₀_pos : 0 < R₀ := by linarith [hε₀_pos, hε₀_lt_R₀]
''',
            '''          have hR₀_le_one : R₀ ≤ 1 := by linarith
''',
            '''          have h1 : 0 ≤ s.re + 2 := by linarith
''',
            '''          have h2 : R₀^(s.re + 2) ≤ R₀^(0 : ℝ) := by
''',
            '''            exact Real.rpow_le_rpow_of_exponent_ge hR₀_pos hR₀_le_one h1
''',
            '''          have h3 : R₀^(0 : ℝ) = 1 := by
''',
            '''            exact Real.rpow_zero R₀
''',
            '''          rw [h3] at h2
''',
            '''          linarith
''',
            '''      -- 组合起来
''',
            '''      exact h91_step3.trans (by
''',
            '''        calc R₀^(s.re + 2) / 2 ≤ (R₀^3 + 1) / 2 := by gcongr
''',
            '''           _ ≤ 8 * (R₀^3 + 1) := by linarith)
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
