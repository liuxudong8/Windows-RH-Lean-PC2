# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4533 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 步骤 1：证明 f1 = ‖deriv (deriv h.toFun) x‖ 在 Icc ε₀ R₀ 上连续
''',
            '''      have h_f1_cont : ContinuousOn (fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖) (Set.Icc ε₀ R₀) := by
''',
            '''        have h_deriv2_cont : ContinuousOn (deriv (deriv h.toFun)) (Set.Icc ε₀ R₀) := by
''',
            '''          exact (hC2.continuousOn_deriv hε₀_lt_R₀).continuousOn_deriv
''',
            '''        exact ContinuousOn.norm h_deriv2_cont
''',
            '''      -- 步骤 2：证明 f2 = x^(s.re + 1) 在 Icc ε₀ R₀ 上连续
''',
            '''      have h_f2_cont : ContinuousOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''        apply ContinuousOn.rpow
''',
            '''        · exact continuousOn_id
''',
            '''        · exact continuousOn_const
''',
            '''        · intro x hx
''',
            '''          have hx_pos : 0 < x := by linarith [hx.1, hε₀_pos]
''',
            '''          exact Or.inl hx_pos.ne'
''',
            '''      -- 步骤 3：证明乘积 f1 * f2 连续
''',
            '''      have h_prod_cont : ContinuousOn (fun x : ℝ => (‖(deriv (deriv h.toFun)) x‖) * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''        exact ContinuousOn.mul h_f1_cont h_f2_cont
''',
            '''      -- 步骤 4：用 ContinuousOn.integrableOn_compact 证明可积性
''',
            '''      exact h_prod_cont.integrableOn_compact isCompact_Icc
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
