# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4533 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      -- 步骤 1：证明二阶导数是连续的
''',
            '''      have h_deriv_h_C1 : ContDiff ℝ 1 (deriv h.toFun) := by
''',
            '''        exact hC2.deriv'
''',
            '''      have h_deriv2_C0 : ContDiff ℝ 0 (deriv (deriv h.toFun)) := by
''',
            '''        exact h_deriv_h_C1.deriv'
''',
            '''      have h_deriv2_cont : Continuous (deriv (deriv h.toFun)) := by
''',
            '''        exact h_deriv2_C0.continuous
''',
            '''      have h_norm_deriv2_cont : Continuous (fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖) := by
''',
            '''        exact Continuous.norm h_deriv2_cont
''',
            '''      -- 步骤 2：证明 x^(s.re + 1) 是连续的
''',
            '''      have h_pow_cont : ContinuousOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
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
            '''      -- 步骤 3：证明乘积是 ContinuousOn
''',
            '''      have h_prod_cont_on : ContinuousOn (fun x : ℝ => (‖(deriv (deriv h.toFun)) x‖) * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''        apply ContinuousOn.mul
''',
            '''        · exact h_norm_deriv2_cont.continuousOn
''',
            '''        · exact h_pow_cont
''',
            '''      -- 步骤 4：紧集上的 ContinuousOn 函数是 IntegrableOn
''',
            '''      exact h_prod_cont_on.integrableOn_compact isCompact_Icc
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
