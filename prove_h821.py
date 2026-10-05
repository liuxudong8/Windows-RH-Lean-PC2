# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4533 and line.strip() == 'sorry':
        # 替换为手动证明
        new_lines = [
            '''      have hf : MeasureTheory.IntegrableOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''        have h_cont : ContinuousOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''          apply Continuous.continuousOn
''',
            '''          fun_prop
''',
            '''        exact h_cont.integrableOn_compact isCompact_Icc
''',
            '''      have hg_meas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖) (volume.restrict (Set.Icc ε₀ R₀)) := by
''',
            '''        fun_prop
''',
            '''      have hg_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc ε₀ R₀)), ‖(fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖) x‖ ≤ B' := by
''',
            '''        filter_upwards with x
''',
            '''        simpa using hB x
''',
            '''      exact hf.mul_of_bound hg_meas B' hg_bound
'''
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
