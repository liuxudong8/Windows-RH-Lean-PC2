# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 4535 and line.strip() == 'sorry':
        # 替换为 3 个步骤
        new_lines = [
            '''      -- 步骤 1：证明 f2 在 Icc ε₀ R₀ 上连续
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
            '''          exact hx_pos.ne'
''',
            '''      -- 步骤 2：证明 B' * f2 也连续
''',
            '''      have h_prod_cont : ContinuousOn (fun x : ℝ => B' * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
''',
            '''        exact ContinuousOn.const_mul B' h_f2_cont
''',
            '''      -- 步骤 3：用 ContinuousOn.integrableOn_compact 证明可积性
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
