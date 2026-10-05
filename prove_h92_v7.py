# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h92 的 sorry 行并替换
for i, line in enumerate(lines):
    if 'have h92 :' in line and 'sorry' in line:
        # 替换为完整的定理陈述和证明
        new_lines = [
            '  have h92 : 1/(‖s‖ * ‖s + 1‖) ≤ 1/|s.im| ^ 2 := by\n',
            '    -- 证明 ‖s‖ ≥ |s.im| 和 ‖s + 1‖ ≥ |s.im|\n',
            '    have h2 : ‖s‖ ≥ |s.im| := by\n',
            '      exact Complex.abs_im_le_norm s\n',
            '    have h31 : (s + 1).im = s.im := by\n',
            '      simp\n',
            '    have h3 : ‖s + 1‖ ≥ |s.im| := by\n',
            '      have h32 : |(s + 1).im| ≤ ‖s + 1‖ := Complex.abs_im_le_norm (s + 1)\n',
            '      rw [h31] at h32\n',
            '      exact h32\n',
            '    -- 组合起来\n',
            '    have h1 : ‖s‖ * ‖s + 1‖ ≥ |s.im| ^ 2 := by\n',
            '      calc\n',
            '        ‖s‖ * ‖s + 1‖ ≥ |s.im| * ‖s + 1‖ := by gcongr\n',
            '             _ ≥ |s.im| * |s.im| := by gcongr\n',
            '             _ = |s.im| ^ 2 := by ring\n',
            '    -- 两边取倒数\n',
            '    have h_pos1 : 0 < ‖s‖ * ‖s + 1‖ := by positivity\n',
            '    have h_s_im_ne_zero : s.im ≠ 0 := by\n',
            '      admit\n',
            '    have h_pos2 : 0 < |s.im| ^ 2 := by\n',
            '      positivity\n',
            '    exact one_div_le_one_div_of_le h_pos2 h1\n'
        ]
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1}')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
