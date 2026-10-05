# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 h_w 的证明
old = """    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      have h_first : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := by
        have h_pos : 0 < (nontrivialZeroEnum n).im^2 := by positivity
        rw [div_le_div_iff (by positivity) h_pos]
        exact h_m3
      calc w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := h_first
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
             apply div_le_div_of_nonneg_left
             <;> linarith [h_denom2] <;> positivity"""

new = """    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      have h_im_ne_zero : (nontrivialZeroEnum n).im ≠ 0 := by
        exact nontrivialZeroEnum_im_ne_zero n
      have h_pos : 0 < (nontrivialZeroEnum n).im^2 := by
        exact sq_pos_of_ne_zero h_im_ne_zero
      have h_first : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := by
        have h : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := h_m3
        have h_goal : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (nontrivialZeroEnum n).im^2 ≤ ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (nontrivialZeroEnum n).im^2 := by
          apply div_le_div_of_nonneg_right h
          <;> positivity
        exact h_goal
      have h_second : ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (nontrivialZeroEnum n).im^2 ≤ ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (2 : ℝ)^(2 * k) := by
        gcongr
        <;> linarith [h_denom2]
      calc w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := h_first
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := h_second"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
