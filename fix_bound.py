with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = '''  have h_bound' : ∀ (s : ℂ), 0 < s.re → s.re < 1 → ‖melinTransform h s‖ ≤ C0 / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h := h_bound s hre1' hre2'
    have h_max : max (1 : ℝ) 1 = 1 := by simp
    rw [h_max] at h
    exact h'''

new = '''  have h_bound' : ∀ (s : ℂ), 0 < s.re → s.re < 1 → ‖melinTransform h s‖ ≤ C0 / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h := h_bound s hre1' hre2'
    simpa [max_eq_left (show (1 : ℝ) ≤ 1 by norm_num)] using h'''

if old in content:
    content = content.replace(old, new)
    print("修复成功")
else:
    print("未找到")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
