with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复第 1 处
old1 = '''  have h_m1ρ : melinTransform f1.toTestFunction ρ = 1 := by
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction ρ = melinTransform f2.toTestFunction ρ + melinTransform h ρ := by
      rw [h_eq]
    rw [h1, h_m2ρ, h_mρ] <;> ring'''

new1 = '''  have h_m1ρ : melinTransform f1.toTestFunction ρ = 1 := by
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction ρ = melinTransform f2.toTestFunction ρ + melinTransform h ρ := by
      exact congrFun h_eq ρ
    rw [h1, h_m2ρ, h_mρ] <;> ring'''

content = content.replace(old1, new1)

# 修复第 2 处
old2 = '''  have h_T_eq : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by rw [h_eq]
    have h2 : melinTransform h s = 0 := h_mT s hs
    rw [h1, h2] <;> ring'''

new2 = '''  have h_T_eq : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by
      exact congrFun h_eq s
    have h2 : melinTransform h s = 0 := h_mT s hs
    rw [h1, h2] <;> ring'''

content = content.replace(old2, new2)

# 修复第 3 处
old3 = '''  have h_decay' : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s = melinTransform h s := by
      rw [h_eq] <;> ring
    rw [h1]
    exact h_bound s hre1' hre2' '''

new3 = '''  have h_decay' : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h2 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by
      exact congrFun h_eq s
    have h1 : melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s = melinTransform h s := by
      rw [h2] <;> ring
    rw [h1]
    exact h_bound s hre1' hre2' '''

content = content.replace(old3, new3)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("修复完成")
