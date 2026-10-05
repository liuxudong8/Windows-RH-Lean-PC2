# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 把 axiom 改成 theorem
old_axiom = '''axiom mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M'''

new_theorem = '''theorem mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M := by
  sorry'''

content = content.replace(old_axiom, new_theorem)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
