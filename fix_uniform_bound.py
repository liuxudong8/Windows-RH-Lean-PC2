with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 替换 mellin_constraint_dual_norm_uniform 定理的注释和证明
old = '''/-- 约束泛函对偶范数统一界（定理，第二层分析，强假设）：
    存在统一常数 C，使得对任意 C² 光滑 h，若 ‖h''(x)‖ ≤ B，则
    所有约束泛函的取值 ≤ C·B。
    注：此统一界不能简单由点态界推出（因 C(s) 在 s.re→0 时发散）。
    其严格证明需要额外的论证（如利用零点的零区域定理，或限制 s.re ≥ δ）。
    当前作为定理声明，证明待补。 -/
theorem mellin_constraint_dual_norm_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by
  -- 证明体：需要额外论证（零区域定理或 δ 限制），当前待补
  sorry'''

new = '''/-- 约束泛函对偶范数统一界（定理，第二层分析）：
    存在统一常数 C，使得对任意 C² 光滑 h，若 ‖h''(x)‖ ≤ B，则
    所有约束泛函的取值 ≤ C·B。
    证明思路（不用分部积分，避免 s.re→0 发散）：
    (1) 谱点取值：Poincaré 不等式 ‖h‖_∞ ≤ (R-ε)²·‖h''‖_∞，故 |h(specDiscM n)| ≤ C₁·B。
    (2) Mellin 变换：直接估计 |M[h](s)| ≤ ‖h‖_∞·∫_ε^R x^{σ-1}dx，
        而 ∫_ε^R x^{σ-1}dx = (R^σ-ε^σ)/σ ≤ max(log(R/ε), R-ε) 对 σ∈(0,1) 有界，
        再用 Poincaré 不等式得 |M[h](s)| ≤ C₂·B。
    注：分部积分给出的界在 s.re→0 时发散，但直接估计 + Poincaré 给出统一界。 -/
theorem mellin_constraint_dual_norm_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by
  -- 证明体：需要 Poincaré 不等式 + 积分估计 + Mellin 变换绝对值不等式
  -- 当前作为定理声明，证明待补（数学路径已清晰）
  sorry'''

content = content.replace(old, new, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
