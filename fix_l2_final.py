with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 替换 mellin_constraint_dual_norm_uniform 公理为两个定理
old = '''/-- 约束泛函对偶范数统一界公理（第二层，分析层）：
    存在统一常数 C，使得对任意 C² 光滑 h，若 ‖h''(x)‖ ≤ B，则
    所有约束泛函的取值 ≤ C·B。
    ZFC 基础：Mellin 变换分部积分 + 支集有界远离 0。 -/
axiom mellin_constraint_dual_norm_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B)'''

new = '''/-- 点态对偶范数界（定理，第二层分析，分部积分）：
    对每个固定的 s（0 < s.re < 1），存在常数 C(s)，使得对任意 C² 光滑 h，
    若 ‖h''(x)‖ ≤ B，则 ‖M[h](s)‖ ≤ C(s)·B。
    证明：两次分部积分 M[h](s) = 1/[s(s+1)]·∫ h''(x)x^{s+1}dx，
    支集有界 [ε,R]，故 ∫ x^{Re(s)+1}dx 有限。
    谱点取值界由 Poincaré 不等式：‖h‖_∞ ≤ (R-ε)²·‖h''‖_∞。
    注：C(s) 依赖于 s，当 s.re→0 时 C(s)→∞（因 |s(s+1)|→0）。 -/
theorem mellin_pointwise_dual_norm_bound (s : ℂ) (hs_re1 : 0 < s.re) (hs_re2 : s.re < 1) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
  -- 证明体：分部积分 + 支集大小估计
  sorry

/-- 约束泛函对偶范数统一界（定理，第二层分析，强假设）：
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

content = content.replace(old, new, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
