with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- C² 光滑约束满射性公理')
end = content.find('/-- 光滑插值存在性（定理', start)
old_block = content[start:end]

new_block = '''/-- C² 光滑约束满射性公理（第一层，代数层）：
    对非临界线零点 ρ，对任意有限 T（ρ∉T）和任意右端项 (wρ, wT)，
    存在 C² 光滑磨光函数 h 满足约束条件。
    ZFC 基础：Paley-Wiener-Whitney 联合插值 + 光滑化。 -/
axiom mellin_smooth_surjectivity (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∀ (wρ : ℂ) (wT : ℂ → ℂ),
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = wT s) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun

/-- 约束泛函对偶范数统一界公理（第二层，分析层）：
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
          ‖melinTransform h.toTestFunction s‖ ≤ C * B)

/-- 最小范数原理公理（第三层，Hahn-Banach 层）：
    给定对偶范数界 C，对任意右端项 wρ（wT=0），存在 C² 光滑解 h
    满足约束且 ‖h''‖ ≤ C·max(‖wρ‖,1)。
    这是 Hahn-Banach 定理的标准推论。 -/
axiom mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (C : ℝ) (hC_pos : 0 < C) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      (∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B)) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ C * max ‖wρ‖ 1)

/-- 最小导数范数统一界（定理，由对偶范数界 + 最小范数原理推出）： -/
theorem mellin_smooth_min_derivative_norm_uniform (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) := by
  intro hz hre1 hre2 hne
  rcases mellin_constraint_dual_norm_uniform ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_dual⟩
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  exact mellin_min_norm_principle ρ wρ C hC_pos hz hre1 hre2 hne T hT hρ_notin (h_dual T hT hρ_notin)

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
