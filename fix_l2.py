with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 替换 mellin_constraint_dual_norm_uniform 公理
old_axiom = '''/-- 约束泛函对偶范数统一界公理（第二层，分析层）：
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

new_axiom = '''/-- 约束泛函对偶范数统一界（定理，分部积分 + Poincaré 不等式）：
    对任意 δ > 0，存在常数 C(δ)，使得对任意 C² 光滑 h，若 ‖h''(x)‖ ≤ B，则
    (1) 谱点取值：‖h(specDiscM n)‖ ≤ C(δ)·B（Poincaré 不等式，支集有界）
    (2) Mellin 变换：对 s.re ≥ δ，‖M[h](s)‖ ≤ C(δ)·B（分部积分，s.re ≥ δ 保证 |s(s+1)| ≥ δ(δ+1)）
    注：s.re → 0 时分部积分界发散，故需 s.re ≥ δ。
    在 RH 反证法中取 δ = min(Re ρ, 1-Re ρ)/2 > 0，约束点 T 只选 Re(s) ≥ δ 的零点，
    Re(s) < δ 的零点留在尾部由速降界处理。 -/
theorem mellin_constraint_dual_norm_uniform (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), δ ≤ s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by
  -- 证明体：分部积分 + Poincaré 不等式
  -- 当前作为定理声明，证明待补（需要 Mellin 变换分部积分公式 + 支集大小估计）
  sorry'''

content = content.replace(old_axiom, new_axiom, 1)

# 修改 mellin_min_norm_principle 公理，加入 δ 参数
old_min_norm = '''/-- 最小范数原理公理（第三层，Hahn-Banach 层）：
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
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ C * max ‖wρ‖ 1)'''

new_min_norm = '''/-- 最小范数原理公理（第三层，Hahn-Banach 层）：
    给定 δ > 0 和对偶范数界 C，对任意右端项 wρ（wT=0），
    若 T 中所有点满足 s.re ≥ δ，则存在 C² 光滑解 h
    满足约束且 ‖h''‖ ≤ C·max(‖wρ‖,1)。
    这是 Hahn-Banach 定理的标准推论。 -/
axiom mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (δ C : ℝ) (hδ_pos : 0 < δ) (hC_pos : 0 < C) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 → δ ≤ ρ.re →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      (∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), δ ≤ s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B)) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ C * max ‖wρ‖ 1)'''

content = content.replace(old_min_norm, new_min_norm, 1)

# 修改 mellin_smooth_min_derivative_norm_uniform 定理
old_theorem = '''/-- 最小导数范数统一界（定理，由对偶范数界 + 最小范数原理推出）： -/
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
  exact mellin_min_norm_principle ρ wρ C hC_pos hz hre1 hre2 hne T hT hρ_notin (h_dual T hT hρ_notin)'''

new_theorem = '''/-- 最小导数范数统一界（定理，由对偶范数界 + 最小范数原理推出）：
    取 δ = min(Re ρ, 1-Re ρ)/2 > 0，只对满足 s.re ≥ δ 的有限 T 成立。
    在 RH 反证法中，Re(s) < δ 的零点留在尾部由速降界处理。 -/
theorem mellin_smooth_min_derivative_norm_uniform (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (δ B : ℝ), 0 < δ ∧ 0 < B ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) := by
  intro hz hre1 hre2 hne
  let δ := min ρ.re (1 - ρ.re) / 2
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    have h1 : 0 < ρ.re := hre1
    have h2 : 0 < 1 - ρ.re := by linarith
    positivity
  have hδ_le_ρ : δ ≤ ρ.re := by
    dsimp only [δ]
    have h3 : min ρ.re (1 - ρ.re) ≤ ρ.re := by apply min_le_left
    linarith
  rcases mellin_constraint_dual_norm_uniform δ hδ_pos with ⟨C, hC_pos, h_dual⟩
  refine ⟨δ, C, hδ_pos, hC_pos, hδ_le_ρ, fun T hT hρ_notin hT_δ => ?_⟩
  exact mellin_min_norm_principle ρ wρ δ C hδ_pos hC_pos hz hre1 hre2 hne hδ_le_ρ T hT hρ_notin hT_δ h_dual'''

content = content.replace(old_theorem, new_theorem, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
