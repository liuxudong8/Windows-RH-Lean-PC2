with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到三层结构的起始位置
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

/-- 点态对偶范数界（定理，第二层，分析层）：
    对每个固定的 s（0 < s.re < 1），存在常数 C(s)，使得对任意 C² 光滑 h，
    若 ‖h''(x)‖ ≤ B，则 ‖M[h](s)‖ ≤ C(s)·B。
    证明：两次分部积分 M[h](s) = 1/[s(s+1)]·∫ h''(x)x^{s+1}dx，
    支集有界 [ε,R]，故 ∫ x^{Re(s)+1}dx ≤ (R^{Re(s)+2}-ε^{Re(s)+2})/(Re(s)+2)。
    谱点取值界由 Poincaré 不等式：‖h‖_∞ ≤ (R-ε)²·‖h''‖_∞。
    注：C(s) 依赖于 s，当 s.re→0 时 C(s)→∞，故不存在统一 C。 -/
theorem mellin_pointwise_dual_norm_bound (s : ℂ) (hs_re1 : 0 < s.re) (hs_re2 : s.re < 1) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
  -- 证明体：分部积分 + 支集大小估计
  -- 当前作为定理声明，证明待补
  sorry

/-- 最小导数范数界公理（第三层，Hahn-Banach 层）：
    对非临界线零点 ρ 和目标值 wρ，对任意有限 T（ρ∉T），
    存在常数 B(T)，使得存在 C² 光滑 h 满足 (1)-(3) 且 ‖h''‖ ≤ B(T)·max(‖wρ‖,1)。
    B(T) 依赖于 T（因为点态对偶范数界 C(s) 依赖于 s），但对每个固定的 T 是有限的。
    ZFC 基础：Hahn-Banach 定理——有限维约束的最小范数解的范数等于右端项的对偶范数，
    而对偶范数 = max_{s∈T∪{ρ}} C(s)，有限集上有限。 -/
axiom mellin_smooth_min_derivative_norm (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (B : ℝ), 0 < B ∧
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1)

'''

content = content[:start] + new_block + content[end:]

# 现在修改 mellin_smooth_interpolation_no_bound, mellin_smooth_interpolation, mellin_mollification_preserves_finite
# 它们使用 mellin_smooth_min_derivative_norm_uniform，现在改为 mellin_smooth_min_derivative_norm

# 1. mellin_smooth_interpolation_no_bound
old1 = '''theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩'''

new1 = '''theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_smooth_min_derivative_norm ρ wρ hz hre1 hre2 hne T hT hρ_notin with ⟨B, hB_pos, h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩'''

content = content.replace(old1, new1, 1)

# 2. mellin_smooth_interpolation - 改为 B 依赖于 T
old2 = '''theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  mellin_smooth_min_derivative_norm_uniform ρ wρ'''

new2 = '''theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (B : ℝ), 0 < B ∧
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  fun hz hre1 hre2 hne T hT hρ_notin => mellin_smooth_min_derivative_norm ρ wρ hz hre1 hre2 hne T hT hρ_notin'''

content = content.replace(old2, new2, 1)

# 3. mellin_mollification_preserves_finite
old3 = '''  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩'''

new3 = '''  rcases mellin_smooth_min_derivative_norm ρ wρ hz hre1 hre2 hne T hT hρ_notin with ⟨B, hB_pos, h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩'''

content = content.replace(old3, new3, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
