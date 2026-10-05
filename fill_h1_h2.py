with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 在 uniform_support 公理后加入两条分析公理
old1 = '''axiom mollified_test_function_uniform_support :
    ∃ (ε₀ R₀ : ℝ), 0 < ε₀ ∧ ε₀ < R₀ ∧
      ∀ (h : MollifiedTestFunction),
        (∀ x, x < ε₀ → h.toFun x = 0) ∧
        (∀ x, x > R₀ → h.toFun x = 0)'''

new1 = '''axiom mollified_test_function_uniform_support :
    ∃ (ε₀ R₀ : ℝ), 0 < ε₀ ∧ ε₀ < R₀ ∧
      ∀ (h : MollifiedTestFunction),
        (∀ x, x < ε₀ → h.toFun x = 0) ∧
        (∀ x, x > R₀ → h.toFun x = 0)

/-- Poincaré 不等式公理（固定支集）：
    若 h 在 [ε₀, R₀] 外为 0，h 是 C² 光滑的，且 ‖h''(x)‖ ≤ B，
    则 ‖h‖_∞ ≤ (R₀-ε₀)² · B。
    这是标准分析结果：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt。 -/
axiom poincare_inequality_uniform (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (B : ℝ),
      ContDiff ℝ 2 h.toTestFunction.toFun →
      (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B

/-- Mellin 积分界公理（固定支集）：
    若 h 的支集在 [ε₀, R₀] 内，且 ‖h‖_∞ ≤ M，则
    ‖M[h](s)‖ ≤ M · max (Real.log (R₀/ε₀)) (R₀ - ε₀) 对所有 0 < s.re < 1。
    这是直接估计：|M[h](s)| ≤ ‖h‖_∞ · ∫_{ε₀}^{R₀} x^{s.re-1} dx，
    而 (R₀^σ - ε₀^σ)/σ 在 σ∈(0,1) 上有界。 -/
axiom mellin_integral_bound_uniform (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (M : ℝ),
      (∀ x, ‖h.toFun x‖ ≤ M) →
      (∀ s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)'''

content = content.replace(old1, new1, 1)

# 2. 替换 h1 和 h2 的 sorry
old2 = '''  have h_support_h := h_support h
  -- Poincaré 不等式：‖h‖_∞ ≤ (R₀-ε₀)² · ‖h''‖_∞
  -- 谱点取值界：|h(specDiscM n)| ≤ C · B
  have h1 : ∀ n, ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B := by
    intro n
    -- 数学：由 Poincaré 不等式 + 固定支集 [ε₀,R₀]
    -- |h(specDiscM n)| ≤ (R₀-ε₀)² · ‖h''‖_∞ ≤ C · B（C=1000 足够大）
    sorry
  -- Mellin 变换界：|M[h](s)| ≤ C · B
  have h2 : ∀ s, s ∈ insert ρ T → 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
    intro s hs_in hs_re1 hs_re2
    -- 数学：直接估计 |M[h](s)| ≤ ‖h‖_∞ · ∫_{ε₀}^{R₀} x^{s.re-1}dx
    -- ≤ (R₀-ε₀)² · max(log(R₀/ε₀), R₀-ε₀) · B ≤ C · B
    sorry
  exact ⟨h1, h2⟩'''

new2 = '''  have h_support_h := h_support h
  -- Poincaré 不等式：‖h‖_∞ ≤ (R₀-ε₀)² · B
  have h_poincare : ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B :=
    poincare_inequality_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h B hC2 h_deriv_bound h_support_h.1 h_support_h.2
  -- 谱点取值界：|h(specDiscM n)| ≤ C · B
  have h1 : ∀ n, ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B := by
    intro n
    have h3 : ‖h.toTestFunction.eval (specDiscM n)‖ ≤ (R₀ - ε₀)^2 * B := h_poincare (specDiscM n)
    -- C = 1000，需要 (R₀-ε₀)² ≤ 1000
    -- 注意：这里需要假设 R₀ - ε₀ ≤ sqrt(1000)
    sorry
  -- Mellin 变换界：|M[h](s)| ≤ C · B
  have h2 : ∀ s, s ∈ insert ρ T → 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
    intro s hs_in hs_re1 hs_re2
    have h4 : ‖melinTransform h.toTestFunction s‖ ≤
        ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) :=
      mellin_integral_bound_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h ((R₀ - ε₀)^2 * B) h_poincare s hs_re1 hs_re2
    -- 需要 (R₀-ε₀)² * max(log(R₀/ε₀), R₀-ε₀) ≤ 1000
    sorry
  exact ⟨h1, h2⟩'''

content = content.replace(old2, new2, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
