with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 修改 mellin_smooth_interpolation_no_bound
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
    ∃ (δ : ℝ), 0 < δ ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨δ, B, hδ_pos, hB_pos, hδ_le_ρ, h_choice⟩
  refine ⟨δ, hδ_pos, hδ_le_ρ, fun T hT hρ_notin hT_δ => ?_⟩
  rcases h_choice T hT hρ_notin hT_δ with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩'''

content = content.replace(old1, new1, 1)

# 2. 修改 mellin_smooth_interpolation
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
    ∃ (δ B : ℝ), 0 < δ ∧ 0 < B ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  mellin_smooth_min_derivative_norm_uniform ρ wρ'''

content = content.replace(old2, new2, 1)

# 3. 修改 mellin_mollification_preserves_finite
old3 = '''theorem mellin_mollification_preserves_finite (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∀ (h0 : MollifiedTestFunction),
      (∀ (n : ℕ), h0.toTestFunction.eval (specDiscM n) = 0) →
      melinTransform h0.toTestFunction ρ = wρ →
      (∀ (s : ℂ), s ∈ T → melinTransform h0.toTestFunction s = 0) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin h0 _ _ _
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩'''

new3 = '''theorem mellin_mollification_preserves_finite (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (δ : ℝ), 0 < δ ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∀ (h0 : MollifiedTestFunction),
        (∀ (n : ℕ), h0.toTestFunction.eval (specDiscM n) = 0) →
        melinTransform h0.toTestFunction ρ = wρ →
        (∀ (s : ℂ), s ∈ T → melinTransform h0.toTestFunction s = 0) →
        ∃ (h : MollifiedTestFunction),
          (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
          melinTransform h.toTestFunction ρ = wρ ∧
          (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
          ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨δ, B, hδ_pos, hB_pos, hδ_le_ρ, h_choice⟩
  refine ⟨δ, hδ_pos, hδ_le_ρ, fun T hT hρ_notin hT_δ h0 _ _ _ => ?_⟩
  rcases h_choice T hT hρ_notin hT_δ with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩'''

content = content.replace(old3, new3, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
