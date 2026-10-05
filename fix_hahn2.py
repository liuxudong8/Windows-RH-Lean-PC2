with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 mellin_smooth_interpolation_no_bound 的证明
old_proof = '''theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_zero_spectral_interpolation ρ wρ hz hre1 hre2 hne T hT hρ_notin with ⟨h0, h0_spec, h0_mel_ρ, h0_mel_T⟩
  exact mellin_mollification_preserves_finite ρ wρ hz hre1 hre2 hne T hT hρ_notin h0 h0_spec h0_mel_ρ h0_mel_T'''

new_proof = '''theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_zero_spectral_interpolation ρ T hT hρ_notin wρ with ⟨h0, h0_spec, h0_mel_ρ, h0_mel_T⟩
  exact mellin_mollification_preserves_finite ρ wρ hz hre1 hre2 hne T hT hρ_notin h0 h0_spec h0_mel_ρ h0_mel_T'''

content = content.replace(old_proof, new_proof, 1)

# 修复 mellin_mollification_preserves_finite 中的旧名字
content = content.replace(
    'rcases mellin_smooth_derivative_uniform ρ wρ hz hre1 hre2 hne with',
    'rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with'
)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
