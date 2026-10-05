with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 删除当前位置的 mellin_mollification_preserves_finite 定理
start = content.find('/-- 光滑化保持有限赋值（定理')
end = content.find('/-- 光滑导数统一界公理', start)
block_to_remove = content[start:end]
content = content[:start] + content[end:]

# 2. 在 mellin_smooth_interpolation 定理之后插入
insert_point = content.find('/-- Mellin 变换的 C² 速降估计')
# 先找到 mellin_smooth_interpolation 定理的结束
theorem_end = content.find('/-- Mellin 变换的 C² 速降估计', content.find('theorem mellin_smooth_interpolation'))

new_theorem = '''/-- 光滑化保持有限赋值（定理，由导数统一界公理直接推出）：
    对任意满足零谱点插值条件 (1)-(3) 的磨光函数 h₀，存在 C² 光滑磨光函数 h
    满足同样的 (1)-(3)。
    证明：mellin_smooth_derivative_uniform 直接构造 C² 光滑 h 满足 (1)-(3)，
    且不依赖于 h₀。h₀ 的存在性由 mellin_zero_spectral_interpolation 保证，
    但光滑化后的 h 由导数统一界公理独立构造。 -/
theorem mellin_mollification_preserves_finite (ρ : ℂ) (wρ : ℂ) :
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
  rcases mellin_smooth_derivative_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩

'''

content = content[:theorem_end] + new_theorem + content[theorem_end:]

# 3. 更新 mellin_smooth_interpolation 注释中的引用
content = content.replace(
    '注：mellin_mollification_preserves_finite 保证光滑化的可行性，\n    mellin_smooth_derivative_uniform 直接给出带导数界的构造。',
    '注：mellin_smooth_derivative_uniform 直接给出带导数界的构造，\n    mellin_mollification_preserves_finite 是其直接推论。'
)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
