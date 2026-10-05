with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 删除当前位置的 mellin_smooth_interpolation_no_bound
start = content.find('/-- 光滑插值存在性（定理')
end = content.find('/-- 最小导数范数统一界公理', start)
content = content[:start] + content[end:]

# 2. 在 mellin_smooth_interpolation 定理之前插入
insert_point = content.find('/-- 光滑插值选择定理')

new_theorem = '''/-- 光滑插值存在性（定理，由最小导数范数统一界公理推出）：
    对非临界线零点 ρ 和目标值 wρ，对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3)。
    证明：mellin_smooth_min_derivative_norm_uniform 直接构造 C² 光滑 h 满足 (1)-(3)。 -/
theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
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
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩

'''

content = content[:insert_point] + new_theorem + content[insert_point:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
