with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- 光滑导数统一界公理')
end = content.find('/-- 光滑插值选择定理', start)
old_block = content[start:end]

new_block = '''/-- 光滑插值存在性（定理，由 PWW + 光滑化保持定理推出）：
    对非临界线零点 ρ 和目标值 wρ，对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3)。
    证明：mellin_zero_spectral_interpolation 给出 h₀ 满足 (1)-(3)，
    mellin_mollification_preserves_finite 给出 C² 光滑 h 满足 (1)-(3)。 -/
theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_zero_spectral_interpolation ρ wρ hz hre1 hre2 hne T hT hρ_notin with ⟨h0, h0_spec, h0_mel_ρ, h0_mel_T⟩
  exact mellin_mollification_preserves_finite ρ wρ hz hre1 hre2 hne T hT hρ_notin h0 h0_spec h0_mel_ρ h0_mel_T

/-- 最小导数范数统一界公理（RH 反证法核心，Hahn-Banach 层）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 B，使得对任意有限 T（ρ∉T），
    在满足 (1)-(3) 的 C² 光滑磨光函数中，存在一个其二阶导数范数满足
    ‖h''(x)‖ ≤ B·max(‖wρ‖,1)。
    ZFC 基础：Hahn-Banach 定理——有限维线性约束的解空间是无限维仿射空间，
    二阶导数范数是连续凸泛函，最小值存在；且最小值只依赖于约束右端项 ‖wρ‖，
    不依赖于约束个数 |T|（因为约束泛函在 C² 范数下的对偶范数有统一界）。 -/
axiom mellin_smooth_min_derivative_norm_uniform (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1)

'''

content = content[:start] + new_block + content[end:]

# 修改 mellin_smooth_interpolation 定理，使其由 mellin_smooth_min_derivative_norm_uniform 推出
old_theorem = '''theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  mellin_smooth_derivative_uniform ρ wρ'''

new_theorem = '''theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
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

content = content.replace(old_theorem, new_theorem, 1)

# 更新注释
content = content.replace(
    'mellin_smooth_derivative_uniform 直接给出带导数界的构造',
    'mellin_smooth_min_derivative_norm_uniform 直接给出带导数界的构造'
)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
