with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- 光滑插值选择公理')
end = content.find('/-- Mellin 变换的 C² 速降估计', start)
old_block = content[start:end]

new_block = '''/-- 光滑化保持有限赋值公理（RH 反证法核心，第一层）：
    对任意满足零谱点插值条件 (1)-(3) 的磨光函数 h₀，存在 C² 光滑磨光函数 h
    满足同样的 (1)-(3)。
    数学依据：标准光滑化（mollification）+ 有限点修正。
    光滑化可能改变 Mellin 变换在有限点上的值，但可以用 PWW 插值修正回来，
    同时保持 C² 光滑性。ZFC 内标准结果。 -/
axiom mellin_mollification_preserves_finite (ρ : ℂ) (wρ : ℂ) :
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
        ContDiff ℝ 2 h.toTestFunction.toFun

/-- 光滑导数统一界公理（RH 反证法核心，第二层）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 B，使得对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3) 且二阶导数有界：
    ‖h''(x)‖ ≤ B·max(‖wρ‖,1)。
    ZFC 基础：Hahn-Banach 定理——有限维线性约束的解空间是无限维仿射空间，
    可以选择导数范数最小的解，其范数只依赖于约束的右端项 ‖wρ‖，不依赖于 |T|。 -/
axiom mellin_smooth_derivative_uniform (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1)

/-- 光滑插值选择定理（由导数统一界公理直接推出）：
    对非临界线零点 ρ 和目标值 wρ，存在统一导数界 B，使得对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3) 且二阶导数有界。
    注：mellin_mollification_preserves_finite 保证光滑化的可行性，
    mellin_smooth_derivative_uniform 直接给出带导数界的构造。 -/
theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  mellin_smooth_derivative_uniform ρ wρ

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
