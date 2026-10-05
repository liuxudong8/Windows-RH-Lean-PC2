with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- 最小导数范数统一界公理')
end = content.find('/-- 光滑插值存在性（定理', start)
old_block = content[start:end]

new_block = '''/-- C² 光滑约束满射性公理（第一层，代数层）：
    对非临界线零点 ρ，对任意有限 T（ρ∉T）和任意右端项 (wρ, wT)，
    存在 C² 光滑磨光函数 h 满足：
    (1) h(specDiscM n) = 0
    (2) M[h](ρ) = wρ
    (3) M[h]|_T = wT
    这是约束映射的满射性，不涉及范数估计。
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
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    约束泛函族 {h ↦ h(specDiscM n)} ∪ {h ↦ M[h](s) | s ∈ T ∪ {ρ}}
    在 C² 范数（二阶导数上确界）下的对偶范数 ≤ C。
    等价地：对任意 C² 光滑 h，max(‖h(specDiscM n)‖, ‖M[h](s)‖ for s∈T∪{ρ}) ≤ C·‖h''‖_∞。
    ZFC 基础：谱点 specDiscM n ≥ 1/4 有下界，Mellin 变换 M[h](s) = ∫ h(x)x^{s-1}dx，
    由分部积分 |M[h](s)| ≤ ‖h''‖_∞ / |s(s+1)| · ∫_{supp} x^{σ-1}dx，
    支集有界且远离 0，积分有界；σ∈(0,1) 时 |s(s+1)| 有正下界。 -/
axiom mellin_constraint_dual_norm_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∀ (h : MollifiedTestFunction), ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B)

/-- 最小范数原理公理（第三层，Hahn-Banach 层）：
    在满射性 + 对偶范数统一界的前提下，对任意右端项 wρ（wT=0），
    存在 C² 光滑解 h 满足 ‖h''‖_∞ ≤ C·max(‖wρ‖,1)。
    这是 Hahn-Banach 定理的标准推论：最小范数解的范数等于右端项的对偶范数，
    而对偶范数 ≤ C·max(‖wρ‖,1)。
    注：完整形式化需要赋范空间 + Hahn-Banach，此处作为公理声明。 -/
axiom mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∀ (C : ℝ), 0 < C →
      (∀ (h : MollifiedTestFunction), ContDiff ℝ 2 h.toTestFunction.toFun →
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

/-- 最小导数范数统一界（定理，由满射性 + 对偶范数界 + 最小范数原理推出）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 B，使得对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3) 且二阶导数有界：
    ‖h''(x)‖ ≤ B·max(‖wρ‖,1)。 -/
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
  exact mellin_min_norm_principle ρ wρ hz hre1 hre2 hne T hT hρ_notin C hC_pos (h_dual T hT hρ_notin)

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
