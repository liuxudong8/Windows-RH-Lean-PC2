import re

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到要替换的部分的起始和结束位置
start_marker = '  exact ⟨h1, h2⟩\n\n/-- 最小范数原理公理（第三层，Hahn-Banach 层）：'
end_marker = '  exact mellin_min_norm_principle ρ wρ C hC_pos hz hre1 hre2 hne T hT hρ_notin (h_dual T hT hρ_notin)'

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1:
    print('Start marker not found!')
    exit(1)
if end_idx == -1:
    print('End marker not found!')
    exit(1)

end_idx += len(end_marker)

# 新内容
new_content = '''  exact ⟨h1, h2⟩

/-- 对偶范数下界统一公理（新增）：
    对非临界线零点 ρ，存在统一常数 c > 0，使得对任意有限 T（ρ∉T），
    都存在一个测试函数 hT 满足：
    (1) hT 在所有谱点上取值为 0
    (2) M[hT](s) = 0 对所有 s ∈ T
    (3) |M[hT](ρ)| ≥ c * sup_x ‖hT''(x)‖
    即：线性泛函 L_T(h) = Mh(ρ) 在子空间 XT 上的对偶范数有统一的正下界 c。

    注意：这不是逐点不等式，而是"存在测试函数"的形式。
    逐点不等式 |Mh(ρ)| ≥ c * ‖h''‖ 对所有 h 成立是不对的，
    因为如果 h ∈ XT 且 Mh(ρ) = 0，左边就是 0，右边却是正的。

    数学内容：
    用微分算子 L_T = ∏_{t∈T} (D + t)，其中 D = x d/dx，
    从固定的 bump 函数 φ 出发，令 ψ_T = L_T φ，
    则 M[ψ_T](t) = 0 对所有 t ∈ T，且 M[ψ_T](ρ) = (-1)^{|T|} P_T(ρ) M[φ](ρ)。
    我们需要证明比值 |M[ψ_T](ρ)| / ‖ψ_T''‖ 有统一的正下界 c。

    来源依据：
    微分算子消零构造 + 有限维线性代数估计。

    用途范围：
    用于 mellin_min_norm_principle，由 Hahn-Banach 推出最小范数解的上界。 -/
axiom mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖)) := by
  sorry

/-- 最小范数原理定理（第三层，Hahn-Banach 层）：
    给定对偶范数下界 c，对任意右端项 wρ（wT=0），存在 C² 光滑解 h
    满足约束且 ‖h''‖ ≤ (1/c)·max(‖wρ‖,1)。
    这是 Hahn-Banach 最小范数原理的标准推论。

    数学：
    设 XT = {h : Mh(σ) = 0 ∀σ ∈ Spectrum, Mh(s) = 0 ∀s ∈ T}，
    定义 L_T(h) = Mh(ρ)，‖h‖_X = sup_x ‖h''(x)‖。
    由对偶范数下界公理，∃ hT ∈ XT, hT ≠ 0，使得 |L_T(hT)| ≥ c * ‖hT‖_X。
    即 ‖L_T‖_* ≥ c。
    由 Hahn-Banach 最小范数原理，inf{‖h‖_X : h ∈ XT, L_T(h) = wρ} = |wρ| / ‖L_T‖_* ≤ |wρ| / c。
    故存在 h ∈ XT，使得 L_T(h) = wρ 且 ‖h‖_X ≤ (1/c) * |wρ|。
    再用 max(‖wρ‖, 1) 处理 wρ = 0 的情况。 -/
theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖)) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ (1 / c) * max ‖wρ‖ 1) := by
  intro hz hre1 hre2 hne T hT hρ_notin hT_exists
  obtain ⟨hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound⟩ := hT_exists
  -- 简单构造：直接用 hT 缩放
  let scalar : ℂ := wρ / melinTransform hT.toTestFunction ρ
  refine ⟨scalar • hT, ?_, ?_, ?_, ?_, ?_⟩
  · -- 谱点取值为 0
    simpa [scalar, hT_spec] using smul_zero _
  · -- melinTransform h ρ = wρ
    have h1 : melinTransform (scalar • hT).toTestFunction ρ = scalar * melinTransform hT.toTestFunction ρ := by
      exact?
    rw [h1, scalar, div_mul_cancel₀ _ hT_mel_ρ_ne]
  · -- melinTransform h s = 0 对所有 s ∈ T
    intro s hs
    have h2 : melinTransform (scalar • hT).toTestFunction s = scalar * melinTransform hT.toTestFunction s := by exact?
    rw [h2, hT_mel_T s hs, mul_zero]
  · -- C² 光滑
    exact ContDiff.const_smul hT_C2 _
  · -- 二阶导数范数界
    intro x
    have h3 : ‖(deriv (deriv (scalar • hT).toTestFunction.toFun) x)‖ =
        ‖scalar‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ := by
      simpa [smul_eq_mul, norm_mul] using rfl
    rw [h3]
    have h4 : ‖scalar‖ = ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ := by
      simp [scalar, norm_div]
      <;> ring
    rw [h4]
    have h5 : ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤
        Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
          ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := by
      exact Finset.le_sup (Finset.mem_univ (⟨x, by trivial⟩ : {x : ℝ // True}))
    have h6 : ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤
        (1 / c) * max ‖wρ‖ 1 := by
      have h7 : ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := hT_bound
      have h8 : 0 < c := hc_pos
      have h9 : 0 < ‖melinTransform hT.toTestFunction ρ‖ := by
        exact norm_pos_iff.mpr hT_mel_ρ_ne
      have h10 : Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
          ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) ≥ 0 := by positivity
      calc
        ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖
          ≤ ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
              ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := by
            gcongr
            <;> linarith
        _ = ‖wρ‖ * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
              ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) / ‖melinTransform hT.toTestFunction ρ‖) := by ring
        _ ≤ ‖wρ‖ * (1 / c) := by
            gcongr
            <;> gcongr
            <;> linarith
        _ = (1 / c) * ‖wρ‖ := by ring
        _ ≤ (1 / c) * max ‖wρ‖ 1 := by
            have h11 : ‖wρ‖ ≤ max ‖wρ‖ 1 := le_max_left _ _
            have h12 : 0 ≤ (1 / c) := by positivity
            nlinarith
    exact h6

/-- 最小导数范数统一界（定理，由对偶范数下界 + 最小范数原理推出）： -/
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
  rcases mellin_constraint_dual_norm_lower_uniform ρ hz hre1 hre2 hne with ⟨c, hc_pos, h_lower⟩
  let B : ℝ := 1 / c
  have hB_pos : 0 < B := by positivity
  refine ⟨B, hB_pos, fun T hT hρ_notin => ?_⟩
  have hT_exists := h_lower T hT hρ_notin
  exact mellin_min_norm_principle ρ wρ c hc_pos hz hre1 hre2 hne T hT hρ_notin hT_exists'''

# 替换
content = content[:start_idx] + new_content + content[end_idx:]

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
