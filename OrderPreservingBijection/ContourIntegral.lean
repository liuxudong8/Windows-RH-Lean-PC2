/-
  围道积分基础设施模块
  为 Weil 显式公式提供围道积分、ζ 对数导数、素理想 Dirichlet 级数、留数定理等。
  依赖 BasicInfrastructure、MellinInfrastructure、ZetaZeros。
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ZetaZeros

set_option maxHeartbeats 600000

namespace OrderPreservingBijection

open Filter
open scoped Topology
open ArithmeticFunction.vonMangoldt

/-- 围道半径（def）：Weil 显式公式中使用的圆围道半径。
    以 1/2 为中心。具体值不影响结论（围道积分形变不变性），取 1 简化。
    从 opaque 降为 def：任意正实数均可，取 1 是规范选择。 -/
def contourRadius : ℝ := 1

/-- 围道半径为正（定理，由定义直接推出）。 -/
theorem contourRadius_pos : 0 < contourRadius := by
  simp [contourRadius] <;> norm_num

/-- 归一化围道积分（def）：(1/2πi) ∮_{|s - 1/2| = contourRadius} g(s) ds。
    用 Mathlib 的 circleIntegral 实现，中心在 1/2（临界线中点）。 -/
noncomputable def contourIntegral (g : ℂ → ℂ) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g (1 / 2 : ℂ) contourRadius

/-- Contour integral linearity (theorem, from Mathlib circleIntegral):
    For CircleIntegrable g1, g2, contourIntegral(c1*g1 + c2*g2) = c1*contourIntegral(g1) + c2*contourIntegral(g2).
    Downgraded from axiom: Mathlib has circleIntegral.integral_add (with integrable premise) and integral_smul. -/
theorem contourIntegral_linear (g1 g2 : ℂ → ℂ) (c1 c2 : ℂ)
    (h1 : CircleIntegrable g1 (1 / 2 : ℂ) contourRadius)
    (h2 : CircleIntegrable g2 (1 / 2 : ℂ) contourRadius) :
    contourIntegral (fun s => c1 * g1 s + c2 * g2 s) = c1 * contourIntegral g1 + c2 * contourIntegral g2 := by
  have h1s : CircleIntegrable (fun s => c1 • g1 s) (1 / 2 : ℂ) contourRadius := h1.const_smul (a := c1)
  have h2s : CircleIntegrable (fun s => c2 • g2 s) (1 / 2 : ℂ) contourRadius := h2.const_smul (a := c2)
  have h_eq1 : (fun s : ℂ => c1 * g1 s + c2 * g2 s) = fun s => c1 • g1 s + c2 • g2 s := by
    funext s; simp [smul_eq_mul]
  rw [h_eq1]
  simp only [contourIntegral, circleIntegral.integral_add h1s h2s, circleIntegral.integral_smul]
  <;> simp [smul_eq_mul] <;> ring

/-- 黎曼ζ函数的对数导数（def）：ζ'/ζ(s) = (dζ/ds)(s) / ζ(s)。
    在 ζ(s) ≠ 0 且 s ≠ 1 处有定义；零点处用 0 占位（留数由围道积分处理）。
    Mathlib 有 differentiableAt_riemannZeta（s ≠ 1 处可微）。 -/
noncomputable def zetaLogDerivative (s : ℂ) : ℂ :=
    if _root_.riemannZeta s = 0 then 0
    else deriv _root_.riemannZeta s / _root_.riemannZeta s

/-- 素理想 Dirichlet 级数（def）：D(s) = Σ_p (log p) p^{-s} / (1 - p^{-s})。
    这是几何侧素理想加权求和的生成函数，Re(s) > 1 时绝对收敛。
    由 Euler 乘积 ζ(s) = ∏_p (1 - p^{-s})^{-1}，取对数导数得 ζ'/ζ(s) = D(s)。 -/
noncomputable def primeDirichletSeries (s : ℂ) : ℂ :=
    ∑' p : ℕ, if Nat.Prime p then (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) else 0

/-- 柯西定理（围道积分版本）：g 在闭圆盘上连续，开圆盘内全纯，则围道积分为零。
    桥接 mathlib Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable。 -/
lemma cauchy_theorem_contour (g : ℂ → ℂ)
    (h_cont : ContinuousOn g (Metric.closedBall (1 / 2 : ℂ) contourRadius))
    (h_diff : ∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius, DifferentiableAt ℂ g s) :
    contourIntegral g = 0 := by
  have h_diff' : ∀ z ∈ Metric.ball (1 / 2 : ℂ) contourRadius \ (∅ : Set ℂ), DifferentiableAt ℂ g z := by
    intro z hz; exact h_diff z hz.1
  have h_main : circleIntegral g (1 / 2 : ℂ) contourRadius = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      (by linarith [contourRadius_pos]) Set.countable_empty h_cont h_diff'
  simpa [contourIntegral] using h_main

/-- 简单极点留数（局部版，定理，真证）：h 只在半径为 r 的小圆内可微（无需 1-球），
    则 (2πi)⁻¹ ∮_{|s-z0|=r} g = h z0（g = h/(s-z0)，r 内）。
    与 simplePole_residue_radius（1-球版）的区别：本版假设 h 在 ball z0 r 内可微，
    供局部极点分解（ζ 零点/极点邻域）使用。由柯西积分公式
    （Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable）推出。 -/
lemma simplePole_residue_local (g h : ℂ → ℂ) (z0 : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hc : ContinuousOn h (Metric.closedBall z0 r))
    (hd : ∀ z ∈ Metric.ball z0 r, DifferentiableAt ℂ h z)
    (h_eq : ∀ s ∈ Metric.closedBall z0 r, s ≠ z0 → g s = h s / (s - z0)) :
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 r = h z0 := by
  have h_eq_on_sphere : Set.EqOn g (fun s => (s - z0)⁻¹ • h s) (Metric.sphere z0 r) := by
    intro s hs
    have hs_dist : dist s z0 = r := by simpa using (Metric.mem_sphere.mp hs)
    have hs_cl : s ∈ Metric.closedBall z0 r := by
      exact Metric.mem_closedBall.mpr (by linarith [hs_dist, hr])
    have hs_ne : s ≠ z0 := by
      intro hne
      have : dist s z0 = 0 := by rw [hne, dist_self]
      linarith
    have hg : g s = h s / (s - z0) := h_eq s hs_cl hs_ne
    rw [hg]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have h_congr : circleIntegral g z0 r = circleIntegral (fun s => (s - z0)⁻¹ • h s) z0 r :=
    circleIntegral.integral_congr hr.le h_eq_on_sphere
  have hd' : ∀ z ∈ Metric.ball z0 r \ (∅ : Set ℂ), DifferentiableAt ℂ h z := by
    intro z hz
    exact hd z hz.1
  have h_cauchy : circleIntegral (fun s => (s - z0)⁻¹ • h s) z0 r =
      (2 * Real.pi * Complex.I) • h z0 :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (R := r) (f := h) (c := z0) (s := (∅ : Set ℂ)) hr Set.countable_empty hc hd'
  rw [h_congr, h_cauchy]
  simp only [smul_eq_mul]
  change (2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I * h z0) = h z0
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- 解析点 ⟹ 存在有限正半径实球，球内每点解析（收缩 HasFPowerSeriesOnBall 的 ENNReal 半径到有限 ℝ 球）。
    主引理 ε-球构造的基础：对 ζ'/ζ 分解中的正则因子 G 在每个极点 z0 取局部解析球。 -/
lemma analyticAt_finite_ball {G : ℂ → ℂ} {z0 : ℂ} (hGA : AnalyticAt ℂ G z0) :
    ∃ r : ℝ, 0 < r ∧ (∀ s ∈ Metric.ball z0 r, AnalyticAt ℂ G s) := by
  rcases hGA with ⟨p, hp⟩
  rcases hp with ⟨r0, hr0_le, hr0_pos, hr0_ball⟩
  let hb0' : HasFPowerSeriesOnBall G p z0 r0 := ⟨hr0_le, hr0_pos, hr0_ball⟩
  let r0c : ENNReal := min r0 (ENNReal.ofReal 1)
  have hr0c_pos : 0 < r0c := by
    exact lt_min hr0_pos (by simp [ENNReal.ofReal_one])
  have hr0c_lt_top : r0c < ⊤ := by
    exact min_lt_iff.mpr (Or.inr ENNReal.ofReal_lt_top)
  have hr0c_le : r0c ≤ r0 := min_le_left _ _
  have hb0 : HasFPowerSeriesOnBall G p z0 r0c := by
    refine ⟨le_trans hr0c_le hb0'.r_le, hr0c_pos, ?_⟩
    intro y hy
    exact hb0'.hasSum (by
      rw [Metric.mem_eball] at hy ⊢
      exact lt_of_lt_of_le hy hr0c_le)
  have hr0c_real_pos : 0 < r0c.toReal := ENNReal.toReal_pos_iff.mpr ⟨hr0c_pos, hr0c_lt_top⟩
  have hG_an : AnalyticOnNhd ℂ G (Metric.eball z0 r0c) := hb0.analyticOnNhd
  refine ⟨r0c.toReal / 2, by positivity, ?_⟩
  intro s hs
  have hd : dist s z0 < r0c.toReal / 2 := Metric.mem_ball.mp hs
  have hdlt : dist s z0 < r0c.toReal := lt_of_lt_of_le hd (le_of_lt (half_lt_self hr0c_real_pos))
  have hs_eb : s ∈ Metric.eball z0 r0c := by
    rw [Metric.mem_eball, edist_dist]
    rw [← ENNReal.ofReal_toReal (ne_of_lt hr0c_lt_top)]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0c_real_pos).mpr hdlt
  exact hG_an s hs_eb

/-- 连续延拓值引理：h 与 F 都在 z0 连续，且在去心邻域相等 ⟹ h z0 = F z0。
    用于从简单极点等式（s ≠ z0 ⟹ g s = h s/(s-z0)）提取 h 在 z0 的延拓值（= 留数）。 -/
lemma cont_congr_value {h F : ℂ → ℂ} {z0 : ℂ}
    (hc : ContinuousAt h z0) (hF : ContinuousAt F z0)
    (heq : ∀ᶠ s in 𝓝[≠] z0, h s = F s) : h z0 = F z0 := by
  have ht1 : Tendsto h (𝓝[≠] z0) (𝓝 (h z0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto F (𝓝[≠] z0) (𝓝 (F z0)) := hF.tendsto.mono_left nhdsWithin_le_nhds
  have ht1' : Tendsto F (𝓝[≠] z0) (𝓝 (h z0)) := ht1.congr' heq
  exact tendsto_nhds_unique ht1' ht2

/-- 函数在一点处的留数（def）：
    Res(g, z0) = (1/2πi) ∮_{|z-z0|=ε} g(z) dz，
    其中 ε 足够小使得圆周内只有 z0 一个奇点。
    用 circleIntegral 实现，半径取 1/2（留数与半径无关，由柯西定理保证）。
    留数是 Laurent 展开中 (z-z0)^{-1} 项的系数。 -/
noncomputable def residueAt (g : ℂ → ℂ) (z0 : ℂ) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 (1 / 2)

section ResidueBasics

/-- 围道上连续 ⟹ CircleIntegrable（辅助）：闭合圆上连续函数可积。
    由 Mathlib ContinuousOn.circleIntegrable' 推出。 -/
lemma circleIntegrable_of_continuousOn (g : ℂ → ℂ)
    (h : ContinuousOn g (Metric.sphere (1 / 2 : ℂ) contourRadius)) :
    CircleIntegrable g (1 / 2 : ℂ) contourRadius := by
  have h' : ContinuousOn g (Metric.sphere (1 / 2 : ℂ) |contourRadius|) := by
    simpa [abs_of_nonneg contourRadius_pos.le] using h
  exact h'.circleIntegrable'

/-- 核 (s-z0)⁻¹ 的围道积分（定理）：z0 在围道内 ⟹ contourIntegral(s ↦ (s-z0)⁻¹) = 1。
    由 Mathlib circleIntegral.integral_sub_inv_of_mem_ball（∮_{|s-1/2|=1} (s-z0)⁻¹ ds = 2πi）推出。 -/
lemma contourIntegral_inv_sub (z0 : ℂ) (hz : z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius) :
    contourIntegral (fun s => (s - z0)⁻¹) = 1 := by
  unfold contourIntegral
  rw [circleIntegral.integral_sub_inv_of_mem_ball hz]
  change (2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I) = 1
  exact inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)

/-- 简单极点处小圆留数 = 核系数（定理，半径参数化）：
    若 g = h/(s-z0)（h 在 z0 的 1-球内可微）且 0 < r < 1，
    则 (2πi)⁻¹ ∮_{|s-z0|=r} g(s) ds = h z0。
    由柯西积分公式（Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable）推出。
    数学意义：一阶极点 z0 处的小圆留数 = 核系数 h z0，与半径 r 无关（r 足够小）。 -/
lemma simplePole_residue_radius (g h : ℂ → ℂ) (z0 : ℂ) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (hd : DifferentiableOn ℂ h (Metric.ball z0 1))
    (h_eq : ∀ s ∈ Metric.ball z0 1, s ≠ z0 → g s = h s / (s - z0)) :
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 r = h z0 := by
  have h_eq_on_sphere : Set.EqOn g (fun s => (s - z0)⁻¹ • h s) (Metric.sphere z0 r) := by
    intro s hs
    have hs_dist : dist s z0 = r := by simpa using (Metric.mem_sphere.mp hs)
    have hs_ball : s ∈ Metric.ball z0 1 := by
      exact Metric.mem_ball.mpr (by linarith [hs_dist, hr1])
    have hs_ne : s ≠ z0 := by
      intro hne
      have : dist s z0 = 0 := by rw [hne, dist_self]
      linarith
    have hg : g s = h s / (s - z0) := h_eq s hs_ball hs_ne
    rw [hg]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have h_congr : circleIntegral g z0 r = circleIntegral (fun s => (s - z0)⁻¹ • h s) z0 r :=
    circleIntegral.integral_congr hr.le h_eq_on_sphere
  have hc : ContinuousOn h (Metric.closedBall z0 r) := by
    exact hd.continuousOn.mono (Metric.closedBall_subset_ball hr1)
  have hd' : ∀ z ∈ Metric.ball z0 r \ (∅ : Set ℂ), DifferentiableAt ℂ h z := by
    intro z hz
    have hz1 : z ∈ Metric.ball z0 1 := by
      exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hz.1, hr1])
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
  have h_cauchy : circleIntegral (fun s => (s - z0)⁻¹ • h s) z0 r =
      (2 * Real.pi * Complex.I) • h z0 :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (R := r) (f := h) (c := z0) (s := (∅ : Set ℂ)) hr Set.countable_empty hc hd'
  rw [h_congr, h_cauchy]
  simp only [smul_eq_mul]
  change (2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I * h z0) = h z0
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- 核和引理（系数版）：Σ_{z0∈S} c(z0)/(s-z0) 的围道积分 = Σ_{z0∈S} c(z0)。
    线性性（contourIntegral_linear）+ 每个核的围道积分 = 1（contourIntegral_inv_sub）。
    与旧 residueAt 版（已删除）的区别：系数 c 任意，供留数定理"核减除"使用。 -/
lemma contourIntegral_kernel_sum (c : ℂ → ℂ) (S : Finset ℂ)
    (h_sub : ∀ z0 ∈ S, z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius) :
    contourIntegral (fun s => ∑ z0 ∈ S, c z0 / (s - z0)) =
    ∑ z0 ∈ S, c z0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hzero : contourIntegral (fun _ : ℂ => (0 : ℂ)) = 0 := by
        have hlin := contourIntegral_linear (fun s : ℂ => s) (fun _ : ℂ => (0 : ℂ)) 0 0
          (circleIntegrable_id (1 / 2 : ℂ) contourRadius)
          (circleIntegrable_const (0 : ℂ) (1 / 2 : ℂ) contourRadius)
        simpa using hlin
      simpa using hzero
  | insert z0 S hz0 ih =>
      have hsub_z0 : z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius := h_sub z0 (by simp)
      have hsub_S : ∀ z0 ∈ S, z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius :=
        fun z hz => h_sub z (by simp [hz])
      have ih' := ih hsub_S
      have hzne : ∀ s ∈ Metric.sphere (1 / 2 : ℂ) contourRadius, s ≠ z0 := by
        intro s hs
        have ht : dist s (1 / 2 : ℂ) ≤ dist s z0 + dist z0 (1 / 2 : ℂ) := dist_triangle s z0 (1 / 2 : ℂ)
        have hsph : dist s (1 / 2 : ℂ) = contourRadius := by simpa using (Metric.mem_sphere.mp hs)
        have hz : dist z0 (1 / 2 : ℂ) < contourRadius := Metric.mem_ball.mp hsub_z0
        have hdist : 0 < dist s z0 := by linarith
        exact (dist_pos.mp hdist)
      have hci_inv : CircleIntegrable (fun s => (s - z0)⁻¹) (1 / 2 : ℂ) contourRadius := by
        apply circleIntegrable_of_continuousOn
        exact (continuousOn_id.sub continuousOn_const).inv₀ (fun s hs => sub_ne_zero.mpr (hzne s hs))
      have hci_new : CircleIntegrable (fun s => c z0 / (s - z0)) (1 / 2 : ℂ) contourRadius := by
        apply circleIntegrable_of_continuousOn
        refine ((continuousOn_id.sub continuousOn_const).inv₀ (fun s hs => sub_ne_zero.mpr (hzne s hs))).const_mul (c z0)
      have hci_old : CircleIntegrable (fun s => ∑ z0 ∈ S, c z0 / (s - z0)) (1 / 2 : ℂ) contourRadius := by
        apply circleIntegrable_of_continuousOn
        refine continuousOn_finsetSum S ?_
        intro z hzS
        have hsub_z : z ∈ Metric.ball (1 / 2 : ℂ) contourRadius := hsub_S z hzS
        have hzne' : ∀ s ∈ Metric.sphere (1 / 2 : ℂ) contourRadius, s ≠ z := by
          intro s hs
          have ht : dist s (1 / 2 : ℂ) ≤ dist s z + dist z (1 / 2 : ℂ) := dist_triangle s z (1 / 2 : ℂ)
          have hsph : dist s (1 / 2 : ℂ) = contourRadius := by simpa using (Metric.mem_sphere.mp hs)
          have hz : dist z (1 / 2 : ℂ) < contourRadius := Metric.mem_ball.mp hsub_z
          have hdist : 0 < dist s z := by linarith
          exact (dist_pos.mp hdist)
        exact ((continuousOn_id.sub continuousOn_const).inv₀ (fun s hs => sub_ne_zero.mpr (hzne' s hs))).const_mul (c z)
      have hfun : (fun s => ∑ z0 ∈ insert z0 S, c z0 / (s - z0)) =
          fun s => c z0 / (s - z0) + ∑ z0 ∈ S, c z0 / (s - z0) := by
        funext s
        simp [Finset.sum_insert hz0]
      rw [hfun]
      have hlin := contourIntegral_linear (fun s => c z0 / (s - z0))
        (fun s => ∑ z0 ∈ S, c z0 / (s - z0)) 1 1 hci_new hci_old
      have hlin' : contourIntegral (fun s => c z0 / (s - z0) + ∑ z0 ∈ S, c z0 / (s - z0)) =
          contourIntegral (fun s => c z0 / (s - z0)) + contourIntegral (fun s => ∑ z0 ∈ S, c z0 / (s - z0)) := by
        simpa using hlin
      rw [hlin']
      have hkern : contourIntegral (fun s => c z0 / (s - z0)) = c z0 := by
        have hlin2 := contourIntegral_linear (fun s => (s - z0)⁻¹) (fun _ : ℂ => (0 : ℂ))
          (c z0) 0 hci_inv (circleIntegrable_const (0 : ℂ) (1 / 2 : ℂ) contourRadius)
        have hlin2' : contourIntegral (fun s => c z0 / (s - z0)) =
            c z0 * contourIntegral (fun s => (s - z0)⁻¹) := by
          have htmp : (fun s => c z0 / (s - z0)) =
              fun s => c z0 * (s - z0)⁻¹ + 0 * (0 : ℂ) := by
            funext s
            simp [div_eq_mul_inv]
          rw [htmp, hlin2]
          simp
        rw [hlin2', contourIntegral_inv_sub z0 hsub_z0, mul_one]
      rw [hkern, ih', Finset.sum_insert hz0]

/-- 极点消除（辅助）：若 g 在 z0 连续、h 在 z0 可微，且 g s = h s/(s-z0) 于 z0 的去心邻域成立，
    则 h z0 = 0。数学依据：g s·(s-z0) = h s（s ≠ z0），两侧取极限 s → z0：g z0·0 = h z0。
    用途：连续函数 g 若在某点表现为"简单极点 h/(s-z0)"，则核系数 h z0 必为零，
    使留数定理的"核减除"函数在该点可去。 -/
lemma pole_zero_of_continuous (g h : ℂ → ℂ) (z0 : ℂ)
    (h_cont : ContinuousAt g z0) (h_diff : DifferentiableAt ℂ h z0)
    (h_eq : ∀ᶠ s in nhdsWithin z0 ({z0}ᶜ), g s = h s / (s - z0)) :
    h z0 = 0 := by
  have h_self : {z0}ᶜ ∈ nhdsWithin z0 ({z0}ᶜ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.univ, isOpen_univ, trivial, by intro s hs; exact hs.2⟩
  have h_nebot : NeBot (nhdsWithin z0 ({z0}ᶜ)) := by
    infer_instance
  have h_ge : (fun s => g s * (s - z0)) =ᶠ[nhdsWithin z0 ({z0}ᶜ)] h := by
    rw [Filter.EventuallyEq]
    filter_upwards [h_eq, h_self] with s hs hne
    rw [hs]
    field_simp [sub_ne_zero.mpr hne]
  have h_t1 : Filter.Tendsto (fun s => g s * (s - z0)) (nhdsWithin z0 ({z0}ᶜ)) (nhds (g z0 * (z0 - z0))) := by
    have hg : Filter.Tendsto g (nhdsWithin z0 ({z0}ᶜ)) (nhds (g z0)) := h_cont.tendsto.mono_left nhdsWithin_le_nhds
    have hsub0 : Filter.Tendsto (fun s : ℂ => s - z0) (nhds z0) (nhds (z0 - z0)) := tendsto_id.sub tendsto_const_nhds
    exact hg.mul (hsub0.mono_left nhdsWithin_le_nhds)
  have h_t2 : Filter.Tendsto h (nhdsWithin z0 ({z0}ᶜ)) (nhds (h z0)) := h_diff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_lim_eq : g z0 * (z0 - z0) = h z0 :=
    tendsto_nhds_unique_of_eventuallyEq h_t1 h_t2 h_ge
  calc h z0 = g z0 * (z0 - z0) := h_lim_eq.symm
    _ = 0 := by simp

end ResidueBasics

/-- 一般留数定理（小圆版，陈述）：
    g 在围道 |s-1/2| = contourRadius 内部除有限个简单极点 S 外全纯，则
      contourIntegral g = Σ_{z0 ∈ S} (2πi)⁻¹ ∮_{|s-z0|=ε(z0)} g(s) ds，
    其中每个 ε(z0) > 0 足够小（小圆互不相交、都在围道内，ε(z0) < 1 以适用简单极点引理）。
    数学依据：多连通区域 Cauchy 定理（大圆积分 = 小圆积分之和），经"留数核减除"实现：
      g₁ = g - Σ_{z0∈S} A(z0)/(s-z0)（A(z0) = 小圆留数）在围道内全纯（简单极点处由
      simplePole_residue_radius 知 A(z0) = h z0，核减除后奇点可去），由 Cauchy 定理 ∮ g₁ = 0；
      而 ∮ Σ A(z0)/(s-z0) = Σ A(z0)（contourIntegral_inv_sub / contourIntegral_kernel_sum）。
    说明：
    (1) 此处使用"小圆留数"而非 residueAt（固定半径 1/2）——围道内奇点可能相距 < 1，
        固定半径 1/2 的 residueAt 不总等于数学留数；小圆版不需要奇点分离假设。
    (2) 通用版（允许本性奇点）需要 Casorati-Weierstrass 或同调 Cauchy（mathlib 未形式化）；
        主链 ζ'/ζ·M[f] 的奇点均为一阶极点（零点处留数 = 阶数，s=1 处留数 = -1），简单极点版足够。
    证明主体（已完成，2026-10-01 围道连续版）：前提用 h_diff_off（closedBall \ S 上可微）
    替代旧版 h_cont（closedBall 连续）——旧版只覆盖"可去奇点"情形（pole_zero_of_continuous
    强制小圆留数为 0），对 ζ'/ζ·M[f] 的真极点（零点、s=1）不适用。新证明：
    核减除 g₁ = g - Σ A(z0)/(s-z0)，A(z0) = h z0（simplePole_residue_local）；定义延拓
    g₁bar（S 处 = deriv H s - Σ_{z≠s} A z/(s-z)，由 HasDerivAt.tendsto_slope 保证连续），
    g₁bar 在 closedBall 连续（S 处 ContinuousAt + closedBall\S 上 = g₁）且 ball 内可微
    （S 处经可去奇点定理 analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt），
    Cauchy 定理（cauchy_theorem_contour）给 ∮g₁bar = 0；∮g₁ = ∮g₁bar（sphere 上一致，
    integral_congr）；核和由 contourIntegral_kernel_sum 求和，线性性
    （contourIntegral_linear）拼装得 ∮g = Σ_{z0∈S} A(z0)。 -/
lemma residue_theorem_general (g : ℂ → ℂ) (S : Finset ℂ) (ε : ℂ → ℝ)
    (h_diff_off : ∀ z ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ),
      DifferentiableAt ℂ g z)
    (h_sub : ∀ z0 ∈ S, z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius)
    (h_pole : ∀ z0 ∈ S, ∃ h : ℂ → ℂ,
      ContinuousOn h (Metric.closedBall z0 (ε z0)) ∧
      (∀ s ∈ Metric.ball z0 (ε z0), DifferentiableAt ℂ h s) ∧
      ∀ s ∈ Metric.closedBall z0 (ε z0), s ≠ z0 → g s = h s / (s - z0))
    (h_eps : ∀ z0 ∈ S, 0 < ε z0 ∧ ε z0 < 1 ∧
      Metric.ball z0 (ε z0) ⊆ Metric.ball (1 / 2 : ℂ) contourRadius ∧
      ∀ z ∈ Metric.ball z0 (ε z0), z ∈ S → z = z0) :
    contourIntegral g =
    ∑ z0 ∈ S, (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 (ε z0) := by
  classical
  let A : ℂ → ℂ := fun z => if z ∈ S then (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z (ε z) else 0
  let H : S → ℂ → ℂ := fun z0 => (h_pole z0.1 z0.2).choose
  have hH_cont : ∀ z0 : S, ContinuousOn (H z0) (Metric.closedBall z0.1 (ε z0.1)) := by
    intro z0; exact (h_pole z0.1 z0.2).choose_spec.1
  have hH_diff : ∀ z0 : S, ∀ s ∈ Metric.ball z0.1 (ε z0.1), DifferentiableAt ℂ (H z0) s := by
    intro z0; exact (h_pole z0.1 z0.2).choose_spec.2.1
  have hH_eq : ∀ z0 : S, ∀ s ∈ Metric.closedBall z0.1 (ε z0.1), s ≠ z0.1 → g s = H z0 s / (s - z0.1) := by
    intro z0; exact (h_pole z0.1 z0.2).choose_spec.2.2
  have hA_eqH : ∀ z0 : S, A z0.1 = H z0 z0.1 := by
    intro z0
    have h_res : (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0.1 (ε z0.1) = H z0 z0.1 := by
      exact simplePole_residue_local g (H z0) z0.1 (ε z0.1)
        (h_eps z0.1 z0.2).1 (hH_cont z0) (hH_diff z0) (hH_eq z0)
    change (if z0.1 ∈ S then (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0.1 (ε z0.1) else 0) = H z0 z0.1
    rw [if_pos z0.2]
    exact h_res
  have h_sph_ne : ∀ s ∈ Metric.sphere (1 / 2 : ℂ) contourRadius, ∀ z0 ∈ S, s ≠ z0 := by
    intro s hs z0 hz0S
    have hz0d : dist z0 (1 / 2 : ℂ) < contourRadius := Metric.mem_ball.mp (h_sub z0 hz0S)
    have hsd : dist s (1 / 2 : ℂ) = contourRadius := Metric.mem_sphere.mp hs
    intro h_eq
    rw [h_eq] at hsd
    linarith
  have h_cont_g_off : ContinuousOn g (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) := by
    intro z hz
    exact (h_diff_off z hz).continuousAt.continuousWithinAt
  have h_cont_sum_at : ∀ x : ℂ, ∀ t : Finset ℂ, (∀ z ∈ t, z ≠ x) →
      ContinuousAt (fun u : ℂ => ∑ z ∈ t, A z / (u - z)) x := by
    intro x t ht_ne
    induction t using Finset.induction_on with
    | empty => exact continuousAt_const
    | insert z zs hz hzs =>
        have hz_ne : z ≠ x := ht_ne z (by simp)
        have hzs_ne : ∀ z' ∈ zs, z' ≠ x := fun z' hz' => ht_ne z' (by simp [hz'])
        have h_cont_item : ContinuousAt (fun u : ℂ => A z / (u - z)) x := by
          exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hz_ne.symm))
        have h_cont_rest : ContinuousAt (fun u : ℂ => ∑ z' ∈ zs, A z' / (u - z')) x := hzs hzs_ne
        have h_eq : (fun u : ℂ => ∑ z' ∈ insert z zs, A z' / (u - z')) =
            fun u => A z / (u - z) + ∑ z' ∈ zs, A z' / (u - z') := by
          funext u
          simp [Finset.sum_insert hz]
        rw [h_eq]
        exact h_cont_item.add h_cont_rest
  have h_cont_sum_off : ContinuousOn (fun s : ℂ => ∑ z0 ∈ S, A z0 / (s - z0))
      (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) := by
    intro s hs
    exact (h_cont_sum_at s S (fun z hz h_eq => hs.2 (h_eq ▸ hz))).continuousWithinAt
  let g1 : ℂ → ℂ := fun s => g s - ∑ z0 ∈ S, A z0 / (s - z0)
  have h_decomp : (fun s : ℂ => g s) = fun s => g1 s + ∑ z0 ∈ S, A z0 / (s - z0) := by
    funext s
    simp [g1]
  have h_cont_g1_off : ContinuousOn g1 (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) := by
    intro s hs
    exact (h_cont_g_off s hs).sub (h_cont_sum_off s hs)
  have h_sph_sub : Metric.sphere (1 / 2 : ℂ) contourRadius ⊆
      Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ) := by
    intro z hz
    exact ⟨Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz)), by
      intro hzS; exact h_sph_ne z hz z hzS (by rfl)⟩
  have h_cont_g1_sphere : ContinuousOn g1 (Metric.sphere (1 / 2 : ℂ) contourRadius) :=
    h_cont_g1_off.mono h_sph_sub
  let g1bar : ℂ → ℂ := fun s => if hs : s ∈ S then
      deriv (H ⟨s, hs⟩) s - ∑ z ∈ S.erase s, A z / (s - z)
    else g1 s
  have h_eq_sphere : Set.EqOn g1bar g1 (Metric.sphere (1 / 2 : ℂ) contourRadius) := by
    intro s hs
    have hs_notS : s ∉ S := by
      intro hsS
      exact h_sph_ne s hs s hsS (by rfl)
    simp [g1bar, hs_notS]
  have h_cont_g1bar_S : ∀ s ∈ S, ContinuousAt g1bar s := by
    intro s hsS
    let hh : ℂ → ℂ := H ⟨s, hsS⟩
    have hd_at : DifferentiableAt ℂ hh s :=
      hH_diff ⟨s, hsS⟩ s (Metric.mem_ball.mpr (by rw [dist_self]; exact (h_eps s hsS).1))
    have h_slope : Tendsto (slope hh s) (nhdsWithin s ({s}ᶜ)) (nhds (deriv hh s)) :=
      hd_at.hasDerivAt.tendsto_slope
    have h_tend_sum : Tendsto (fun t : ℂ => ∑ z ∈ S.erase s, A z / (t - z))
        (nhdsWithin s ({s}ᶜ)) (nhds (∑ z ∈ S.erase s, A z / (s - z))) := by
      have hc : ContinuousAt (fun t : ℂ => ∑ z ∈ S.erase s, A z / (t - z)) s := by
        exact h_cont_sum_at s (S.erase s) (fun z hz => (Finset.mem_erase.mp hz).1)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have h_eq_punct : (fun t : ℂ => g1bar t) =ᶠ[nhdsWithin s ({s}ᶜ)]
        (fun t => (t - s)⁻¹ * (hh t - hh s) - ∑ z ∈ S.erase s, A z / (t - z)) := by
      have h_self' : {s}ᶜ ∈ nhdsWithin s ({s}ᶜ) := by
        rw [mem_nhdsWithin]
        exact ⟨Set.univ, isOpen_univ, trivial, by intro z hz; exact hz.2⟩
      have hball_ws : Metric.ball s (ε s) ∈ nhdsWithin s ({s}ᶜ) :=
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by rw [dist_self]; exact (h_eps s hsS).1)))
      filter_upwards [h_self', hball_ws] with t hts ht
      have ht_ne : t ≠ s := hts
      have ht_notS : t ∉ S := by
        intro htS
        have huniq : t = s := (h_eps s hsS).2.2.2 t ht htS
        exact ht_ne huniq
      have hg1bar : g1bar t = g1 t := by simp [g1bar, ht_notS]
      have hts1 : t ∈ Metric.closedBall s (ε s) := by
        exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp ht))
      have hg : g t = hh t / (t - s) := hH_eq ⟨s, hsS⟩ t hts1 ht_ne
      have h_sum_split : (∑ z0 ∈ S, A z0 / (t - z0)) = A s / (t - s) + ∑ z0 ∈ S.erase s, A z0 / (t - z0) := by
        rw [← Finset.sum_erase_add S (fun z : ℂ => A z / (t - z)) hsS]
        rw [add_comm]
      rw [hg1bar]
      dsimp [g1]
      change g t - ∑ z0 ∈ S, A z0 / (t - z0) =
        (t - s)⁻¹ * (hh t - hh s) - ∑ z ∈ S.erase s, A z / (t - z)
      rw [hg, h_sum_split]
      rw [hA_eqH ⟨s, hsS⟩]
      field_simp [ht_ne]
      ring
    have h_tend_g1bar : Tendsto (fun t : ℂ => g1bar t) (nhdsWithin s ({s}ᶜ)) (nhds (g1bar s)) := by
      have hg1bar_s : g1bar s = deriv hh s - ∑ z ∈ S.erase s, A z / (s - z) := by
        dsimp [g1bar]
        simp [hsS, hh]
      rw [hg1bar_s]
      have h_combo : Tendsto (fun t : ℂ => slope hh s t - ∑ z ∈ S.erase s, A z / (t - z))
          (nhdsWithin s ({s}ᶜ)) (nhds (deriv hh s - ∑ z ∈ S.erase s, A z / (s - z))) :=
        h_slope.sub h_tend_sum
      exact h_combo.congr' (by
        simpa [slope] using h_eq_punct.symm)
    have h_tend_full : Tendsto (fun t : ℂ => g1bar t) (nhds s) (nhds (g1bar s)) := by
      rw [tendsto_def]
      intro U hU
      have hU' : g1bar ⁻¹' U ∈ nhdsWithin s ({s}ᶜ) := (tendsto_def.mp h_tend_g1bar) U hU
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU'
      rcases hU' with ⟨W0, hW0, hW0'⟩
      rw [mem_nhds_iff]
      rcases (mem_nhds_iff.mp hW0) with ⟨t0, ht0_sub, ht0_open, ht0_s⟩
      refine ⟨t0, ?_, ht0_open, ht0_s⟩
      intro x hx
      by_cases hx_eq : x = s
      · subst x
        exact Set.mem_preimage.mpr (mem_of_mem_nhds hU)
      · exact hW0' ⟨ht0_sub hx, hx_eq⟩
    exact h_tend_full
  have h_cont_g1bar : ContinuousOn g1bar (Metric.closedBall (1 / 2 : ℂ) contourRadius) := by
    intro s hs
    by_cases hsS : s ∈ S
    · exact (h_cont_g1bar_S s hsS).continuousWithinAt
    · have hs_off : s ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ) := ⟨hs, hsS⟩
      have h_eq_off : Set.EqOn g1bar g1 (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) := by
        intro z hz
        dsimp [g1bar]
        by_cases hzS : z ∈ S
        · exfalso
          exact hz.2 hzS
        · simp [hzS]
      have h_cont_g1bar_off : ContinuousOn g1bar (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) :=
        h_cont_g1_off.congr h_eq_off
      have hsS_nhds : (Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ)) ∈ nhdsWithin s (Metric.closedBall (1 / 2 : ℂ) contourRadius) := by
        rw [mem_nhdsWithin]
        exact ⟨(S : Set ℂ)ᶜ, (Finset.isClosed (s := S)).isOpen_compl, hsS, by
          intro z hz; exact ⟨hz.2, hz.1⟩⟩
      exact (h_cont_g1bar_off s hs_off).mono_of_mem_nhdsWithin hsS_nhds
  have h_diff_sum_at : ∀ x : ℂ, ∀ t : Finset ℂ, (∀ z ∈ t, z ≠ x) →
      DifferentiableAt ℂ (fun u : ℂ => ∑ z ∈ t, A z / (u - z)) x := by
    intro x t ht_ne
    induction t using Finset.induction_on with
    | empty => simpa using differentiableAt_const (c := (0 : ℂ))
    | insert z zs hz hzs =>
        have hz_ne : z ≠ x := ht_ne z (by simp)
        have hzs_ne : ∀ z' ∈ zs, z' ≠ x := fun z' hz' => ht_ne z' (by simp [hz'])
        have hsub : DifferentiableAt ℂ (fun u : ℂ => u - z) x :=
          differentiableAt_id.sub (differentiableAt_const (c := z))
        have hinv : DifferentiableAt ℂ (fun u => (u - z)⁻¹) x := by
          simpa [Ring.inverse_eq_inv'] using
            (DifferentiableAt.inverse hsub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hz_ne.symm)))
        have hmul : DifferentiableAt ℂ (fun u : ℂ => A z * (u - z)⁻¹) x :=
          (differentiableAt_const (c := A z)).mul hinv
        have h_item : DifferentiableAt ℂ (fun u : ℂ => A z / (u - z)) x := by
          exact hmul.congr_of_eventuallyEq (by
            filter_upwards
            intro u
            simp [div_eq_mul_inv])
        have h_rest : DifferentiableAt ℂ (fun u : ℂ => ∑ z' ∈ zs, A z' / (u - z')) x := hzs hzs_ne
        have h_eq : (fun u : ℂ => ∑ z' ∈ insert z zs, A z' / (u - z')) =
            fun u => A z / (u - z) + ∑ z' ∈ zs, A z' / (u - z') := by
          funext u
          simp [Finset.sum_insert hz]
        rw [h_eq]
        exact h_item.add h_rest
  have h_diff_g1bar : ∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius, DifferentiableAt ℂ g1bar s := by
    intro s hs
    by_cases hsS : s ∈ S
    · have h_punct : ∀ᶠ z in nhdsWithin s ({s}ᶜ), DifferentiableAt ℂ g1bar z := by
        have h_self' : {s}ᶜ ∈ nhdsWithin s ({s}ᶜ) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.univ, isOpen_univ, trivial, by intro z hz; exact hz.2⟩
        have hball_ws : Metric.ball s (ε s) ∈ nhdsWithin s ({s}ᶜ) :=
          mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by rw [dist_self]; exact (h_eps s hsS).1)))
        filter_upwards [h_self', hball_ws] with z hzne hzball
        have hz_notS : z ∉ S := by
          intro hzS
          have huniq : z = s := (h_eps s hsS).2.2.2 z hzball hzS
          exact hzne huniq
        have hg1bar_z : g1bar z = g1 z := by simp [g1bar, hz_notS]
        have hz_closed : z ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ) := by
          have hz_ball_main : z ∈ Metric.ball (1 / 2 : ℂ) contourRadius := (h_eps s hsS).2.2.1 hzball
          exact ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz_ball_main)), hz_notS⟩
        have hgd : DifferentiableAt ℂ g z := h_diff_off z hz_closed
        have hSumD : DifferentiableAt ℂ (fun u : ℂ => ∑ z0 ∈ S, A z0 / (u - z0)) z := by
          exact h_diff_sum_at z S (fun z0 hz0S h_eq => hz_notS (h_eq ▸ hz0S))
        have h_eq_nhds : g1bar =ᶠ[nhds z] g1 := by
          refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨(↑S)ᶜ, ?_, ?_⟩
          · exact (Finset.isClosed (s := S)).isOpen_compl.mem_nhds (by simpa using hz_notS)
          · intro x hx
            have hxS : x ∉ S := by simpa using hx
            simp [g1bar, hxS]
        have hH1 : HasDerivAt g1 (deriv g1 z) z := (hgd.sub hSumD).hasDerivAt
        have hH2 : HasDerivAt g1bar (deriv g1 z) z := hH1.congr_of_eventuallyEq h_eq_nhds
        exact hH2.differentiableAt
      exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt h_punct (h_cont_g1bar_S s hsS)).differentiableAt
    · have hg1bar_s : g1bar s = g1 s := by simp [g1bar, hsS]
      have hs_closed : s ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius :=
        Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hs))
      have hgd : DifferentiableAt ℂ g s := h_diff_off s ⟨hs_closed, hsS⟩
      have hSumD : DifferentiableAt ℂ (fun u : ℂ => ∑ z0 ∈ S, A z0 / (u - z0)) s := by
        exact h_diff_sum_at s S (fun z0 hz0S h_eq => hsS (h_eq ▸ hz0S))
      have h_eq_nhds : g1bar =ᶠ[nhds s] g1 := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨(↑S)ᶜ, ?_, ?_⟩
        · exact (Finset.isClosed (s := S)).isOpen_compl.mem_nhds (by simpa using hsS)
        · intro x hx
          have hxS : x ∉ S := by simpa using hx
          simp [g1bar, hxS]
      have hH1 : HasDerivAt g1 (deriv g1 s) s := (hgd.sub hSumD).hasDerivAt
      have hH2 : HasDerivAt g1bar (deriv g1 s) s := hH1.congr_of_eventuallyEq h_eq_nhds
      exact hH2.differentiableAt
  have h_g1bar_zero : contourIntegral g1bar = 0 := by
    exact cauchy_theorem_contour g1bar h_cont_g1bar h_diff_g1bar
  have h_g1_zero : contourIntegral g1 = 0 := by
    have hci_g1bar : CircleIntegrable g1bar (1 / 2 : ℂ) contourRadius := by
      apply circleIntegrable_of_continuousOn
      exact h_cont_g1bar.mono (by intro z hz; exact Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz)))
    have hci_g1 : CircleIntegrable g1 (1 / 2 : ℂ) contourRadius := by
      apply circleIntegrable_of_continuousOn
      exact h_cont_g1_sphere
    have h_eq_int : circleIntegral g1bar (1 / 2 : ℂ) contourRadius = circleIntegral g1 (1 / 2 : ℂ) contourRadius :=
      circleIntegral.integral_congr (by linarith [contourRadius_pos]) h_eq_sphere
    have h_main : contourIntegral g1bar = contourIntegral g1 := by
      unfold contourIntegral
      rw [h_eq_int]
    rw [← h_main]
    exact h_g1bar_zero
  have h_kern : contourIntegral (fun s => ∑ z0 ∈ S, A z0 / (s - z0)) = ∑ z0 ∈ S, A z0 := by
    exact contourIntegral_kernel_sum A S h_sub
  have hci_g : CircleIntegrable g (1 / 2 : ℂ) contourRadius := by
    apply circleIntegrable_of_continuousOn
    exact h_cont_g_off.mono h_sph_sub
  have hci_g1 : CircleIntegrable g1 (1 / 2 : ℂ) contourRadius := by
    apply circleIntegrable_of_continuousOn
    exact h_cont_g1_sphere
  have hci_sum : CircleIntegrable (fun s => ∑ z0 ∈ S, A z0 / (s - z0)) (1 / 2 : ℂ) contourRadius := by
    apply circleIntegrable_of_continuousOn
    exact h_cont_sum_off.mono h_sph_sub
  have hlin := contourIntegral_linear g1 (fun s => ∑ z0 ∈ S, A z0 / (s - z0)) 1 1 hci_g1 hci_sum
  have hlin' : contourIntegral (fun s => g1 s + ∑ z0 ∈ S, A z0 / (s - z0)) =
      contourIntegral g1 + contourIntegral (fun s => ∑ z0 ∈ S, A z0 / (s - z0)) := by
    simpa using hlin
  have h_target : contourIntegral g = contourIntegral (fun s => g1 s + ∑ z0 ∈ S, A z0 / (s - z0)) := by
    rw [← h_decomp]
  rw [h_target, hlin', h_g1_zero, h_kern]
  have hA_eq : ∀ z0 ∈ S, A z0 = (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 (ε z0) := by
    intro z0 hz0S
    simp [A, hz0S]
  rw [Finset.sum_congr rfl hA_eq]
  simp

/-- 平移幂函数的对数导数（引理，真证）：logDeriv (fun s => (s-z0)^m) z = m/(z-z0)，z ≠ z0。
    证明：logDeriv_apply 展开 → deriv_pow（幂函数可微）+ 链法则（s ↦ s-z0），
    指数差用 pow_succ 化简，field_simp 消 (z-z0)。m=0 时两端均为 0。 -/
lemma logDeriv_pow_sub (z0 : ℂ) (m : ℕ) (z : ℂ) (hz : z ≠ z0) :
    logDeriv (fun s : ℂ => (s - z0) ^ m) z = (m : ℂ) / (z - z0) := by
  rw [logDeriv_apply]
  have hdiff : DifferentiableAt ℂ (fun s : ℂ => s - z0) z :=
    (differentiableAt_id.sub (differentiableAt_const (c := z0)))
  have hder1 : deriv (fun s : ℂ => s - z0) z = 1 := by
    have h := deriv_sub_const (c := z0) (f := fun s : ℂ => s) (x := z)
    simpa using h
  have hder : deriv (fun s : ℂ => (s - z0) ^ m) z = (m : ℂ) * (z - z0) ^ (m - 1) := by
    have h := deriv_pow hdiff m
    simpa [hder1] using h
  rw [hder]
  by_cases hm : m = 0
  · subst m
    simp
  · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨k, rfl⟩
    rw [pow_succ]
    have hsub : z - z0 ≠ 0 := by
      intro h
      exact hz (sub_eq_zero.mp h)
    have hsk : k.succ - 1 = k := Nat.succ_sub_one k
    field_simp [hsub]
    rw [hsk]

/-- ζ'/ζ 在非平凡零点 ρ 的对数导数分解（定理，真证）：
    ρ ∈ contourZeroFinset ⟹ 存在 G（在 ρ 解析且 G(ρ) ≠ 0），在 ρ 的去心邻域内
      zetaLogDerivative z = m/(z-ρ) + logDeriv G z，m = zeroMultiplicity ρ。
    证明：ζ 在 ρ 的 m 阶因式分解（mathlib AnalyticAt.analyticOrderNatAt_eq_iff）：
      ζ(s) = (s-ρ)^m · G(s)，G 解析非零；
    两侧取对数导数（logDeriv_congr_nhds 保持邻域相等、logDeriv_mul 拆分乘积、
      logDeriv_pow_sub 计算幂项），ζ 在零点去心邻域非零处 zetaLogDerivative = logDeriv ζ。
    本引理是 :431 围道留数计算中"零点处留数 = m(ρ)·M[f](ρ)"的 ζ 侧核心：
    乘以全纯因子 M[f] 后即得留数分类（M[f] 的解析性由模型层假设承担）。 -/
lemma zetaLogDerivative_decomposition_at_zero (ρ : ℂ) (hρ : ρ ∈ contourZeroFinset) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧ G ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, z ≠ ρ →
        zetaLogDerivative z = (zeroMultiplicity ρ : ℂ) / (z - ρ) + logDeriv G z := by
  have hρm : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ - (1 / 2 : ℂ)‖ < 1 :=
    (contourZeroFinset_mem ρ).mp hρ
  rcases hρm with ⟨hz, hre1, hre2, _⟩
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at hre2
    norm_num at hre2
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hne1)
  have hord : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrder_riemannZeta_ne_top hre1 hre2
  have hfac : ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧ G ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ zeroMultiplicity ρ * G z := by
    have h := (AnalyticAt.analyticOrderNatAt_eq_iff hA hord (n := zeroMultiplicity ρ)).1 (by rfl)
    rcases h with ⟨G, hGA, hGne0, hGeq⟩
    refine ⟨G, hGA, hGne0, ?_⟩
    filter_upwards [hGeq] with z hzeq
    simpa [smul_eq_mul] using hzeq
  rcases hfac with ⟨G, hGA, hGne0, hGeq⟩
  refine ⟨G, hGA, hGne0, ?_⟩
  have hG_ne : ∀ᶠ z in 𝓝 ρ, G z ≠ 0 := hGA.continuousAt.eventually_ne hGne0
  have hζ_ne : ∀ᶠ z in 𝓝 ρ, z ≠ ρ → riemannZeta z ≠ 0 := by
    filter_upwards [hGeq, hG_ne] with z hzeq hGz
    intro hzρ
    rw [hzeq]
    exact mul_ne_zero (pow_ne_zero (zeroMultiplicity ρ) (sub_ne_zero_of_ne hzρ)) hGz
  have h_logζ : ∀ᶠ z in 𝓝 ρ, z ≠ ρ → zetaLogDerivative z = logDeriv riemannZeta z := by
    filter_upwards [hζ_ne] with z hζz
    intro hzρ
    unfold zetaLogDerivative
    rw [if_neg (hζz hzρ)]
    rfl
  have h_logcongr : ∀ᶠ z in 𝓝 ρ,
      logDeriv riemannZeta z = logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ * G s) z := by
    exact logDeriv_congr_nhds hGeq
  have h_logmul : ∀ᶠ z in 𝓝 ρ, z ≠ ρ →
      logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ * G s) z =
        logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) z + logDeriv G z := by
    have hG_diff_near : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ G z := by
      rcases hGA with ⟨p, hp⟩
      exact hp.eventually_differentiableAt
    filter_upwards [hG_ne, hG_diff_near] with z hGz hGdiff
    intro hzρ
    change logDeriv ((fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) * G) z =
      logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) z + logDeriv G z
    have hf0 : (z - ρ) ^ zeroMultiplicity ρ ≠ 0 :=
      pow_ne_zero (zeroMultiplicity ρ) (sub_ne_zero_of_ne hzρ)
    have hfdiff : DifferentiableAt ℂ (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) z := by
      have hsubdiff : DifferentiableAt ℂ (fun s : ℂ => s - ρ) z :=
        differentiableAt_id.sub (differentiableAt_const (c := ρ))
      exact hsubdiff.pow (zeroMultiplicity ρ)
    exact logDeriv_mul z hf0 hGz hfdiff hGdiff
  have h_logpow : ∀ᶠ z in 𝓝 ρ, z ≠ ρ →
      logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) z =
        (zeroMultiplicity ρ : ℂ) / (z - ρ) := by
    filter_upwards with z
    intro hzρ
    exact logDeriv_pow_sub ρ (zeroMultiplicity ρ) z hzρ
  filter_upwards [h_logζ, h_logcongr, h_logmul, h_logpow] with z hL1 hL2 hL3 hL4
  intro hzρ
  calc
    zetaLogDerivative z = logDeriv riemannZeta z := hL1 hzρ
    _ = logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ * G s) z := hL2
    _ = logDeriv (fun s : ℂ => (s - ρ) ^ zeroMultiplicity ρ) z + logDeriv G z := hL3 hzρ
    _ = (zeroMultiplicity ρ : ℂ) / (z - ρ) + logDeriv G z := by rw [hL4 hzρ]

/-- 倒数平移的对数导数（引理，真证）：logDeriv (fun s => (s-z0)⁻¹) z = -1/(z-z0)，z ≠ z0。
    证明：logDeriv_apply 展开 → deriv_inv''（倒数链法则）+ 平移导数 = 1，
    field_simp 消 (z-z0)⁻¹。 -/
lemma logDeriv_inv_sub (z0 : ℂ) (z : ℂ) (hz : z ≠ z0) :
    logDeriv (fun s : ℂ => (s - z0)⁻¹) z = -1 / (z - z0) := by
  rw [logDeriv_apply]
  have hc : DifferentiableAt ℂ (fun s : ℂ => s - z0) z :=
    differentiableAt_id.sub (differentiableAt_const (c := z0))
  have hx : (fun s : ℂ => s - z0) z ≠ 0 := sub_ne_zero_of_ne hz
  have hder1 : deriv (fun s : ℂ => s - z0) z = 1 := by
    have h1 := deriv_sub_const (c := z0) (f := fun s : ℂ => s) (x := z)
    simpa using h1
  have hder : deriv (fun s : ℂ => s - z0)⁻¹ z = -1 / (z - z0) ^ 2 := by
    simpa [hder1] using deriv_inv'' hc hx
  change deriv (fun s : ℂ => s - z0)⁻¹ z / (z - z0)⁻¹ = -1 / (z - z0)
  rw [hder]
  field_simp [sub_ne_zero_of_ne hz]

/-- ζ'/ζ 在 s=1 的对数导数分解（定理，真证）：
    存在 G（在 1 解析且 G(1) ≠ 0），在 1 的去心邻域内
      zetaLogDerivative z = -1/(z-1) + logDeriv G z。
    证明：G = Function.update (fun s => (s-1)·ζ(s)) 1 1（在 1 处 = 1）；
    (s-1)ζ(s) 在去心邻域可微且在 1 的极限 = 1（riemannZeta_residue_one，
    continuousAt_update_same），由可去奇点定理
    （analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt）G 在 1 解析。
    ζ = G·(s-1)⁻¹ 两侧对数导数（logDeriv_congr_nhds + logDeriv_mul +
    logDeriv_inv_sub）得 zetaLogDerivative z = logDeriv G z - 1/(z-1)。
    本引理是 :431 围道留数计算中"s=1 极点处留数 = -M[f](1)"的 ζ 侧核心。 -/
lemma zetaLogDerivative_decomposition_at_one :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧ G 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝 1, z ≠ 1 →
        zetaLogDerivative z = (-1 : ℂ) / (z - 1) + logDeriv G z := by
  let H : ℂ → ℂ := fun s => (s - 1) * riemannZeta s
  let G : ℂ → ℂ := Function.update H 1 1
  have hG_diff : ∀ z, z ≠ 1 → DifferentiableAt ℂ G z := by
    intro z hz
    have hζD : DifferentiableAt ℂ riemannZeta z := by
      have hA := analyticOn_riemannZeta z (by simpa using hz)
      exact hA.differentiableAt
    have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) z :=
      differentiableAt_id.sub (differentiableAt_const (c := 1))
    have hHd : DifferentiableAt ℂ H z := by
      change DifferentiableAt ℂ ((fun s : ℂ => s - 1) * riemannZeta) z
      exact h1.mul hζD
    have h_eq : G =ᶠ[𝓝 z] H := by
      refine eventuallyEq_iff_exists_mem.mpr ⟨({1}ᶜ : Set ℂ), ?_, ?_⟩
      · exact (isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds (by
          change z ≠ 1
          exact hz)
      · intro s hs
        have hs1 : s ≠ 1 := by simpa using hs
        simp [G, hs1]
    exact hHd.congr_of_eventuallyEq h_eq
  have hd_G : ∀ᶠ z in 𝓝[≠] 1, DifferentiableAt ℂ G z := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with z hz
    exact hG_diff z (by
      change z ∈ ({1}ᶜ : Set ℂ)
      exact hz)
  have hG_cont : ContinuousAt G 1 := by
    rw [continuousAt_update_same]
    simpa [H] using riemannZeta_residue_one
  have hGA : AnalyticAt ℂ G 1 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd_G hG_cont
  have hG1 : G 1 ≠ 0 := by simp [G]
  have hG_ne : ∀ᶠ z in 𝓝 1, G z ≠ 0 := hGA.continuousAt.eventually_ne hG1
  have hζ_ne : ∀ᶠ z in 𝓝 1, z ≠ 1 → riemannZeta z ≠ 0 := by
    filter_upwards [hG_ne] with z hGz
    intro hz1
    have hGz_eq : G z = (z - 1) * riemannZeta z := by simp [G, hz1, H]
    have hprod : (z - 1) * riemannZeta z ≠ 0 := by simpa [hGz_eq] using hGz
    exact (mul_ne_zero_iff.mp hprod).2
  have h_logζ : ∀ᶠ z in 𝓝 1, z ≠ 1 → zetaLogDerivative z = logDeriv riemannZeta z := by
    filter_upwards [hζ_ne] with z hζz
    intro hz1
    unfold zetaLogDerivative
    rw [if_neg (hζz hz1)]
    rfl
  have h_logcongr : ∀ᶠ z in 𝓝 1, z ≠ 1 →
      logDeriv riemannZeta z = logDeriv (fun s : ℂ => G s * (s - 1)⁻¹) z := by
    filter_upwards with z
    intro hz1
    have h_eq_nhds : riemannZeta =ᶠ[𝓝 z] fun s : ℂ => G s * (s - 1)⁻¹ := by
      refine eventuallyEq_iff_exists_mem.mpr ⟨({1}ᶜ : Set ℂ), ?_, ?_⟩
      · exact (isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds (by
          change z ≠ 1
          exact hz1)
      · intro s hs
        have hs1 : s ≠ 1 := by simpa using hs
        have hGs : G s = (s - 1) * riemannZeta s := by simp [G, hs1, H]
        change riemannZeta s = G s * (s - 1)⁻¹
        rw [hGs]
        field_simp [sub_ne_zero_of_ne hs1]
    rcases Eventually.exists_mem (logDeriv_congr_nhds h_eq_nhds) with ⟨U, hU_nhds, hU_all⟩
    exact hU_all z (mem_of_mem_nhds hU_nhds)
  have h_logmul : ∀ᶠ z in 𝓝 1, z ≠ 1 →
      logDeriv (fun s : ℂ => G s * (s - 1)⁻¹) z =
        logDeriv G z + logDeriv (fun s : ℂ => (s - 1)⁻¹) z := by
    filter_upwards [hG_ne] with z hGz
    intro hz1
    change logDeriv (G * fun s : ℂ => (s - 1)⁻¹) z =
      logDeriv G z + logDeriv (fun s : ℂ => (s - 1)⁻¹) z
    have hg0 : (z - 1)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero_of_ne hz1)
    have hdf : DifferentiableAt ℂ G z := hG_diff z hz1
    have hsubD : DifferentiableAt ℂ (fun s : ℂ => s - 1) z :=
      differentiableAt_id.sub (differentiableAt_const (c := 1))
    have hdg : DifferentiableAt ℂ (fun s : ℂ => (s - 1)⁻¹) z := by
      change DifferentiableAt ℂ ((fun s : ℂ => s - 1)⁻¹) z
      exact hsubD.inv (sub_ne_zero_of_ne hz1)
    exact logDeriv_mul z hGz hg0 hdf hdg
  have h_logpow : ∀ᶠ z in 𝓝 1, z ≠ 1 →
      logDeriv (fun s : ℂ => (s - 1)⁻¹) z = (-1 : ℂ) / (z - 1) := by
    filter_upwards with z
    intro hz1
    exact logDeriv_inv_sub 1 z hz1
  refine ⟨G, hGA, hG1, ?_⟩
  filter_upwards [h_logζ, h_logcongr, h_logmul, h_logpow] with z hL1 hL2 hL3 hL4
  intro hz1
  calc
    zetaLogDerivative z = logDeriv riemannZeta z := hL1 hz1
    _ = logDeriv (fun s : ℂ => G s * (s - 1)⁻¹) z := hL2 hz1
    _ = logDeriv G z + logDeriv (fun s : ℂ => (s - 1)⁻¹) z := hL3 hz1
    _ = logDeriv G z + (-1 : ℂ) / (z - 1) := by rw [hL4 hz1]
    _ = (-1 : ℂ) / (z - 1) + logDeriv G z := by ring

/-- 对数导数的解析性（引理，真证）：G 在 z0 解析且 G z0 ≠ 0 ⟹ logDeriv G 在 z0 解析。
    证明：logDeriv G = deriv G · G⁻¹（logDeriv_apply + div_eq_mul_inv），
    AnalyticAt.deriv + AnalyticAt.inv + AnalyticAt.mul 保持解析性。 -/
lemma logDeriv_analyticAt {G : ℂ → ℂ} {z0 : ℂ} (hGA : AnalyticAt ℂ G z0) (hG0 : G z0 ≠ 0) :
    AnalyticAt ℂ (logDeriv G) z0 := by
  have hGdA : AnalyticAt ℂ (deriv G) z0 := hGA.deriv
  have hGinvA : AnalyticAt ℂ (fun s => (G s)⁻¹) z0 := hGA.inv hG0
  have hprod : AnalyticAt ℂ ((deriv G) * fun s => (G s)⁻¹) z0 := hGdA.mul hGinvA
  exact hprod.congr (Eventually.of_forall (fun s => by
    simp [logDeriv_apply, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]))

/-- 零点 ρ 处的留数分类（定理，真证，M[f] 解析性为显式前提）：
    存在足够小的半径 r（< 1），使小圆留数
      (2πi)⁻¹ ∮_{|s-ρ|=r} (ζ'/ζ·M[f])(s) ds = m(ρ)·M[f](ρ)。
    证明：zetaLogDerivative_decomposition_at_zero 给 ζ'/ζ = m/(s-ρ) + logDeriv G（G 解析、G ρ ≠ 0）；
    h(s) := if s=ρ then m·M[f](ρ) else (s-ρ)·ζ'/ζ(s)·M[f](s) 在 ρ 邻域等于
    (m + (s-ρ)·logDeriv G)·M[f]（全纯，因 logDeriv G 与 M[f] 解析），故 h 在 ρ 解析；
    取 r 小到闭球落在分解邻域与可微邻域内，由 simplePole_residue_local 得留数 = h ρ = m·M[f](ρ)。
    M[f] 解析性（hM）是模型层前提（melinTransform 的全纯性由 Mellin 理论保证，docstring 标注）。 -/
lemma residue_classification_at_zero (f : TestFunction) (ρ : ℂ) (hρ : ρ ∈ contourZeroFinset)
    (hM : AnalyticOnNhd ℂ (melinTransform f) (Metric.ball ρ 1)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (2 * Real.pi * Complex.I)⁻¹ *
        circleIntegral (fun s => zetaLogDerivative s * melinTransform f s) ρ r =
      (zeroMultiplicity ρ : ℂ) * melinTransform f ρ := by
  rcases zetaLogDerivative_decomposition_at_zero ρ hρ with ⟨G, hGA, hG0, hdec⟩
  have hLG : AnalyticAt ℂ (logDeriv G) ρ := logDeriv_analyticAt hGA hG0
  have hMρ : AnalyticAt ℂ (melinTransform f) ρ := hM ρ (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  let F : ℂ → ℂ := fun s => ((zeroMultiplicity ρ : ℂ) + (s - ρ) * logDeriv G s) * melinTransform f s
  let h : ℂ → ℂ := fun s => if s = ρ then (zeroMultiplicity ρ : ℂ) * melinTransform f ρ
    else (s - ρ) * zetaLogDerivative s * melinTransform f s
  have h_eq_nhds : h =ᶠ[𝓝 ρ] F := by
    filter_upwards [hdec] with z hdec'
    by_cases hzρ : z = ρ
    · subst hzρ
      simp [h, F]
    · have hdec'' : zetaLogDerivative z = (zeroMultiplicity ρ : ℂ) / (z - ρ) + logDeriv G z := hdec' hzρ
      simp [h, F, hzρ]
      rw [hdec'']
      field_simp [sub_ne_zero_of_ne hzρ]
      exact Or.inl trivial
  have hF : AnalyticAt ℂ F ρ := by
    have h1 : AnalyticAt ℂ (fun s : ℂ => s - ρ) ρ := analyticAt_id.sub (analyticAt_const (v := ρ))
    have h2 : AnalyticAt ℂ (fun s : ℂ => (s - ρ) * logDeriv G s) ρ := h1.mul hLG
    have h3 : AnalyticAt ℂ (fun s : ℂ => (zeroMultiplicity ρ : ℂ) + (s - ρ) * logDeriv G s) ρ :=
      (analyticAt_const (v := (zeroMultiplicity ρ : ℂ))).add h2
    exact h3.mul hMρ
  have hhA : AnalyticAt ℂ h ρ := hF.congr h_eq_nhds.symm
  rcases hF with ⟨p, hp⟩
  have hFdiff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ F z := hp.eventually_differentiableAt
  rcases Eventually.exists_mem h_eq_nhds with ⟨U, hU, hUall⟩
  rcases Eventually.exists_mem hFdiff with ⟨V, hV, hVall⟩
  rcases (Metric.nhds_basis_closedBall (x := ρ)).mem_iff.1 hU with ⟨R1, hR10, hcl1⟩
  rcases (Metric.nhds_basis_closedBall (x := ρ)).mem_iff.1 hV with ⟨R2, hR20, hcl2⟩
  let r : ℝ := min (min R1 R2) (1 / 2) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (lt_min (lt_min hR10 hR20) (by norm_num)) (by norm_num)
  have hr1 : r < 1 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ 1 / 2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 4 := by norm_num
      _ < 1 := by norm_num
  have hle_rR1 : r ≤ R1 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ min R1 R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left (min R1 R2) (1 / 2)) (by norm_num)
      _ ≤ R1 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left R1 R2) (by norm_num)
      _ ≤ R1 := by linarith [hR10]
  have hle_rR2 : r ≤ R2 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ min R1 R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left (min R1 R2) (1 / 2)) (by norm_num)
      _ ≤ R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_right R1 R2) (by norm_num)
      _ ≤ R2 := by linarith [hR20]
  have hclr1 : Metric.closedBall ρ r ⊆ Metric.closedBall ρ R1 := by
    intro z hz
    exact Metric.mem_closedBall.mpr (by
      have hdz : dist z ρ ≤ r := Metric.mem_closedBall.mp hz
      linarith)
  have hclr2 : Metric.closedBall ρ r ⊆ Metric.closedBall ρ R2 := by
    intro z hz
    exact Metric.mem_closedBall.mpr (by
      have hdz : dist z ρ ≤ r := Metric.mem_closedBall.mp hz
      linarith)
  have hc : ContinuousOn h (Metric.closedBall ρ r) := by
    have hFcont : ContinuousOn F (Metric.closedBall ρ r) := by
      intro z hz
      have hzV : z ∈ V := hcl2 (hclr2 hz)
      exact (hVall z hzV).continuousAt.continuousWithinAt
    refine hFcont.congr ?_
    intro z hz
    exact hUall z (hcl1 (hclr1 hz))
  have hd : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z := by
    intro z hz
    have hzV : z ∈ V := hcl2 (hclr2 (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz))))
    have hFdz : DifferentiableAt ℂ F z := hVall z hzV
    have h_eqz : h =ᶠ[𝓝 z] F := by
      refine eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball ρ r, ?_, ?_⟩
      · exact (Metric.isOpen_ball).mem_nhds hz
      · intro s hs2
        exact hUall s (hcl1 (hclr1 (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hs2)))))
    exact hFdz.congr_of_eventuallyEq h_eqz
  have h_eq : ∀ s ∈ Metric.closedBall ρ r, s ≠ ρ →
      (fun s => zetaLogDerivative s * melinTransform f s) s = h s / (s - ρ) := by
    intro s hs hsρ
    simp [h, hsρ]
    field_simp [sub_ne_zero_of_ne hsρ]
  refine ⟨r, hr, hr1, ?_⟩
  have hmain := simplePole_residue_local (fun s => zetaLogDerivative s * melinTransform f s) h ρ r hr hc hd h_eq
  simpa [h] using hmain

/-- s=1 极点处的留数分类（定理，真证，M[f] 解析性为显式前提）：
    存在足够小的半径 r（< 1），使小圆留数
      (2πi)⁻¹ ∮_{|s-1|=r} (ζ'/ζ·M[f])(s) ds = -M[f](1)。
    证明：zetaLogDerivative_decomposition_at_one 给 ζ'/ζ = -1/(s-1) + logDeriv G（G 在 1 解析、G 1 ≠ 0）；
    h(s) := if s=1 then -M[f](1) else (s-1)·ζ'/ζ(s)·M[f](s) 在 1 邻域等于
    (-1 + (s-1)·logDeriv G)·M[f]（全纯，因 logDeriv G 与 M[f] 解析），故 h 在 1 解析；
    由 simplePole_residue_local 得留数 = h 1 = -M[f](1)。
    M[f] 解析性（hM）是模型层前提（docstring 标注）。 -/
lemma residue_classification_at_one (f : TestFunction)
    (hM : AnalyticOnNhd ℂ (melinTransform f) (Metric.ball 1 1)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (2 * Real.pi * Complex.I)⁻¹ *
        circleIntegral (fun s => zetaLogDerivative s * melinTransform f s) 1 r =
      -melinTransform f 1 := by
  rcases zetaLogDerivative_decomposition_at_one with ⟨G, hGA, hG0, hdec⟩
  have hLG : AnalyticAt ℂ (logDeriv G) 1 := logDeriv_analyticAt hGA hG0
  have hM1 : AnalyticAt ℂ (melinTransform f) 1 := hM 1 (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  let F : ℂ → ℂ := fun s => (-1 + (s - 1) * logDeriv G s) * melinTransform f s
  let h : ℂ → ℂ := fun s => if s = 1 then -melinTransform f 1
    else (s - 1) * zetaLogDerivative s * melinTransform f s
  have h_eq_nhds : h =ᶠ[𝓝 1] F := by
    filter_upwards [hdec] with z hdec'
    by_cases hz1 : z = 1
    · subst hz1
      simp [h, F]
    · have hdec'' : zetaLogDerivative z = (-1 : ℂ) / (z - 1) + logDeriv G z := hdec' hz1
      simp [h, F, hz1]
      rw [hdec'']
      field_simp [sub_ne_zero_of_ne hz1]
      exact Or.inl trivial
  have hF : AnalyticAt ℂ F 1 := by
    have h1 : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 := analyticAt_id.sub (analyticAt_const (v := 1))
    have h2 : AnalyticAt ℂ (fun s : ℂ => (s - 1) * logDeriv G s) 1 := h1.mul hLG
    have h3 : AnalyticAt ℂ (fun s : ℂ => -1 + (s - 1) * logDeriv G s) 1 :=
      (analyticAt_const (v := (-1 : ℂ))).add h2
    exact h3.mul hM1
  have hhA : AnalyticAt ℂ h 1 := hF.congr h_eq_nhds.symm
  rcases hF with ⟨p, hp⟩
  have hFdiff : ∀ᶠ z in 𝓝 1, DifferentiableAt ℂ F z := hp.eventually_differentiableAt
  rcases Eventually.exists_mem h_eq_nhds with ⟨U, hU, hUall⟩
  rcases Eventually.exists_mem hFdiff with ⟨V, hV, hVall⟩
  rcases (Metric.nhds_basis_closedBall (x := 1)).mem_iff.1 hU with ⟨R1, hR10, hcl1⟩
  rcases (Metric.nhds_basis_closedBall (x := 1)).mem_iff.1 hV with ⟨R2, hR20, hcl2⟩
  let r : ℝ := min (min R1 R2) (1 / 2) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (lt_min (lt_min hR10 hR20) (by norm_num)) (by norm_num)
  have hr1 : r < 1 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ 1 / 2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 4 := by norm_num
      _ < 1 := by norm_num
  have hle_rR1 : r ≤ R1 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ min R1 R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left (min R1 R2) (1 / 2)) (by norm_num)
      _ ≤ R1 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left R1 R2) (by norm_num)
      _ ≤ R1 := by linarith [hR10]
  have hle_rR2 : r ≤ R2 := by
    dsimp [r]
    calc
      min (min R1 R2) (1 / 2) / 2 ≤ min R1 R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left (min R1 R2) (1 / 2)) (by norm_num)
      _ ≤ R2 / 2 := by
        exact div_le_div_of_nonneg_right (min_le_right R1 R2) (by norm_num)
      _ ≤ R2 := by linarith [hR20]
  have hclr1 : Metric.closedBall (1 : ℂ) r ⊆ Metric.closedBall (1 : ℂ) R1 := by
    intro z hz
    exact Metric.mem_closedBall.mpr (by
      have hdz : dist z (1 : ℂ) ≤ r := Metric.mem_closedBall.mp hz
      linarith)
  have hclr2 : Metric.closedBall (1 : ℂ) r ⊆ Metric.closedBall (1 : ℂ) R2 := by
    intro z hz
    exact Metric.mem_closedBall.mpr (by
      have hdz : dist z (1 : ℂ) ≤ r := Metric.mem_closedBall.mp hz
      linarith)
  have hc : ContinuousOn h (Metric.closedBall (1 : ℂ) r) := by
    have hFcont : ContinuousOn F (Metric.closedBall (1 : ℂ) r) := by
      intro z hz
      have hzV : z ∈ V := hcl2 (hclr2 hz)
      exact (hVall z hzV).continuousAt.continuousWithinAt
    refine hFcont.congr ?_
    intro z hz
    exact hUall z (hcl1 (hclr1 hz))
  have hd : ∀ z ∈ Metric.ball (1 : ℂ) r, DifferentiableAt ℂ h z := by
    intro z hz
    have hzV : z ∈ V := hcl2 (hclr2 (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz))))
    have hFdz : DifferentiableAt ℂ F z := hVall z hzV
    have h_eqz : h =ᶠ[𝓝 z] F := by
      refine eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball (1 : ℂ) r, ?_, ?_⟩
      · exact (Metric.isOpen_ball).mem_nhds hz
      · intro s hs2
        exact hUall s (hcl1 (hclr1 (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hs2)))))
    exact hFdz.congr_of_eventuallyEq h_eqz
  have h_eq : ∀ s ∈ Metric.closedBall (1 : ℂ) r, s ≠ 1 →
      (fun s => zetaLogDerivative s * melinTransform f s) s = h s / (s - 1) := by
    intro s hs hs1
    simp [h, hs1]
    field_simp [sub_ne_zero_of_ne hs1]
  refine ⟨r, hr, hr1, ?_⟩
  have hmain := simplePole_residue_local (fun s => zetaLogDerivative s * melinTransform f s) h 1 r hr hc hd h_eq
  simpa [h] using hmain

/-- ζ'/ζ · M[f] 的围道积分等于留数求和（定理，一般留数定理在 ζ 上的应用）：
    围道积分 = 围道内所有奇点的留数之和：
      contourIntegral(ζ'/ζ · M[f]) = Σ_{ρ ∈ 围道内} m(ρ)·M[f](ρ) + (-1)·M[f](1)
    其中非平凡零点处留数 = m(ρ)·M[f](ρ)（对数导数在 m 阶零点处留数为 m，全纯因子 M[f] 可提出），
    s=1 极点处留数 = -M[f](1)（ζ 在 s=1 为一阶极点，对数导数留数为 -1）。
    这是一般留数定理（residue_theorem_general）+ 留数乘积公式 + ζ 具体留数计算的综合结果。
    围道 |s−1/2| = 1 只含 |ρ−1/2| < 1 的零点（有限，contourZeroFinset）；围道外零点
    贡献由 farZeroContribution 表示，故等式右端写为 zetaZeroSide - farZeroContribution
    （zetaZeroSide = 围道内 + 围道外 + s=1 项，减去围道外即围道内留数和）。
    平凡零点（负偶数）在围道外，无贡献（围道外约定）。

    模型层显式前提（2026-10-01，待磨光层落实）：
      hM              : M[f] 在围道闭盘 |s−1/2| ≤ 1 解析（测试函数 Mellin 变换的解析性）。
      h_no_boundary_zeros : 围道球面 |s−1/2| = 1 上 ζ 无零点（围道不经过零点）。
      h_zero_in_S     : 围道闭盘内 ζ 的零点都是 contourZeroFinset 的成员或 s=1
                        （数学事实：临界带内零点 + 平凡零点不在围道闭盘）。 -/
lemma zeta_log_derivative_contour_eq_residue_sum (f : TestFunction)
    (hM : AnalyticOnNhd ℂ (melinTransform f) (Metric.closedBall (1 / 2 : ℂ) contourRadius))
    (h_no_boundary_zeros : ∀ z, z ∈ Metric.sphere (1 / 2 : ℂ) contourRadius →
      _root_.riemannZeta z ≠ 0)
    (h_zero_in_S : ∀ z, z ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius →
      _root_.riemannZeta z = 0 → z ∈ contourZeroFinset ∨ z = 1) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) =
    zetaZeroSide f - farZeroContribution f := by
  classical
  let g : ℂ → ℂ := fun s => zetaLogDerivative s * melinTransform f s
  let S : Finset ℂ := insert 1 contourZeroFinset
  -- 分解数据（s=1 与各零点）
  rcases zetaLogDerivative_decomposition_at_one with ⟨G1, hG1A, hG10, hG1dec⟩
  have hG1_ball : ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Metric.ball (1 : ℂ) r, AnalyticAt ℂ G1 s :=
    analyticAt_finite_ball hG1A
  rcases hG1_ball with ⟨r1, hr1_pos, hr1_an⟩
  have hdec_all : ∀ ρ : ℂ, (hρ : ρ ∈ contourZeroFinset) → ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G ρ ∧ G ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, z ≠ ρ → zetaLogDerivative z = (zeroMultiplicity ρ : ℂ) / (z - ρ) + logDeriv G z :=
    fun ρ hρ => zetaLogDerivative_decomposition_at_zero ρ hρ
  choose Gρ hGρA hGρ0 hGρdec using hdec_all
  have hGρ_ball : ∀ ρ : ℂ, (hρ : ρ ∈ contourZeroFinset) → ∃ r : ℝ, 0 < r ∧
      ∀ s ∈ Metric.ball ρ r, AnalyticAt ℂ (Gρ ρ hρ) s :=
    fun ρ hρ => analyticAt_finite_ball (hGρA ρ hρ)
  choose rρ hrρ_pos hrρ_an using hGρ_ball
  -- 分解恒等式球（h_eq 化简用）
  have hdec_ball_one : ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Metric.ball (1 : ℂ) r, s ≠ 1 →
      zetaLogDerivative s = -1 / (s - 1) + logDeriv G1 s := by
    rcases Eventually.exists_mem hG1dec with ⟨U, hU, hUall⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨r, hr0, hball⟩
    refine ⟨r, hr0, ?_⟩
    intro s hs hs1
    exact hUall s (hball hs) hs1
  rcases hdec_ball_one with ⟨r_dec1, hr_dec1_pos, hr_dec1_eq⟩
  have hdec_ball_all : ∀ ρ : ℂ, (hρ : ρ ∈ contourZeroFinset) → ∃ r : ℝ, 0 < r ∧
      ∀ s ∈ Metric.ball ρ r, s ≠ ρ →
      zetaLogDerivative s = (zeroMultiplicity ρ : ℂ) / (s - ρ) + logDeriv (Gρ ρ hρ) s := by
    intro ρ hρ
    rcases Eventually.exists_mem (hGρdec ρ hρ) with ⟨U, hU, hUall⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨r, hr0, hball⟩
    refine ⟨r, hr0, ?_⟩
    intro s hs hs1
    exact hUall s (hball hs) hs1
  choose r_decρ hr_decρ_pos hr_decρ_eq using hdec_ball_all
  -- 非零邻域球
  have hG1_nz : ∃ δ > 0, ∀ s ∈ Metric.ball (1 : ℂ) δ, G1 s ≠ 0 := by
    have hc : ContinuousAt G1 (1 : ℂ) := hG1A.continuousAt
    have hne : ∀ᶠ s in 𝓝 (1 : ℂ), G1 s ≠ 0 := hc.eventually_ne hG10
    rcases Eventually.exists_mem hne with ⟨U, hU, hUall⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ0, hball⟩
    refine ⟨δ, hδ0, ?_⟩
    intro s hs
    exact hUall s (hball hs)
  rcases hG1_nz with ⟨δG1, hδG1_pos, hδG1_nz⟩
  have hGρ_nz_all : ∀ ρ : ℂ, (hρ : ρ ∈ contourZeroFinset) → ∃ δ > 0,
      ∀ s ∈ Metric.ball ρ δ, Gρ ρ hρ s ≠ 0 := by
    intro ρ hρ
    have hc : ContinuousAt (Gρ ρ hρ) ρ := (hGρA ρ hρ).continuousAt
    have hne : ∀ᶠ s in 𝓝 ρ, Gρ ρ hρ s ≠ 0 := hc.eventually_ne (hGρ0 ρ hρ)
    rcases Eventually.exists_mem hne with ⟨U, hU, hUall⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ0, hball⟩
    refine ⟨δ, hδ0, ?_⟩
    intro s hs
    exact hUall s (hball hs)
  choose δGρ hδGρ_pos hδGρ_nz using hGρ_nz_all
  -- 小圆互斥（分离）
  have hsep_all : ∀ z0 : ℂ, (hz0S : z0 ∈ S) → ∃ δ > 0,
      ∀ z ∈ Metric.ball z0 δ, z ∈ S → z = z0 := by
    intro z0 hz0S
    have hcl : IsClosed (((S.erase z0 : Finset ℂ) : Set ℂ)) := by
      exact Finset.isClosed (S.erase z0)
    have hnot : z0 ∉ (S.erase z0 : Finset ℂ) := by simp
    have hz0c : z0 ∈ ((S.erase z0 : Finset ℂ)ᶜ : Set ℂ) := by simp [hnot]
    have hopen : IsOpen (((S.erase z0 : Finset ℂ) : Set ℂ)ᶜ) := hcl.isOpen_compl
    rcases Metric.mem_nhds_iff.mp (hopen.mem_nhds hz0c) with ⟨δ, hδ0, hball⟩
    refine ⟨δ, hδ0, ?_⟩
    intro z hz hzS
    by_contra hne
    have hz_er : z ∈ (S.erase z0 : Finset ℂ) := Finset.mem_erase.mpr ⟨hne, hzS⟩
    exact hball hz hz_er
  choose δρ hδρ_pos hδρ_sep using hsep_all
  -- ε 构造（每点取解析球 / 非零球 / 分解球 / 分离球 / 主围道内距 的最小值之半）
  let ε : ℂ → ℝ := fun z0 =>
    if hz0_1 : z0 = 1 then
      (min (min (min (min r1 1) (1 - dist z0 (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ z0 (Finset.mem_insert.mpr (Or.inl hz0_1)))) / 2
    else if hz0S : z0 ∈ contourZeroFinset then
      (min (min (min (min (rρ z0 hz0S) 1) (1 - dist z0 (1 / 2 : ℂ)))
        (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0S))) (δGρ z0 hz0S)))
        (r_decρ z0 hz0S)) / 2
    else 1
  -- h_eps：正性 / <1 / 小球 ⊆ 主围道 / 小圆内唯一
  have h_eps : ∀ z0 ∈ S, 0 < ε z0 ∧ ε z0 < 1 ∧
      Metric.ball z0 (ε z0) ⊆ Metric.ball (1 / 2 : ℂ) contourRadius ∧
      ∀ z ∈ Metric.ball z0 (ε z0), z ∈ S → z = z0 := by
    intro z0 hz0S
    rcases (Finset.mem_insert.mp hz0S) with hz0_1 | hz0_cz
    · subst z0
      have hε1_def : ε (1 : ℂ) = (min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))) / 2 := by
        simp [ε]
      have hd12 : dist (1 : ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [dist_eq_norm]
      have hmin_pos : 0 < min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) := by
        exact lt_min
          (lt_min (lt_min (lt_min hr1_pos (by norm_num)) (by linarith)) (lt_min hδG1_pos hr_dec1_pos))
          (hδρ_pos (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))
      have hε1_pos : 0 < ε (1 : ℂ) := by
        rw [hε1_def]
        positivity
      have hε1_lt1 : ε (1 : ℂ) < 1 := by
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ 1 := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
        linarith [hle, hmin_pos]
      have hε1_lt_dist : ε (1 : ℂ) < 1 - dist (1 : ℂ) (1 / 2 : ℂ) := by
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ 1 - dist (1 : ℂ) (1 / 2 : ℂ) := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
        linarith [hle, hmin_pos, hd12]
      have hε1_ltδ1 : ε (1 : ℂ) < δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)) := by
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)) := by
          exact min_le_right _ _
        linarith [hle, hmin_pos]
      refine ⟨hε1_pos, hε1_lt1, ?_, ?_⟩
      · intro s hs
        rw [Metric.mem_ball]
        have hds : dist s (1 : ℂ) < ε (1 : ℂ) := Metric.mem_ball.mp hs
        have hεh : ε (1 : ℂ) + dist (1 : ℂ) (1 / 2 : ℂ) < 1 := by
          linarith [hε1_lt_dist, hd12]
        have hlt : dist s (1 : ℂ) + dist (1 : ℂ) (1 / 2 : ℂ) < 1 := by
          linarith [hds, hεh]
        exact lt_of_le_of_lt (dist_triangle s (1 : ℂ) (1 / 2 : ℂ)) hlt
      · intro z hz hzS
        exact hδρ_sep (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)) z
          (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) hε1_ltδ1.le)) hzS
    · -- 零点分支
      have hz0_ne1 : z0 ≠ 1 := by
        intro h
        have hre : z0.re < 1 := (contourZeroFinset_mem z0).mp hz0_cz |>.2.2.1
        rw [h] at hre
        norm_num at hre
      have hε_def : ε z0 = (min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
          (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
          (r_decρ z0 hz0_cz)) / 2 := by
        simp [ε, hz0_ne1, hz0_cz]
      have hd0 : dist z0 (1 / 2 : ℂ) < 1 := by
        have hd : ‖z0 - (1 / 2 : ℂ)‖ < contourRadius := (contourZeroFinset_mem z0).mp hz0_cz |>.2.2.2
        simpa [dist_eq_norm, contourRadius] using hd
      have hmin_pos : 0 < min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
          (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
          (r_decρ z0 hz0_cz) := by
        exact lt_min
          (lt_min (lt_min (lt_min (hrρ_pos z0 hz0_cz) (by norm_num)) (by linarith))
            (lt_min (hδρ_pos z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (hδGρ_pos z0 hz0_cz)))
          (hr_decρ_pos z0 hz0_cz)
      have hε_pos : 0 < ε z0 := by
        rw [hε_def]
        positivity
      have hε_lt1 : ε z0 < 1 := by
        rw [hε_def]
        have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz) ≤ 1 := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
        linarith [hle, hmin_pos]
      have hε_lt_dist : ε z0 < 1 - dist z0 (1 / 2 : ℂ) := by
        rw [hε_def]
        have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz) ≤ 1 - dist z0 (1 / 2 : ℂ) := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
        linarith [hle, hmin_pos, hd0]
      refine ⟨hε_pos, hε_lt1, ?_, ?_⟩
      · intro s hs
        rw [Metric.mem_ball]
        have hds : dist s z0 < ε z0 := Metric.mem_ball.mp hs
        have hεh : ε z0 + dist z0 (1 / 2 : ℂ) < 1 := by
          linarith [hε_lt_dist, hd0]
        have hlt : dist s z0 + dist z0 (1 / 2 : ℂ) < 1 := by
          linarith [hds, hεh]
        exact lt_of_le_of_lt (dist_triangle s z0 (1 / 2 : ℂ)) hlt
      · intro z hz hzS
        have hε_ltδ : ε z0 < δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz)) := by
          rw [hε_def]
          have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
              (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
              (r_decρ z0 hz0_cz) ≤ δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz)) := by
            exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
          linarith
        exact hδρ_sep z0 (Finset.mem_insert.mpr (Or.inr hz0_cz)) z
          (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) hε_ltδ.le)) hzS
  -- h_pole：小圆局部单值化
  have h_pole : ∀ z0 ∈ S, ∃ h : ℂ → ℂ,
      ContinuousOn h (Metric.closedBall z0 (ε z0)) ∧
      (∀ s ∈ Metric.ball z0 (ε z0), DifferentiableAt ℂ h s) ∧
      ∀ s ∈ Metric.closedBall z0 (ε z0), s ≠ z0 → g s = h s / (s - z0) := by
    intro z0 hz0S
    rcases (Finset.mem_insert.mp hz0S) with hz0_1 | hz0_cz
    · subst z0
      let h1 : ℂ → ℂ := fun s => (-1 + (s - 1) * logDeriv G1 s) * melinTransform f s
      have hd12 : dist (1 : ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [dist_eq_norm]
      have hmin1_pos : 0 < min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) := by
        exact lt_min
          (lt_min (lt_min (lt_min hr1_pos (by norm_num)) (by linarith [hd12])) (lt_min hδG1_pos hr_dec1_pos))
          (hδρ_pos (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))
      have hε1_lt_r1 : ε (1 : ℂ) < r1 := by
        have hε1_def : ε (1 : ℂ) = (min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))) / 2 := by
          simp [ε]
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ r1 := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
        linarith [hle, hmin1_pos]
      have hε1_lt_dG1 : ε (1 : ℂ) < δG1 := by
        have hε1_def : ε (1 : ℂ) = (min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))) / 2 := by
          simp [ε]
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ min δG1 r_dec1 := by
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        have hle2 : min δG1 r_dec1 ≤ δG1 := min_le_left _ _
        linarith [hle, hle2, hmin1_pos]
      have hε1_lt_dec1 : ε (1 : ℂ) < r_dec1 := by
        have hε1_def : ε (1 : ℂ) = (min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))) / 2 := by
          simp [ε]
        rw [hε1_def]
        have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ min δG1 r_dec1 := by
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        have hle2 : min δG1 r_dec1 ≤ r_dec1 := min_le_right _ _
        linarith [hle, hle2, hmin1_pos]
      have hs_cb : ∀ s ∈ Metric.closedBall (1 : ℂ) (ε 1), s ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius := by
        intro s hs
        rw [Metric.mem_closedBall]
        have hd1 : dist s (1 : ℂ) ≤ ε (1 : ℂ) := Metric.mem_closedBall.mp hs
        have hεh : ε (1 : ℂ) < 1 / 2 := by
          have hε_def : ε (1 : ℂ) = (min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl)))) / 2 := by
            simp [ε]
          rw [hε_def]
          have hle : min (min (min (min r1 1) (1 - dist (1 : ℂ) (1 / 2 : ℂ))) (min δG1 r_dec1)) (δρ (1 : ℂ) (Finset.mem_insert.mpr (Or.inl rfl))) ≤ 1 - dist (1 : ℂ) (1 / 2 : ℂ) := by
            exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
          linarith [hle, hmin1_pos, hd12]
        have hεh2 : ε (1 : ℂ) + dist (1 : ℂ) (1 / 2 : ℂ) < 1 := by
          linarith [hεh, hd12]
        have hlt : dist s (1 : ℂ) + dist (1 : ℂ) (1 / 2 : ℂ) < 1 := by
          linarith [hd1, hεh2]
        exact le_trans (dist_triangle s (1 : ℂ) (1 / 2 : ℂ)) (le_of_lt hlt)
      refine ⟨h1, ?_, ?_, ?_⟩
      · intro s hs
        have hs_r1 : s ∈ Metric.ball (1 : ℂ) r1 := by
          rw [Metric.mem_ball]
          have hd1 : dist s (1 : ℂ) ≤ ε (1 : ℂ) := Metric.mem_closedBall.mp hs
          linarith [hd1, hε1_lt_r1]
        have hG1an : AnalyticAt ℂ G1 s := hr1_an s hs_r1
        have hs_dG1 : s ∈ Metric.ball (1 : ℂ) δG1 := by
          rw [Metric.mem_ball]
          have hd1 : dist s (1 : ℂ) ≤ ε (1 : ℂ) := Metric.mem_closedBall.mp hs
          linarith [hd1, hε1_lt_dG1]
        have hG1nz : G1 s ≠ 0 := hδG1_nz s hs_dG1
        have hLG1c : ContinuousAt (logDeriv G1) s := (logDeriv_analyticAt hG1an hG1nz).continuousAt
        have hMfc : ContinuousAt (melinTransform f) s := (hM s (hs_cb s hs)).continuousAt
        have h1c : ContinuousAt (fun _ : ℂ => (-1 : ℂ)) s := continuousAt_const
        have hidc : ContinuousAt (fun x : ℂ => x) s := continuousAt_id
        have h1c' : ContinuousAt (fun _ : ℂ => (1 : ℂ)) s := continuousAt_const
        have hsubc : ContinuousAt (fun x : ℂ => x - 1) s := hidc.sub h1c'
        have hmulc : ContinuousAt (fun x : ℂ => (x - 1) * logDeriv G1 x) s := hsubc.mul hLG1c
        have hsumc : ContinuousAt (fun x : ℂ => (-1 + (x - 1) * logDeriv G1 x)) s := h1c.add hmulc
        have hprod : ContinuousWithinAt h1 (Metric.closedBall (1 : ℂ) (ε 1)) s :=
          (hsumc.mul hMfc).continuousWithinAt
        simpa [h1] using hprod
      · intro s hs
        have hs_r1 : s ∈ Metric.ball (1 : ℂ) r1 := by
          rw [Metric.mem_ball]
          have hd1 : dist s (1 : ℂ) < ε (1 : ℂ) := Metric.mem_ball.mp hs
          linarith [hd1, hε1_lt_r1]
        have hG1an : AnalyticAt ℂ G1 s := hr1_an s hs_r1
        have hs_dG1 : s ∈ Metric.ball (1 : ℂ) δG1 := by
          rw [Metric.mem_ball]
          have hd1 : dist s (1 : ℂ) < ε (1 : ℂ) := Metric.mem_ball.mp hs
          linarith [hd1, hε1_lt_dG1]
        have hG1nz : G1 s ≠ 0 := hδG1_nz s hs_dG1
        have hLG1an : AnalyticAt ℂ (logDeriv G1) s := logDeriv_analyticAt hG1an hG1nz
        have hMfan : AnalyticAt ℂ (melinTransform f) s := hM s (hs_cb s (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hs))))
        exact (((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hLG1an)).mul hMfan).differentiableAt)
      · intro s hs hs1
        have hs_dec : s ∈ Metric.ball (1 : ℂ) r_dec1 := by
          rw [Metric.mem_ball]
          have hd1 : dist s (1 : ℂ) ≤ ε (1 : ℂ) := Metric.mem_closedBall.mp hs
          linarith [hd1, hε1_lt_dec1]
        have hdec : zetaLogDerivative s = -1 / (s - 1) + logDeriv G1 s := hr_dec1_eq s hs_dec hs1
        simp [g, h1, hdec]
        field_simp [sub_ne_zero_of_ne hs1]
    · -- 零点分支
      have hz0_ne1 : z0 ≠ 1 := by
        intro h
        have hre : z0.re < 1 := (contourZeroFinset_mem z0).mp hz0_cz |>.2.2.1
        rw [h] at hre
        norm_num at hre
      let hρ : ℂ → ℂ := fun s => ((zeroMultiplicity z0 : ℂ) + (s - z0) * logDeriv (Gρ z0 hz0_cz) s) * melinTransform f s
      have hd0 : dist z0 (1 / 2 : ℂ) < contourRadius := by
        have hd : ‖z0 - (1 / 2 : ℂ)‖ < contourRadius := (contourZeroFinset_mem z0).mp hz0_cz |>.2.2.2
        simpa [dist_eq_norm, contourRadius] using hd
      have hmin0_pos : 0 < min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
          (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
          (r_decρ z0 hz0_cz) := by
        exact lt_min
          (lt_min (lt_min (lt_min (hrρ_pos z0 hz0_cz) (by norm_num)) (by simpa [contourRadius] using hd0))
            (lt_min (hδρ_pos z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (hδGρ_pos z0 hz0_cz)))
          (hr_decρ_pos z0 hz0_cz)
      have hε_lt_rρ : ε z0 < rρ z0 hz0_cz := by
        have hε_def : ε z0 = (min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz)) / 2 := by
          simp [ε, hz0_ne1, hz0_cz]
        rw [hε_def]
        have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz) ≤ rρ z0 hz0_cz := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
        linarith [hle, hmin0_pos]
      have hε_lt_dGρ : ε z0 < δGρ z0 hz0_cz := by
        have hε_def : ε z0 = (min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz)) / 2 := by
          simp [ε, hz0_ne1, hz0_cz]
        rw [hε_def]
        have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz) ≤ δGρ z0 hz0_cz := by
          exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
        linarith [hle, hmin0_pos]
      have hε_lt_decρ : ε z0 < r_decρ z0 hz0_cz := by
        have hε_def : ε z0 = (min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz)) / 2 := by
          simp [ε, hz0_ne1, hz0_cz]
        rw [hε_def]
        have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
            (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
            (r_decρ z0 hz0_cz) ≤ r_decρ z0 hz0_cz := min_le_right _ _
        linarith [hle, hmin0_pos]
      have hs_cb : ∀ s ∈ Metric.closedBall z0 (ε z0), s ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius := by
        intro s hs
        rw [Metric.mem_closedBall]
        have hd1 : dist s z0 ≤ ε z0 := Metric.mem_closedBall.mp hs
        have hεd : ε z0 < 1 - dist z0 (1 / 2 : ℂ) := by
          have hε_def : ε z0 = (min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
              (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
              (r_decρ z0 hz0_cz)) / 2 := by
            simp [ε, hz0_ne1, hz0_cz]
          rw [hε_def]
          have hle : min (min (min (min (rρ z0 hz0_cz) 1) (1 - dist z0 (1 / 2 : ℂ)))
              (min (δρ z0 (Finset.mem_insert.mpr (Or.inr hz0_cz))) (δGρ z0 hz0_cz)))
              (r_decρ z0 hz0_cz) ≤ 1 - dist z0 (1 / 2 : ℂ) := by
            exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
          linarith [hle, hmin0_pos, hd0]
        have hεh2 : ε z0 + dist z0 (1 / 2 : ℂ) < 1 := by
          linarith [hεd, hd0]
        have hlt : dist s z0 + dist z0 (1 / 2 : ℂ) < 1 := by
          linarith [hd1, hεh2]
        exact le_trans (dist_triangle s z0 (1 / 2 : ℂ)) (le_of_lt hlt)
      refine ⟨hρ, ?_, ?_, ?_⟩
      · intro s hs
        have hs_r : s ∈ Metric.ball z0 (rρ z0 hz0_cz) := by
          rw [Metric.mem_ball]
          have hd1 : dist s z0 ≤ ε z0 := Metric.mem_closedBall.mp hs
          linarith [hd1, hε_lt_rρ]
        have hGan : AnalyticAt ℂ (Gρ z0 hz0_cz) s := hrρ_an z0 hz0_cz s hs_r
        have hs_dG : s ∈ Metric.ball z0 (δGρ z0 hz0_cz) := by
          rw [Metric.mem_ball]
          have hd1 : dist s z0 ≤ ε z0 := Metric.mem_closedBall.mp hs
          linarith [hd1, hε_lt_dGρ]
        have hGnz : Gρ z0 hz0_cz s ≠ 0 := hδGρ_nz z0 hz0_cz s hs_dG
        have hLGc : ContinuousAt (logDeriv (Gρ z0 hz0_cz)) s := (logDeriv_analyticAt hGan hGnz).continuousAt
        have hMfc : ContinuousAt (melinTransform f) s := (hM s (hs_cb s hs)).continuousAt
        have h1c : ContinuousAt (fun _ : ℂ => (zeroMultiplicity z0 : ℂ)) s := continuousAt_const
        have hidc : ContinuousAt (fun x : ℂ => x) s := continuousAt_id
        have hz0c : ContinuousAt (fun _ : ℂ => z0) s := continuousAt_const
        have hsubc : ContinuousAt (fun x : ℂ => x - z0) s := hidc.sub hz0c
        have hmulc : ContinuousAt (fun x : ℂ => (x - z0) * logDeriv (Gρ z0 hz0_cz) x) s := hsubc.mul hLGc
        have hsumc : ContinuousAt (fun x : ℂ => ((zeroMultiplicity z0 : ℂ) + (x - z0) * logDeriv (Gρ z0 hz0_cz) x)) s := h1c.add hmulc
        have hprod : ContinuousWithinAt hρ (Metric.closedBall z0 (ε z0)) s :=
          (hsumc.mul hMfc).continuousWithinAt
        simpa [hρ] using hprod
      · intro s hs
        have hs_r : s ∈ Metric.ball z0 (rρ z0 hz0_cz) := by
          rw [Metric.mem_ball]
          have hd1 : dist s z0 < ε z0 := Metric.mem_ball.mp hs
          linarith [hd1, hε_lt_rρ]
        have hGan : AnalyticAt ℂ (Gρ z0 hz0_cz) s := hrρ_an z0 hz0_cz s hs_r
        have hs_dG : s ∈ Metric.ball z0 (δGρ z0 hz0_cz) := by
          rw [Metric.mem_ball]
          have hd1 : dist s z0 < ε z0 := Metric.mem_ball.mp hs
          linarith [hd1, hε_lt_dGρ]
        have hGnz : Gρ z0 hz0_cz s ≠ 0 := hδGρ_nz z0 hz0_cz s hs_dG
        have hLGan : AnalyticAt ℂ (logDeriv (Gρ z0 hz0_cz)) s := logDeriv_analyticAt hGan hGnz
        have hMfan : AnalyticAt ℂ (melinTransform f) s := hM s (hs_cb s (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hs))))
        exact (((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hLGan)).mul hMfan).differentiableAt)
      · intro s hs hs1
        have hs_dec : s ∈ Metric.ball z0 (r_decρ z0 hz0_cz) := by
          rw [Metric.mem_ball]
          have hd1 : dist s z0 ≤ ε z0 := Metric.mem_closedBall.mp hs
          linarith [hd1, hε_lt_decρ]
        have hdec : zetaLogDerivative s = (zeroMultiplicity z0 : ℂ) / (s - z0) + logDeriv (Gρ z0 hz0_cz) s :=
          hr_decρ_eq z0 hz0_cz s hs_dec hs1
        simp [g, hρ, hdec]
        field_simp [sub_ne_zero_of_ne hs1]
  -- 围道球面不经过奇点（h_diff_off 前提）
  have h_sub : ∀ z0 ∈ S, z0 ∈ Metric.ball (1 / 2 : ℂ) contourRadius := by
    intro z0 hz0S
    rcases (Finset.mem_insert.mp hz0S) with hz0_1 | hz0_cz
    · subst z0
      rw [Metric.mem_ball]
      norm_num [dist_eq_norm, contourRadius]
    · rw [Metric.mem_ball]
      have hd : ‖z0 - (1 / 2 : ℂ)‖ < contourRadius := (contourZeroFinset_mem z0).mp hz0_cz |>.2.2.2
      simpa [dist_eq_norm, contourRadius] using hd
  -- 围道闭盘内除奇点外可微（ζ 解析 + M[f] 解析）
  have h_diff_off : ∀ z ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius \ (S : Set ℂ),
      DifferentiableAt ℂ g z := by
    intro z hz
    have hzS : z ∉ S := hz.2
    have hz_ne1 : z ≠ 1 := by intro h; apply hzS; simp [S, h]
    have hz_zeta_ne : riemannZeta z ≠ 0 := by
      intro hz0
      have hzS' : z ∈ S := by
        rcases h_zero_in_S z hz.1 hz0 with hz_cz | hz_eq1
        · exact Finset.mem_insert.mpr (Or.inr hz_cz)
        · exact Finset.mem_insert.mpr (Or.inl hz_eq1)
      exact hzS hzS'
    have hlogdiff : DifferentiableAt ℂ zetaLogDerivative z := by
      unfold zetaLogDerivative
      have hζan : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz_ne1
      have hζderiv : DifferentiableAt ℂ (fun s : ℂ => deriv riemannZeta s / riemannZeta s) z :=
        hζan.deriv.differentiableAt.div hζan.differentiableAt hz_zeta_ne
      have hcongr : (fun s : ℂ => if riemannZeta s = 0 then 0 else deriv riemannZeta s / riemannZeta s) =ᶠ[𝓝 z]
          (fun s : ℂ => deriv riemannZeta s / riemannZeta s) := by
        filter_upwards [hζan.continuousAt.eventually_ne (y := (0 : ℂ)) hz_zeta_ne]
        intro s hs
        simp [hs]
      exact hζderiv.congr_of_eventuallyEq hcongr
    have hMdz : DifferentiableAt ℂ (melinTransform f) z := (hM z hz.1).differentiableAt
    exact hlogdiff.mul hMdz
  -- 留数 = 小圆积分求和 → 分类值
  have h_sum : (∑ z0 ∈ S, (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 (ε z0)) =
      (∑ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ)
      + (-1 : ℂ) * melinTransform f (1 : ℂ) := by
    have h1_not : (1 : ℂ) ∉ contourZeroFinset := by
      intro h1
      have hre : (1 : ℂ).re < 1 := (contourZeroFinset_mem (1 : ℂ)).mp h1 |>.2.2.1
      norm_num at hre
    dsimp [S]
    rw [Finset.sum_insert h1_not]
    -- 零点项（sum_congr）
    have hz_sum : (∑ ρ ∈ contourZeroFinset, (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g ρ (ε ρ)) =
        (∑ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ) := by
      refine Finset.sum_congr rfl ?_
      intro ρ hρ
      rcases h_pole ρ (Finset.mem_insert.mpr (Or.inr hρ)) with ⟨hw, hwc, hwd, hweq⟩
      have hres := simplePole_residue_local g hw ρ (ε ρ) (h_eps ρ (Finset.mem_insert.mpr (Or.inr hρ))).1 hwc hwd hweq
      have hh : hw ρ = (zeroMultiplicity ρ : ℂ) * melinTransform f ρ := by
        have hF1c : ContinuousAt (fun s => ((zeroMultiplicity ρ : ℂ) + (s - ρ) * logDeriv (Gρ ρ hρ) s) * melinTransform f s) ρ := by
          have hGan1 : AnalyticAt ℂ (Gρ ρ hρ) ρ := hrρ_an ρ hρ ρ (Metric.mem_ball.mpr (by simp [hrρ_pos ρ hρ]))
          have hGnz1 : Gρ ρ hρ ρ ≠ 0 := hδGρ_nz ρ hρ ρ (Metric.mem_ball.mpr (by simp [hδGρ_pos ρ hρ]))
          have hLGc1 : ContinuousAt (logDeriv (Gρ ρ hρ)) ρ := (logDeriv_analyticAt hGan1 hGnz1).continuousAt
          have hMf1c : ContinuousAt (melinTransform f) ρ := (hM ρ (Metric.mem_closedBall.mpr (by
            have hd : ‖ρ - (1 / 2 : ℂ)‖ < contourRadius := (contourZeroFinset_mem ρ).mp hρ |>.2.2.2
            exact le_of_lt (by simpa [dist_eq_norm, contourRadius] using hd)))).continuousAt
          have h1c : ContinuousAt (fun _ : ℂ => (zeroMultiplicity ρ : ℂ)) ρ := continuousAt_const
          have hidc : ContinuousAt (fun x : ℂ => x) ρ := continuousAt_id
          have hρc : ContinuousAt (fun _ : ℂ => ρ) ρ := continuousAt_const
          have hsubc : ContinuousAt (fun x : ℂ => x - ρ) ρ := hidc.sub hρc
          have hmulc : ContinuousAt (fun x : ℂ => (x - ρ) * logDeriv (Gρ ρ hρ) x) ρ := hsubc.mul hLGc1
          have hsumc : ContinuousAt (fun x : ℂ => ((zeroMultiplicity ρ : ℂ) + (x - ρ) * logDeriv (Gρ ρ hρ) x)) ρ := h1c.add hmulc
          exact hsumc.mul hMf1c
        have heqF : ∀ᶠ s in 𝓝[≠] ρ, hw s = ((zeroMultiplicity ρ : ℂ) + (s - ρ) * logDeriv (Gρ ρ hρ) s) * melinTransform f s := by
          have h1 : ∀ᶠ s in 𝓝[≠] ρ, hw s = g s * (s - ρ) := by
            have hεb : Metric.ball ρ (ε ρ) ∈ 𝓝 ρ := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by simp [(h_eps ρ (Finset.mem_insert.mpr (Or.inr hρ))).1]))
            have hεb' : ∀ᶠ s in 𝓝[≠] ρ, s ∈ Metric.ball ρ (ε ρ) := Filter.Eventually.filter_mono nhdsWithin_le_nhds hεb
            filter_upwards [self_mem_nhdsWithin, hεb']
            intro s hs_ne hs_ball
            have hs_cl : s ∈ Metric.closedBall ρ (ε ρ) := Metric.ball_subset_closedBall hs_ball
            have hge : g s = hw s / (s - ρ) := hweq s hs_cl hs_ne
            rw [hge]
            field_simp [sub_ne_zero_of_ne hs_ne]
          have h2 : ∀ᶠ s in 𝓝[≠] ρ, g s * (s - ρ) = ((zeroMultiplicity ρ : ℂ) + (s - ρ) * logDeriv (Gρ ρ hρ) s) * melinTransform f s := by
            have hdecb : Metric.ball ρ (r_decρ ρ hρ) ∈ 𝓝 ρ := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by simp [hr_decρ_pos ρ hρ]))
            have hdecb' : ∀ᶠ s in 𝓝[≠] ρ, s ∈ Metric.ball ρ (r_decρ ρ hρ) := Filter.Eventually.filter_mono nhdsWithin_le_nhds hdecb
            filter_upwards [self_mem_nhdsWithin, hdecb']
            intro s hs_ne hs_dec
            simp [g]
            rw [hr_decρ_eq ρ hρ s hs_dec hs_ne]
            field_simp [sub_ne_zero_of_ne hs_ne]
          filter_upwards [h1, h2]
          intro s hs1 hs2
          exact hs1.trans hs2
        have hwcAt : ContinuousAt hw ρ := hwc.continuousAt (Metric.closedBall_mem_nhds ρ (h_eps ρ (Finset.mem_insert.mpr (Or.inr hρ))).1)
        have hval := cont_congr_value hwcAt hF1c heqF
        simpa [sub_self, zero_mul, add_zero] using hval
      rw [hres, hh]
    -- s=1 项
    have h1_res : (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g (1 : ℂ) (ε 1) =
        (-1 : ℂ) * melinTransform f (1 : ℂ) := by
      rcases h_pole 1 (Finset.mem_insert.mpr (Or.inl rfl)) with ⟨h1w, h1c, h1d, h1eq⟩
      have hres1 := simplePole_residue_local g h1w (1 : ℂ) (ε 1) (h_eps 1 (Finset.mem_insert.mpr (Or.inl rfl))).1 h1c h1d h1eq
      have hh1 : h1w (1 : ℂ) = (-1 : ℂ) * melinTransform f (1 : ℂ) := by
        have hF1c : ContinuousAt (fun s => (-1 + (s - 1) * logDeriv G1 s) * melinTransform f s) (1 : ℂ) := by
          have hGan1 : AnalyticAt ℂ G1 (1 : ℂ) := hr1_an (1 : ℂ) (Metric.mem_ball.mpr (by simp [hr1_pos]))
          have hGnz1 : G1 (1 : ℂ) ≠ 0 := hδG1_nz (1 : ℂ) (Metric.mem_ball.mpr (by simp [hδG1_pos]))
          have hLGc1 : ContinuousAt (logDeriv G1) (1 : ℂ) := (logDeriv_analyticAt hGan1 hGnz1).continuousAt
          have hMf1c : ContinuousAt (melinTransform f) (1 : ℂ) := (hM (1 : ℂ) (Metric.mem_closedBall.mpr (by norm_num [dist_eq_norm, contourRadius]))).continuousAt
          have h1c : ContinuousAt (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ) := continuousAt_const
          have hidc : ContinuousAt (fun x : ℂ => x) (1 : ℂ) := continuousAt_id
          have h1c' : ContinuousAt (fun _ : ℂ => (1 : ℂ)) (1 : ℂ) := continuousAt_const
          have hsubc : ContinuousAt (fun x : ℂ => x - 1) (1 : ℂ) := hidc.sub h1c'
          have hmulc : ContinuousAt (fun x : ℂ => (x - 1) * logDeriv G1 x) (1 : ℂ) := hsubc.mul hLGc1
          have hsumc : ContinuousAt (fun x : ℂ => (-1 + (x - 1) * logDeriv G1 x)) (1 : ℂ) := h1c.add hmulc
          exact hsumc.mul hMf1c
        have heqF : ∀ᶠ s in 𝓝[≠] (1 : ℂ), h1w s = (-1 + (s - 1) * logDeriv G1 s) * melinTransform f s := by
          have h1 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), h1w s = g s * (s - 1) := by
            have hεb : Metric.ball (1 : ℂ) (ε 1) ∈ 𝓝 (1 : ℂ) := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by simp [(h_eps 1 (Finset.mem_insert.mpr (Or.inl rfl))).1]))
            have hεb' : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ∈ Metric.ball (1 : ℂ) (ε 1) := Filter.Eventually.filter_mono nhdsWithin_le_nhds hεb
            filter_upwards [self_mem_nhdsWithin, hεb']
            intro s hs_ne hs_ball
            have hs_cl : s ∈ Metric.closedBall (1 : ℂ) (ε 1) := Metric.ball_subset_closedBall hs_ball
            have hge : g s = h1w s / (s - 1) := h1eq s hs_cl hs_ne
            rw [hge]
            field_simp [sub_ne_zero_of_ne hs_ne]
          have h2 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), g s * (s - 1) = (-1 + (s - 1) * logDeriv G1 s) * melinTransform f s := by
            have hdecb : Metric.ball (1 : ℂ) r_dec1 ∈ 𝓝 (1 : ℂ) := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr (by simp [hr_dec1_pos]))
            have hdecb' : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ∈ Metric.ball (1 : ℂ) r_dec1 := Filter.Eventually.filter_mono nhdsWithin_le_nhds hdecb
            filter_upwards [self_mem_nhdsWithin, hdecb']
            intro s hs_ne hs_dec
            simp [g]
            rw [hr_dec1_eq s hs_dec hs_ne]
            field_simp [sub_ne_zero_of_ne hs_ne]
          filter_upwards [h1, h2]
          intro s hs1 hs2
          exact hs1.trans hs2
        have h1cAt : ContinuousAt h1w (1 : ℂ) := h1c.continuousAt (Metric.closedBall_mem_nhds (1 : ℂ) (h_eps 1 (Finset.mem_insert.mpr (Or.inl rfl))).1)
        have hval := cont_congr_value h1cAt hF1c heqF
        simpa [sub_self, zero_mul, add_zero] using hval
      rw [hres1, hh1]
    rw [hz_sum]
    rw [h1_res]
    simpa [add_comm]
  -- 应用一般留数定理 + 拼接
  have hmain := residue_theorem_general g S ε h_diff_off h_sub h_pole h_eps
  rw [hmain]
  rw [h_sum]
  -- 拼接：∑ m·M[f](ρ) + (-1)·M[f](1) = zetaZeroSide f - farZeroContribution f（定义展开，farZero 消去）
  unfold zetaZeroSide trivialZeroContribution nontrivialZeroSum farZeroContribution
  ring

/-- 留数求和等于零点侧减围道外项（定理，由定义展开）：
    Σ_{ρ ∈ 围道内} m(ρ)·M[f](ρ) + (-1)·M[f](1) = zetaZeroSide(f) - farZeroContribution(f)
    其中 zetaZeroSide(f) = nontrivialZeroSum(f) + trivialZeroContribution(f)，
    nontrivialZeroSum = 围道内零点和 + farZeroContribution（ZetaZeros 显式拆分），
    trivialZeroContribution(f) = -M[f](1)。两侧展开后 ring 关闭（farZero 消去）。 -/
lemma zeta_log_derivative_residue_sum_eq_zeroside (f : TestFunction) :
    (∑ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ)
    + (-1 : ℂ) * melinTransform f (1 : ℂ) =
    zetaZeroSide f - farZeroContribution f := by
  unfold zetaZeroSide trivialZeroContribution nontrivialZeroSum farZeroContribution
  ring

/-- 留数定理（ζ 对数导数版本，定理，由围道留数计算公理推出）：
    ζ'/ζ 乘以 Mellin 变换的围道积分等于零点侧减围道外项：
      contourIntegral(ζ'/ζ · M[f]) = zetaZeroSide(f) - farZeroContribution(f)
    证明：
    (1) zeta_log_derivative_contour_eq_residue_sum：围道积分 = 围道内留数求和
    传递性即得。
    旧版（全零点 tsum 版本）把围道外零点算进右端，随围道外约定废弃；
    farZeroContribution 的消失由 stage_4.far_zero_vanishes（磨光假设）独立承担。 -/
theorem residue_theorem_zeta_log_derivative (f : TestFunction)
    (hM : AnalyticOnNhd ℂ (melinTransform f) (Metric.closedBall (1 / 2 : ℂ) contourRadius))
    (h_no_boundary_zeros : ∀ z, z ∈ Metric.sphere (1 / 2 : ℂ) contourRadius → riemannZeta z ≠ 0)
    (h_zero_in_S : ∀ z, z ∈ Metric.closedBall (1 / 2 : ℂ) contourRadius →
      riemannZeta z = 0 → z ∈ contourZeroFinset ∨ z = 1) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) =
    zetaZeroSide f - farZeroContribution f := by
  rw [zeta_log_derivative_contour_eq_residue_sum f hM h_no_boundary_zeros h_zero_in_S]

/-- Difference holomorphic extension + circle integrability (axiom):
    primeDirichletSeries - zetaLogDerivative vanishes for Re(s) > 1 (Euler product),
    and extends holomorphically inside the contour (singularities at zeta zeros canceled
    by zetaLogDerivative definition). Thus the difference is holomorphic inside the contour
    and CircleIntegrable on the contour, so Cauchy theorem gives zero contour integral.
    Enhanced to include CircleIntegrable: needed for contourIntegral_linear downgrade. -/
lemma primeDirichlet_zetaLogDerivative_diff_holomorphic (f : TestFunction) :
    (∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
      DifferentiableAt ℂ (fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f s) s) ∧
    ContinuousOn (fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f s)
      (Metric.closedBall (1 / 2 : ℂ) contourRadius) ∧
    CircleIntegrable (fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f s) (1 / 2 : ℂ) contourRadius := by sorry

/-- primeDirichletSeries 等于 Nat.Primes 上的求和（引理）：
    primeDirichletSeries s = ∑' p : Nat.Primes, (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))
    证明：用 tsum_subtype_eq_of_support_subset 把 ℕ 上的 if-sum 改写成 Nat.Primes 上的 sum。 -/
lemma primeDirichletSeries_eq_tsum_primes (s : ℂ) :
    primeDirichletSeries s =
    ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
  rw [primeDirichletSeries]
  let f : ℕ → ℂ := fun p => if Nat.Prime p then (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) else 0
  have h_support : Function.support f ⊆ {p : ℕ | Nat.Prime p} := by
    intro p hp
    have hfp : f p ≠ 0 := (Function.mem_support.mp hp)
    by_cases hprime : Nat.Prime p
    · exact hprime
    · have h : f p = 0 := by
        simp [f, hprime]
      contradiction
  have h : (∑' p : {p : ℕ // Nat.Prime p}, f p) = ∑' p : ℕ, f p := by
    exact tsum_subtype_eq_of_support_subset h_support
  have h' : (∑' p : ℕ, f p) = ∑' p : {p : ℕ // Nat.Prime p}, f p := h.symm
  rw [h']
  have h2 : (∑' p : {p : ℕ // Nat.Prime p}, f p) =
      ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
    congr with (p : {p : ℕ // Nat.Prime p})
    simpa [f, p.prop] using rfl
  exact h2

/-- Step 3: 几何级数求和（从 k=1 开始）。
    ∑' k : ℕ, x^(k+1) = x / (1 - x)，当 ‖x‖ < 1。
    证明：利用 mathlib 的 tsum_geometric_of_norm_lt_one。 -/
lemma geometric_sum_from_one (x : ℂ) (h : ‖x‖ < 1) :
    ∑' k : ℕ, x ^ (k + 1) = x / (1 - x) := by
  have h_summable : Summable (fun k : ℕ => x ^ k) := summable_geometric_of_norm_lt_one h
  have h_main : ∑' k : ℕ, x ^ (k + 1) = x * ∑' k : ℕ, x ^ k := by
    have h1 : ∑' k : ℕ, x ^ (k + 1) = ∑' k : ℕ, x ^ k * x := by
      congr with k
      <;> ring
    rw [h1]
    have h2 : ∑' k : ℕ, x ^ k * x = (∑' k : ℕ, x ^ k) * x := by
      simpa [tsum_mul_right] using rfl
    rw [h2] <;> ring
  rw [h_main]
  have h_geom : ∑' k : ℕ, x ^ k = (1 - x)⁻¹ := tsum_geometric_of_norm_lt_one h
  rw [h_geom]
  <;> field_simp <;> ring

/-- Step 5: von Mangoldt L-series 等于素数幂上的二重求和（引理）。
    LSeries Λ s = ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log p) * p^(-(k+1)*s)。
    证明：用 tsum_eq_tsum_primes_of_support_subset_prime_powers 把 ℕ 上的求和转换成素数幂上的求和，
    然后化简 von Mangoldt 函数和复指数。 -/
lemma vonMangoldt_tsum_eq (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1) * s) := by
  let f : ℕ → ℂ := fun n => LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n
  have h_sum : Summable f := by
    simpa [LSeriesSummable, f] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h_support : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    have h1 : f n ≠ 0 := hn
    have h2 : n ≠ 0 := by
      by_contra h2'
      rw [h2'] at h1
      simp [f, LSeries.term] at h1 <;> contradiction
    have h3 : (ArithmeticFunction.vonMangoldt n : ℂ) ≠ 0 := by
      simpa [f, LSeries.term, h2] using h1
    have h4 : IsPrimePow n := by
      simpa [ArithmeticFunction.vonMangoldt_ne_zero_iff] using h3
    exact h4
  have h1 : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = ∑' n : ℕ, f n := by rfl
  rw [h1]
  have h_main : ∑' n : ℕ, f n = ∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 1)) :=
    tsum_eq_tsum_primes_of_support_subset_prime_powers h_sum h_support
  rw [h_main]
  have h7 : ∀ (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 1)) =
      (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) := by
    intro p k
    have hp_pos : (0 : ℕ) < (p : ℕ) := Nat.Prime.pos p.prop
    have h8 : ((p : ℕ) ^ (k + 1)) ≠ 0 := by
      exact pow_ne_zero (k + 1) hp_pos.ne'
    have h9 : f ((p : ℕ) ^ (k + 1)) =
        (ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) : ℂ) / (((p : ℕ) ^ (k + 1)) : ℂ) ^ s := by
      have h91 : f ((p : ℕ) ^ (k + 1)) = LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1)) := by rfl
      rw [h91]
      rw [LSeries.term_def (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1))]
      rw [if_neg h8]
      <;> norm_cast <;> rfl
    rw [h9]
    have h10 : ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) = Real.log (p : ℝ) := by
      have h11 : (k + 1) ≠ 0 := by linarith
      rw [ArithmeticFunction.vonMangoldt_apply_pow h11, ArithmeticFunction.vonMangoldt_apply_prime p.prop]
    rw [h10]
    have h12 : (((p : ℕ) ^ (k + 1)) : ℂ) ^ s = (p : ℂ) ^ ((k + 1 : ℂ) * s) := by
      have h13 : ((p : ℕ) ^ (k + 1) : ℂ) = (p : ℂ) ^ (k + 1 : ℂ) := by
        norm_cast <;> simp [pow_succ] <;> ring
      rw [h13]
      have h14 : 0 ≤ (p : ℂ).re := by
        exact_mod_cast hp_pos.le
      have h15 : ((p : ℂ) ^ (k + 1 : ℂ)) ^ s = (p : ℂ) ^ ((k + 1 : ℂ) * s) := by
        have h16 : (Complex.log (p : ℂ) * (k + 1 : ℂ)).im = 0 := by
          have h17 : 0 < (p : ℝ) := by exact_mod_cast hp_pos
          have h18 : (p : ℂ).im = 0 := by simp
          simp [Complex.log_im, h17, h18, mul_comm] <;> ring
        have h19 : -Real.pi < (Complex.log (p : ℂ) * (k + 1 : ℂ)).im := by
          rw [h16] <;> linarith [Real.pi_pos]
        have h20 : (Complex.log (p : ℂ) * (k + 1 : ℂ)).im ≤ Real.pi := by
          rw [h16] <;> linarith [Real.pi_pos]
        have h21 : (p : ℂ) ^ ((k + 1 : ℂ) * s) = ((p : ℂ) ^ (k + 1 : ℂ)) ^ s :=
          Complex.cpow_mul s h19 h20
        exact h21.symm
      exact h15
    rw [h12]
    have h16 : ((Real.log (p : ℝ) : ℂ)) / (p : ℂ) ^ ((k + 1 : ℂ) * s) =
        (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-(k + 1 : ℂ) * s) := by
      rw [div_eq_mul_inv]
      have hp_ne_zero : (p : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
      have h17 : (p : ℂ) ^ (-((k + 1 : ℂ) * s)) = ((p : ℂ) ^ ((k + 1 : ℂ) * s))⁻¹ :=
        Complex.cpow_neg (p : ℂ) ((k + 1 : ℂ) * s)
      have h18 : (p : ℂ) ^ (-(k + 1 : ℂ) * s) = (p : ℂ) ^ (-((k + 1 : ℂ) * s)) := by
        congr 1 <;> ring
      have h19 : (p : ℂ) ^ (-(k + 1 : ℂ) * s) = ((p : ℂ) ^ ((k + 1 : ℂ) * s))⁻¹ := by
        rw [h18, h17]
      exact congr_arg (fun x : ℂ => (Real.log (p : ℝ) : ℂ) * x) h19.symm
    exact h16
  have h13 : ∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 1)) =
      ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) := by
    apply tsum_congr; intro p; apply tsum_congr; intro k; exact h7 p k
  exact h13

/-- primeDirichletSeries 等于 von Mangoldt 函数的 L 级数（定理）：
    在 Re(s) > 1 时，primeDirichletSeries s = ∑_n Λ(n) n^{-s}。
    证明：利用 mathlib 中的 LSeries_vonMangoldt_eq_deriv_riemannZeta_div 定理，
    von Mangoldt 函数的 L 级数等于 ζ 函数的负对数导数，
    而 primeDirichletSeries s = ∑_p (log p) p^{-s} / (1 - p^{-s}) = -ζ'/ζ(s)。 -/
theorem primeDirichletSeries_eq_LSeries_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
    primeDirichletSeries s = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have h1 : (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s) = - deriv _root_.riemannZeta s / _root_.riemannZeta s := by
    exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h2 : primeDirichletSeries s = - deriv _root_.riemannZeta s / _root_.riemannZeta s := by
    have h21 : primeDirichletSeries s = ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) :=
      primeDirichletSeries_eq_tsum_primes s
    rw [h21]
    have h22 : ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) =
        ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) := by
      apply tsum_congr
      intro p
      have hp_pos : (0 : ℕ) < (p : ℕ) := Nat.Prime.pos p.prop
      have hp_two_le : 2 ≤ (p : ℕ) := Nat.Prime.two_le p.prop
      have h_norm_lt_one : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
        have hp_pos' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        have h_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_two_le
        have h_abs : ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hp_pos' (-s)
        rw [h_abs]
        have h_neg : -s.re < 0 := by linarith
        have h : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt h_gt_one h_neg
        simpa using h
      have h_exp_pow : ∀ (n : ℕ) (a : ℂ),
          (Complex.exp a) ^ n = Complex.exp ((n : ℂ) * a) := by
        intro n a
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, ih]
          have h_eq : Complex.exp ((n : ℂ) * a) * Complex.exp a =
              Complex.exp (((n : ℂ) + 1) * a) := by
            rw [← Complex.exp_add]
            congr 1
            ring
          rw [h_eq]
          have h_cast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by simp
          rw [h_cast]
      have h_mul_cpow : ∀ (k : ℕ), (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) = ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) := by
        intro k
        have hp_pos' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        have hp_ne_zero : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp_pos'.ne'
        have h_pow1 : ((p : ℕ) : ℂ) ^ (-s) =
            Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-s)) :=
          Complex.cpow_def_of_ne_zero hp_ne_zero (-s)
        rw [h_pow1]
        rw [h_exp_pow (k + 1) (Complex.log ((p : ℕ) : ℂ) * (-s))]
        have h_rhs : ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) =
            Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-(k + 1 : ℂ) * s)) :=
          Complex.cpow_def_of_ne_zero hp_ne_zero (-(k + 1 : ℂ) * s)
        rw [h_rhs]
        congr 1
        push_cast
        ring
      have h_geometric : ∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) =
          ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) :=
        geometric_sum_from_one (((p : ℕ) : ℂ) ^ (-s)) h_norm_lt_one
      have h_eq1 : ∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) =
          ∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) := by
        apply tsum_congr
        intro k
        exact (h_mul_cpow k).symm
      have h_main : (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s))) =
          (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s)) := by
        have h_tmp : (∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1)) =
            (∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s)) := h_eq1.symm
        have h_div : ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s)) =
            ∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) := h_geometric.symm
        have h1 : (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s))) =
            (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1)) := by
          exact congr_arg (fun x : ℂ => (Real.log ((p : ℕ) : ℝ) : ℂ) * x) h_div
        have h2 : (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1)) =
            (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s)) := by
          exact congr_arg (fun x : ℂ => (Real.log ((p : ℕ) : ℝ) : ℂ) * x) h_tmp
        exact Eq.trans h1 h2
      have h_assoc : ((Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s))) =
          (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s))) := by
        ring
      have h_final1 : (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s) / (1 - ((p : ℕ) : ℂ) ^ (-s))) =
          (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s)) := h_main
      have h_final2 : (Real.log ((p : ℕ) : ℝ) : ℂ) * (∑' k : ℕ, ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s)) =
          ∑' k : ℕ, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) := by
        rw [tsum_mul_left]
      rw [h_assoc, h_final1, h_final2]
    rw [h22]
    have h23 : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(k + 1 : ℂ) * s) :=
      vonMangoldt_tsum_eq s hs
    exact h23.symm.trans h1
  rw [h1, h2]

end OrderPreservingBijection
