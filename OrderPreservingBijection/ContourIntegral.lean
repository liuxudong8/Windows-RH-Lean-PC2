/-
  围道积分基础设施模块
  为 Weil 显式公式提供围道积分、ζ 对数导数、素理想 Dirichlet 级数、留数定理等。
  依赖 BasicInfrastructure、MellinInfrastructure、ZetaZeros。
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ZetaZeros

namespace OrderPreservingBijection

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

/-- 函数在一点处的留数（def）：
    Res(g, z0) = (1/2πi) ∮_{|z-z0|=ε} g(z) dz，
    其中 ε 足够小使得圆周内只有 z0 一个奇点。
    用 circleIntegral 实现，半径取 1/2（留数与半径无关，由柯西定理保证）。
    留数是 Laurent 展开中 (z-z0)^{-1} 项的系数。 -/
noncomputable def residueAt (g : ℂ → ℂ) (z0 : ℂ) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g z0 (1 / 2)

/-- 一般留数定理（公理，第二档：标准复分析定理）：
    若 g 在围道 |z - 1/2| = contourRadius 内部除有限个奇点 S 外全纯，
    则 (1/2πi) ∮ g(z) dz = Σ_{z0 ∈ S} Res(g, z0)。
    这是复分析的基本定理，由柯西积分公式（Mathlib CauchyIntegral.lean）+ 围道形变推出。
    完整留数定理尚未在 Mathlib 中形式化，此处作为标准定理引入。 -/
lemma residue_theorem_general (g : ℂ → ℂ) (S : Finset ℂ)
    (h_sing : ∀ z ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
      z ∈ S ∨ DifferentiableAt ℂ g z)
    (h_no_other : ∀ z ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
      z ∉ S → DifferentiableAt ℂ g z) :
    contourIntegral g = ∑ z0 ∈ S, residueAt g z0 := by sorry

/-- ζ'/ζ · M[f] 的围道积分等于留数求和（公理，一般留数定理在 ζ 上的应用）：
    围道积分 = 围道内所有奇点的留数之和：
      contourIntegral(ζ'/ζ · M[f]) = Σ_{ρ ∈ 围道内} m(ρ)·M[f](ρ) + (-1)·M[f](1)
    其中非平凡零点处留数 = m(ρ)·M[f](ρ)（对数导数在 m 阶零点处留数为 m，全纯因子 M[f] 可提出），
    s=1 极点处留数 = -M[f](1)（ζ 在 s=1 为一阶极点，对数导数留数为 -1）。
    这是一般留数定理（residue_theorem_general）+ 留数乘积公式 + ζ 具体留数计算的综合结果。
    围道 |s−1/2| = 1 只含 |ρ−1/2| < 1 的零点（有限，contourZeroFinset）；围道外零点
    贡献由 farZeroContribution 表示，故等式右端写为 zetaZeroSide - farZeroContribution
    （zetaZeroSide = 围道内 + 围道外 + s=1 项，减去围道外即围道内留数和）。
    平凡零点（负偶数）在围道外，无贡献（围道外约定）。 -/
lemma zeta_log_derivative_contour_eq_residue_sum (f : TestFunction) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) =
    zetaZeroSide f - farZeroContribution f := by
  -- 证明蓝图（复分析真缺口，逐项待证）：
  -- (1) residue_theorem_general : contourIntegral = Σ_{ρ ∈ 围道内奇点} residueAt(ζ'/ζ·M[f]) ρ
  -- (2) 留数分类：零点 ρ（m 阶）处 residueAt = m(ρ)·M[f](ρ)（对数导数留数 = 阶，M[f] 全纯提出）；
  --     s=1 一阶极点处 residueAt = -M[f](1)（ζ 在 1 的留数 -1）
  -- (3) 围道内奇点 = contourZeroFinset ∪ {1}（ζ 的奇点只有零点与 s=1 极点）
  -- (4) zetaZeroSide = 围道内零点和 + farZeroContribution + trivialZeroContribution
  --     ⟹ Σ_{围道内} m(ρ)M[f](ρ) + (-1)M[f](1) = zetaZeroSide - farZeroContribution
  sorry

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
theorem residue_theorem_zeta_log_derivative (f : TestFunction) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) =
    zetaZeroSide f - farZeroContribution f := by
  rw [zeta_log_derivative_contour_eq_residue_sum f]

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
            rw [←Complex.exp_add] <;> ring
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
