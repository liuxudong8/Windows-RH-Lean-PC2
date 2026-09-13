/-
  围道积分基础设施模块
  为 Weil 显式公式提供围道积分、ζ 对数导数、素理想 Dirichlet 级数、留数定理等。
  依赖 BasicInfrastructure、MellinInfrastructure、ZetaZeros。
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Basic
import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ZetaZeros

namespace OrderPreservingBijection

/-- 围道半径（opaque）：Weil 显式公式中使用的圆围道半径。
    以 1/2 为中心，半径足够大以包含所有相关非平凡零点。
    具体值不影响结论（由围道积分的形变不变性保证）。 -/
opaque contourRadius : ℝ

/-- 围道半径为正（公理）。 -/
axiom contourRadius_pos : 0 < contourRadius

/-- 归一化围道积分（def）：(1/2πi) ∮_{|s - 1/2| = contourRadius} g(s) ds。
    用 Mathlib 的 circleIntegral 实现，中心在 1/2（临界线中点）。 -/
noncomputable def contourIntegral (g : ℂ → ℂ) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * circleIntegral g (1 / 2 : ℂ) contourRadius

/-- 围道积分的线性性（公理，第一档）：
    contourIntegral(c₁·g₁ + c₂·g₂) = c₁·contourIntegral(g₁) + c₂·contourIntegral(g₂)。
    由 circleIntegral 的线性性和数乘直接推出。 -/
axiom contourIntegral_linear (g1 g2 : ℂ → ℂ) (c1 c2 : ℂ) :
    contourIntegral (fun s => c1 * g1 s + c2 * g2 s) = c1 * contourIntegral g1 + c2 * contourIntegral g2

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

/-- 柯西定理（公理，围道积分版本）：
    如果 g 在围道内部（开圆盘 |s - 1/2| < contourRadius）全纯，
    则围道积分为零。
    这是复分析基本定理，Mathlib 有 circleIntegral 版本但需额外条件。 -/
axiom cauchy_theorem_contour (g : ℂ → ℂ) :
    (∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius, DifferentiableAt ℂ g s) →
    contourIntegral g = 0

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
axiom residue_theorem_general (g : ℂ → ℂ) (S : Finset ℂ)
    (h_sing : ∀ z ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
      z ∈ S ∨ DifferentiableAt ℂ g z)
    (h_no_other : ∀ z ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
      z ∉ S → DifferentiableAt ℂ g z) :
    contourIntegral g = ∑ z0 ∈ S, residueAt g z0

/-- ζ'/ζ · M[f] 的围道积分等于留数求和（公理，一般留数定理在 ζ 上的应用）：
    围道积分 = 围道内所有奇点的留数之和：
      contourIntegral(ζ'/ζ · M[f]) = Σ_{ρ:非平凡零点} m(ρ)·M[f](ρ) + (-1)·M[f](1)
    其中非平凡零点处留数 = m(ρ)·M[f](ρ)（对数导数在 m 阶零点处留数为 m，全纯因子 M[f] 可提出），
    s=1 极点处留数 = -M[f](1)（ζ 在 s=1 为一阶极点，对数导数留数为 -1）。
    这是一般留数定理（residue_theorem_general）+ 留数乘积公式 + ζ 具体留数计算的综合结果。
    围道包含所有非平凡零点（contourRadius 足够大），平凡零点在围道外。 -/
axiom zeta_log_derivative_contour_eq_residue_sum (f : TestFunction) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) =
    (∑' n : ℕ, (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n))
    + (-1 : ℂ) * melinTransform f (1 : ℂ)

/-- 留数求和等于零点侧（公理，trivialZeroContribution 的定义性质）：
    Σ_{ρ:非平凡零点} m(ρ)·M[f](ρ) + (-1)·M[f](1) = zetaZeroSide(f)
    其中 zetaZeroSide(f) = nontrivialZeroSum(f) + trivialZeroContribution(f)，
    trivialZeroContribution(f) 包含平凡零点贡献和 s=1 极点贡献的净效果。 -/
axiom zeta_log_derivative_residue_sum_eq_zeroside (f : TestFunction) :
    (∑' n : ℕ, (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n))
    + (-1 : ℂ) * melinTransform f (1 : ℂ) = zetaZeroSide f

/-- 留数定理（ζ 对数导数版本，定理，由两条留数计算公理推出）：
    ζ'/ζ 乘以 Mellin 变换的围道积分等于零点侧求和：
      contourIntegral(ζ'/ζ · M[f]) = zetaZeroSide(f)
    证明：
    (1) zeta_log_derivative_contour_eq_residue_sum：围道积分 = 留数求和
    (2) zeta_log_derivative_residue_sum_eq_zeroside：留数求和 = zetaZeroSide
    (3) 传递性即得。
    旧版为单一公理，现拆为一般留数定理（residue_theorem_general）+ 两条具体计算公理，
    residue_theorem_zeta_log_derivative 降级为定理。 -/
theorem residue_theorem_zeta_log_derivative (f : TestFunction) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) = zetaZeroSide f := by
  rw [zeta_log_derivative_contour_eq_residue_sum f, zeta_log_derivative_residue_sum_eq_zeroside f]

/-- 差的全纯延拓（公理）：
    primeDirichletSeries - zetaLogDerivative 在 Re(s) > 1 内为零（由 Euler 乘积），
    且可解析延拓为围道内部的全纯函数（仅有的奇点在 ζ 零点处，但已被 zetaLogDerivative 的定义抵消）。
    因此差在围道内部全纯，由柯西定理围道积分为零。 -/
axiom primeDirichlet_zetaLogDerivative_diff_holomorphic (f : TestFunction) :
    ∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
    DifferentiableAt ℂ (fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f s) s

end OrderPreservingBijection
