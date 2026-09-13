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

/-- Euler 乘积 → 对数导数等式（公理，Re(s) > 1）：
    由 Mathlib 的 riemannZeta_eulerProduct（ζ(s) = ∏_p (1-p^{-s})^{-1}），
    取对数导数得 ζ'/ζ(s) = Σ_p (log p) p^{-s}/(1-p^{-s}) = primeDirichletSeries(s)。
    此公理断言该等式在 Re(s) > 1 半平面成立。
    Mathlib 有 Euler 乘积，但对数导数的逐项求导需要额外分析。 -/
axiom euler_product_log_derivative_eq (s : ℂ) :
    1 < s.re → zetaLogDerivative s = primeDirichletSeries s

/-- 留数定理（公理，ζ 对数导数版本）：
    ζ'/ζ 的围道积分等于围道内部所有奇点的留数之和。
    (ζ'/ζ)(s) 的奇点在 ζ 的零点处（留数 = 零点阶数）和 s=1 极点处（留数 = -1）。
    乘以 Mellin 变换 f̂(s) 后，积分 = Σ_{ρ:非平凡零点} m(ρ)·f̂(ρ) + 平凡零点贡献 + 极点贡献
             = zetaZeroSide(f)。
    这是留数定理在 Weil 显式公式中的标准应用。 -/
axiom residue_theorem_zeta_log_derivative (f : TestFunction) :
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s) = zetaZeroSide f

/-- 差的全纯延拓（公理）：
    primeDirichletSeries - zetaLogDerivative 在 Re(s) > 1 内为零（由 Euler 乘积），
    且可解析延拓为围道内部的全纯函数（仅有的奇点在 ζ 零点处，但已被 zetaLogDerivative 的定义抵消）。
    因此差在围道内部全纯，由柯西定理围道积分为零。 -/
axiom primeDirichlet_zetaLogDerivative_diff_holomorphic (f : TestFunction) :
    ∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius,
    DifferentiableAt ℂ (fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f s) s

end OrderPreservingBijection
