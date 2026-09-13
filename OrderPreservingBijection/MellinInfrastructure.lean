/-
  Mellin 变换基础设施模块
  包含 melinTransform 及其线性性定理。
  依赖 BasicInfrastructure（TestFunction、realIntegral）。
-/

import OrderPreservingBijection.BasicInfrastructure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OrderPreservingBijection

/-- Mellin 变换（def，标准积分定义）：
    M[f](s) = ∫₀^∞ f(x) x^{s-1} dx = ∫₀^∞ f(x) e^{(s-1) ln x} dx。
    对紧支光滑 f，Mellin 变换在 Re(s) 充分大时绝对收敛，
    并可解析延拓到整个复平面（除可能的极点外）。
    这是 Weil 显式公式和磨光函数插值理论的核心工具。 -/
noncomputable def melinTransform (f : TestFunction) (s : ℂ) : ℂ :=
    realIntegral (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)

/-- Mellin 变换的线性性（定理，由积分线性性推出）：
    M[c₁·f₁ + c₂·f₂](s) = c₁·M[f₁](s) + c₂·M[f₂](s)。
    证明：Mellin 变换是积分算子，积分的线性性直接推出 Mellin 变换的线性性。
    这是 Paley-Wiener 理论和磨光函数插值的基础。 -/
theorem melinTransform_linear (f1 f2 : TestFunction) (c1 c2 : ℂ) (s : ℂ) :
    melinTransform (c1 • f1 + c2 • f2) s = c1 * melinTransform f1 s + c2 * melinTransform f2 s := by
  have h_integrand : (fun x : ℝ => if 0 < x then (c1 • f1 + c2 • f2).eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
      (fun x : ℝ => c1 * (if 0 < x then f1.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) +
                        c2 * (if 0 < x then f2.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)) := by
    funext x
    by_cases hx : 0 < x
    · rw [if_pos hx, if_pos hx, if_pos hx]
      have h_eval : (c1 • f1 + c2 • f2).eval x = c1 * f1.eval x + c2 * f2.eval x := by rfl
      rw [h_eval] <;> ring
    · rw [if_neg hx, if_neg hx, if_neg hx] <;> ring
  rw [melinTransform, melinTransform, melinTransform, h_integrand]
  rw [realIntegral_linear]
  <;> ring

end OrderPreservingBijection
