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

/-- Mellin 被积函数可积性（公理，标准测度论事实）：
    对 TestFunction f，f(x) * x^{s-1} 在 (0,∞) 上可积。
    数学依据：f 有界 + 紧支集 + 在 0 附近为 0 + 可测 → 被积函数有界紧支集可测 → Lebesgue 可积。
    后续可降级为 theorem（需测度论 API：IntegrableOn.bddAbove + IntegrableOn.union）。 -/
axiom mellin_integrand_integrable (f : TestFunction) (s : ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))

/-- Mellin 变换的线性性（定理，由积分线性性推出）：
    M[c₁·f₁ + c₂·f₂](s) = c₁·M[f₁](s) + c₂·M[f₂](s)。
    证明：Mellin 变换是积分算子，积分的线性性直接推出 Mellin 变换的线性性。
    这是 Paley-Wiener 理论和磨光函数插值的基础。 -/
theorem melinTransform_linear (f1 f2 : TestFunction) (c1 c2 : ℂ) (s : ℂ) :
    melinTransform (c1 • f1 + c2 • f2) s = c1 * melinTransform f1 s + c2 * melinTransform f2 s := by
  let h1 := fun x : ℝ => if 0 < x then f1.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0
  let h2 := fun x : ℝ => if 0 < x then f2.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0
  have h_integrand : (fun x : ℝ => if 0 < x then (c1 • f1 + c2 • f2).eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
      (fun x : ℝ => c1 * h1 x + c2 * h2 x) := by
    funext x
    by_cases hx : 0 < x
    · have h_eval : (c1 • f1 + c2 • f2).eval x = c1 * f1.eval x + c2 * f2.eval x := by rfl
      simp only [h1, h2, h_eval, if_pos hx] <;> ring
    · simp only [h1, h2, if_neg hx] <;> ring
  rw [melinTransform, melinTransform, melinTransform, h_integrand]
  -- TODO: 证明 h1, h2 可积（TestFunction 紧支集 + 适当条件下 Mellin 被积函数可积）
  have h1_int : MeasureTheory.Integrable h1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    mellin_integrand_integrable f1 s
  have h2_int : MeasureTheory.Integrable h2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    mellin_integrand_integrable f2 s
  rw [realIntegral_linear h1 h2 c1 c2 h1_int h2_int]
  <;> ring

/-- Mellin 变换的数乘性质：M[c·f](s) = c·M[f](s)。 -/
theorem melinTransform_smul (f : TestFunction) (c : ℂ) (s : ℂ) :
    melinTransform (c • f) s = c * melinTransform f s := by
  let h1 := fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0
  have h_integrand : (fun x : ℝ => if 0 < x then (c • f).eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
      (fun x : ℝ => c * h1 x + (0 : ℂ)) := by
    funext x
    by_cases hx : 0 < x
    · have h_eval : (c • f).eval x = c * f.eval x := by rfl
      simp only [h1, h_eval, if_pos hx] <;> ring
    · simp only [h1, if_neg hx] <;> ring
  rw [melinTransform, melinTransform, h_integrand]
  have h1_int : MeasureTheory.Integrable h1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    mellin_integrand_integrable f s
  have h2_int : MeasureTheory.Integrable (fun _ : ℝ => (0 : ℂ)) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa using h1_int.of_not_nonempty
  have h_main := realIntegral_linear h1 (fun _ => (0 : ℂ)) c (0 : ℂ) h1_int h2_int
  simpa using h_main

/-- 微分算子 D = x d/dx：
    D f(x) = x * f'(x)。
    Mellin 变换的性质：M(D f)(s) = -s * Mf(s)。
    这是微分算子消零构造的核心。 -/
noncomputable def differentialOperator (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  x * deriv f x

/-- 微分算子作用在 TestFunction 上（假设 f 是 C^∞ 的）：
    如果 f 是 C^∞ 的紧支函数，那 D f 也是 TestFunction。 -/
noncomputable def differentialOperatorTestFunction (f : TestFunction) : TestFunction :=
  { toFun := fun x : ℝ => x * deriv f.eval x
    hasCompactSupport := by sorry
    isBounded := by sorry
    vanishesNearZero := by sorry
    measurable := by sorry }

/-- 微分算子的 Mellin 变换公式：
    M(D f)(s) = -s * Mf(s)。
    证明：分部积分 + 边界项为 0（f 紧支集）。 -/
theorem melinTransform_differentialOperator (f : TestFunction) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s := by
  -- 第一步：证明被积函数相等
  have h1 : ∀ (x : ℝ), 0 < x →
      (x * deriv f.eval x) * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
      deriv f.eval x * Complex.exp (s * (Real.log x : ℂ)) := by
    intro x hx
    have h21 : Real.exp (Real.log x) = x := Real.exp_log hx
    have h22 : x = Real.exp (Real.log x) := Eq.symm h21
    have h2 : (x : ℂ) = Complex.exp ((Real.log x : ℂ)) := by
      exact_mod_cast h22
    rw [h2]
    have h3 : Complex.exp (Real.log x : ℂ) * deriv f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        deriv f.eval x * (Complex.exp (Real.log x : ℂ) * Complex.exp ((s - 1) * (Real.log x : ℂ))) := by ring
    rw [h3]
    have h4 : Complex.exp (Real.log x : ℂ) * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        Complex.exp ((Real.log x : ℂ) + (s - 1) * (Real.log x : ℂ)) := by
      rw [←Complex.exp_add]
    rw [h4]
    have h5 : (Real.log x : ℂ) + (s - 1) * (Real.log x : ℂ) = s * (Real.log x : ℂ) := by ring
    rw [h5]
  sorry

/-- 算子 (D + t) 的 Mellin 变换公式：
    M((D + t) f)(s) = -(s - t) * Mf(s)。
    证明：Mellin 变换线性性 + 微分算子公式。 -/
theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  -- 用线性性拆成两个 Mellin 变换的和
  have h1 := melinTransform_linear (differentialOperatorTestFunction f) f (1 : ℂ) t s
  -- 我们需要证明 1 • differentialOperatorTestFunction f = differentialOperatorTestFunction f
  have h_one_smul : (1 : ℂ) • differentialOperatorTestFunction f = differentialOperatorTestFunction f := by
    apply TestFunction.toFun_injective
    funext x
    change (1 : ℂ) * (differentialOperatorTestFunction f).eval x = (differentialOperatorTestFunction f).eval x
    <;> ring
  -- 现在，我们有 h1 : melinTransform (1 • f1 + t • f2) s = 1 * Mf1 + t * Mf2
  -- 我们需要的是 melinTransform (f1 + t • f2) s = ...
  -- 我们可以把 h1 里的 1 • f1 替换成 f1
  have h_main : melinTransform ((1 : ℂ) • differentialOperatorTestFunction f + t • f) s =
      melinTransform (differentialOperatorTestFunction f + t • f) s := by
    rw [h_one_smul]
  rw [←h_main]
  rw [h1]
  have h2 : (1 : ℂ) * melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s =
      melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s := by
    ring
  rw [h2]
  -- 用微分算子的公式
  have h3 : melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h3]
  <;> ring


end OrderPreservingBijection
