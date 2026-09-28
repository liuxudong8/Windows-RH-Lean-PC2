/-
  Mellin 变换基础设施模块
-/

import OrderPreservingBijection.BasicInfrastructure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OrderPreservingBijection

/-- Mellin 变换（def，标准积分定义）。 -/
noncomputable def melinTransform (f : TestFunction) (s : ℂ) : ℂ :=
    realIntegral (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)

/-- Mellin 被积函数可积性（公理）。 -/
lemma mellin_integrand_integrable (f : TestFunction) (s : ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by sorry

/-- Mellin 变换的线性性。 -/
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
  have h1_int : MeasureTheory.Integrable h1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    mellin_integrand_integrable f1 s
  have h2_int : MeasureTheory.Integrable h2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    mellin_integrand_integrable f2 s
  rw [realIntegral_linear h1 h2 c1 c2 h1_int h2_int] <;> ring

/-- Mellin 变换的数乘性质。 -/
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

/-- 微分算子 D = x d/dx。 -/
noncomputable def differentialOperator (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  x * deriv f x

-- 公共辅助：deriv f.eval 是 C^∞
private lemma deriv_contDiff (f : SmoothTestFunction) : ContDiff ℝ ⊤ (deriv f.eval) := by
  have h : ContDiff ℝ ⊤ f.eval := f.contDiff
  exact?

-- 公共辅助：x ↦ (x:ℂ) 是 C^∞
private lemma coe_real_complex_contDiff : ContDiff ℝ ⊤ (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

/-- 微分算子作用在光滑测试函数上：D f(x) = x * f'(x)。 -/
noncomputable def differentialOperatorTestFunction (f : SmoothTestFunction) : SmoothTestFunction :=
  let toFun : ℝ → ℂ := fun x => (x : ℂ) * deriv f.eval x
  have hcd : ContDiff ℝ ⊤ (deriv f.eval) := deriv_contDiff f
  have hmul : ContDiff ℝ ⊤ toFun := coe_real_complex_contDiff.mul hcd
  { toFun := toFun
    hasCompactSupport := by
      rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
      refine ⟨R, hR_pos, fun x hx => ?_⟩
      have h_cases : x > R ∨ x < -R := by
        by_cases h1 : x > R
        · exact Or.inl h1
        · have h1' : x ≤ R := by linarith
          by_cases h2 : x < -R
          · exact Or.inr h2
          · have h2' : x ≥ -R := by linarith
            have : |x| ≤ R := by rw [abs_le] <;> exact ⟨h2', h1'⟩
            linarith
      have h_event : f.eval =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        rcases h_cases with (h | h)
        · have nh : Set.Ioi R ∈ nhds x := Ioi_mem_nhds h
          filter_upwards [nh] with y hy
          have hy' : y > R := hy
          have h_ypos : (0 : ℝ) < y := hR_pos.trans hy'
          exact hR y (by rw [abs_of_pos h_ypos]; exact hy')
        · have nh : Set.Iio (-R) ∈ nhds x := Iio_mem_nhds h
          filter_upwards [nh] with y hy
          have hy' : y < -R := hy
          have hRneg : -R < 0 := by linarith
          have h_yneg : y < 0 := lt_trans hy' hRneg
          have h_abs : |y| > R := by
            rw [abs_of_neg h_yneg]
            have : -y > R := by linarith
            exact this
          exact hR y h_abs
      have hder : deriv f.eval x = 0 := by
        rw [h_event.deriv_eq] <;> simp
      simp only [toFun, hder] <;> ring
    isBounded := by
      rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
      have hcont : Continuous toFun := hmul.continuous
      have h_norm_cont : ContinuousOn (fun x => ‖toFun x‖) (Set.Icc (-R) R) :=
        hcont.norm.continuousOn
      have h_bdd : ∃ (B : ℝ), ∀ x ∈ Set.Icc (-R) R, ‖toFun x‖ ≤ B := by
        have hc : IsCompact (Set.Icc (-R) R) := isCompact_Icc
        have h : BddAbove ((fun x => ‖toFun x‖) '' Set.Icc (-R) R) :=
          hc.bddAbove_image h_norm_cont
        rcases h with ⟨B, hB⟩
        refine ⟨B, fun x hx => hB ?_⟩
        exact Set.mem_image_of_mem _ hx
      rcases h_bdd with ⟨B, hB⟩
      refine ⟨max B 1, by positivity, fun x => ?_⟩
      by_cases hx : x ∈ Set.Icc (-R) R
      · exact le_trans (hB x hx) (le_max_left _ _)
      · have h_out : |x| > R := by
          by_contra h'
          have h'' : |x| ≤ R := by linarith
          have : x ∈ Set.Icc (-R) R := by
            rw [Set.mem_Icc]; rw [abs_le] at h''; exact ⟨by linarith, by linarith⟩
          exact hx this
        have h_event : f.eval =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
          have h_cases2 : x > R ∨ x < -R := by
            by_cases h2 : x > R
            · exact Or.inl h2
            · have h2' : x ≤ R := by linarith
              have h3 : |x| > R := h_out
              have h4 : x < -R := by
                by_cases h5 : x ≤ 0
                · rw [abs_of_nonpos h5] at h3; linarith
                · have h6 : 0 < x := by linarith
                  rw [abs_of_pos h6] at h3; linarith
              exact Or.inr h4
          rcases h_cases2 with (h2 | h2)
          · have nh : Set.Ioi R ∈ nhds x := Ioi_mem_nhds h2
            filter_upwards [nh] with y hy
            have hy' : y > R := hy
            have h_ypos : (0 : ℝ) < y := hR_pos.trans hy'
            exact hR y (by rw [abs_of_pos h_ypos]; exact hy')
          · have nh : Set.Iio (-R) ∈ nhds x := Iio_mem_nhds h2
            filter_upwards [nh] with y hy
            have hy' : y < -R := hy
            have hRneg : -R < 0 := by linarith
            have h_yneg : y < 0 := lt_trans hy' hRneg
            have h_abs : |y| > R := by
              rw [abs_of_neg h_yneg]
              have : -y > R := by linarith
              exact this
            exact hR y h_abs
        have hder : deriv f.eval x = 0 := by
          rw [h_event.deriv_eq] <;> simp
        have h0 : toFun x = 0 := by
          simp only [toFun, hder] <;> ring
        rw [h0]
        simp [norm_zero]
    vanishesNearZero := by
      rcases f.vanishesNearZero with ⟨ε, hε_pos, hε⟩
      refine ⟨ε, hε_pos, fun x hx => ?_⟩
      have h_event : f.eval =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        have nh : Set.Iio ε ∈ nhds x := Iio_mem_nhds hx
        filter_upwards [nh] with y hy
        exact hε y hy
      have hder : deriv f.eval x = 0 := by
        rw [h_event.deriv_eq] <;> simp
      simp only [toFun, hder] <;> ring
    measurable := hmul.continuous.measurable
    contDiff := hmul }

/-- 微分算子的 Mellin 变换公式：M(D f)(s) = -s * Mf(s)。 -/
theorem melinTransform_differentialOperator (f : SmoothTestFunction) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s := by
  have h1 : ∀ (x : ℝ), 0 < x →
      (x * deriv f.eval x) * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
      deriv f.eval x * Complex.exp (s * (Real.log x : ℂ)) := by
    intro x hx
    have h21 : Real.exp (Real.log x) = x := Real.exp_log hx
    have h22 : (x : ℂ) = Complex.exp ((Real.log x : ℂ)) := by exact_mod_cast h21.symm
    rw [h22]
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

/-- 算子 (D + t) 的 Mellin 变换公式。 -/
theorem melinTransform_differentialOperator_add (f : SmoothTestFunction) (t : ℂ) (s : ℂ) :
    melinTransform ((differentialOperatorTestFunction f : TestFunction) + t • (f : TestFunction)) s = -(s - t) * melinTransform f s := by
  let fD : TestFunction := differentialOperatorTestFunction f
  let fBase : TestFunction := f
  have h1 := melinTransform_linear fD fBase (1 : ℂ) t s
  have h_one_smul : (1 : ℂ) • fD = fD := by
    apply TestFunction.toFun_injective
    funext x
    change (1 : ℂ) * fD.eval x = fD.eval x <;> ring
  have h_main : melinTransform ((1 : ℂ) • fD + t • fBase) s =
      melinTransform (fD + t • fBase) s := by rw [h_one_smul]
  rw [←h_main, h1]
  have h2 : (1 : ℂ) * melinTransform fD s + t * melinTransform fBase s =
      melinTransform fD s + t * melinTransform f s := by
    have h_eq : melinTransform fBase s = melinTransform f s := by rfl
    rw [h_eq] <;> ring
  rw [h2]
  have h3 : melinTransform fD s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h3] <;> ring

end OrderPreservingBijection
