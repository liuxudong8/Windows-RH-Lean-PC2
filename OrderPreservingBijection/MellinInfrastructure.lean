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

/-- 微分算子的 Mellin 变换公式：M(D f)(s) = -s * Mf(s)。
    证明：令 g(x) = f(x)·x^s，则 g'(x) = f'(x)·x^s + s·f(x)·x^{s-1}。
    f 紧支且在 0 附近消失，故 g 在积分边界为 0，∫ g' = 0，移项即得。 -/
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
  -- 取支集界：f 在 x ≤ a 和 x ≥ b 时为 0
  rcases f.vanishesNearZero with ⟨ε, hε_pos, hε⟩
  rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
  let a : ℝ := ε / 2
  let b : ℝ := R + ε + 2
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have hab : a < b := by dsimp only [a, b]; linarith
  have hf_left : ∀ x, x ≤ a → f.eval x = 0 := by
    intro x hx
    have hlt : x < ε := by dsimp only [a] at hx; linarith
    exact hε x hlt
  have hf_right : ∀ x, x ≥ b → f.eval x = 0 := by
    intro x hx
    have hxpos : 0 < x := by dsimp only [b] at hx; linarith
    have habs : |x| > R := by
      rw [abs_of_pos hxpos]; dsimp only [b] at hx; linarith
    exact hR x habs
  -- g(x) = f(x) * x^s，x > 0
  let g : ℝ → ℂ := fun x => f.eval x * Complex.exp (s * (Real.log x : ℂ))
  have g_left : ∀ x, x ≤ a → g x = 0 := by
    intro x hx; have := hf_left x hx; simp [g, this]
  have g_right : ∀ x, x ≥ b → g x = 0 := by
    intro x hx; have := hf_right x hx; simp [g, this]
  -- g'(x) = f'(x) x^s + s f(x) x^{s-1}（链法则，详见 h_integral_deriv）
  have hderiv : ∀ (x : ℝ), 0 < x →
      HasDerivAt g (deriv f.eval x * Complex.exp (s * (Real.log x : ℂ)) +
        s * f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ))) x := by
    intro x hx; sorry
  set A : ℝ → ℂ := fun x => deriv f.eval x * Complex.exp (s * (Real.log x : ℂ)) with hA
  set B : ℝ → ℂ := fun x => f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) with hB
  have h_integral_deriv : ∫ x in Set.Ioi (0:ℝ), (A x + s * B x) = 0 := by
    -- g' = A + s*B 在 x>0 时（hderiv）
    -- g 在 (0,a] 上恒为 0 ⇒ g' 在 (0,a) 上为 0
    -- g 在 [b,∞) 上恒为 0 ⇒ g' 在 (b,∞) 上为 0
    -- 故 ∫_{Ioi 0} g' = ∫_{Icc a b} g'
    have h_left_zero : ∀ x ∈ Set.Ioc (0:ℝ) a, A x + s * B x = 0 := by sorry
    have h_right_zero : ∀ x ∈ Set.Ioi b, A x + s * B x = 0 := by sorry
    have h_split : ∫ x in Set.Ioi (0:ℝ), (A x + s * B x) =
        ∫ x in Set.Icc a b, (A x + s * B x) := by
      sorry
    rw [h_split]
    -- FTC: ∫_a^b g' = g(b) - g(a) = 0
    have h_fTC : ∫ x in Set.Icc a b, (A x + s * B x) = g b - g a := by
      -- a ≤ b
      have hab : a ≤ b := by dsimp only [a, b]; linarith
      -- ∫_{Icc a b} g' = ∫_a^b g'（Icc/Ioc 端点测度为零）
      have h_set_to_interval : ∫ x in Set.Icc a b, (A x + s * B x) =
          ∫ (x : ℝ) in a..b, (A x + s * B x) := by
        sorry
      rw [h_set_to_interval]
      -- g 在 Icc a b 上逐点可导，g' = A + s*B
      have hderiv' : ∀ x ∈ Set.uIcc a b, HasDerivAt g (A x + s * B x) x := by
        intro x hx
        have h_ab : a ≤ b := by dsimp only [a, b]; linarith
        have hxa : a ≤ x := by
          have h : x ∈ Set.uIcc a b := hx
          rw [Set.uIcc_of_le h_ab] at h
          exact h.1
        have hxpos : 0 < x := by linarith [ha_pos, hxa]
        have h := hderiv x hxpos
        have h_eq : deriv f.eval x * Complex.exp (s * (Real.log x : ℂ)) +
            s * f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = A x + s * B x := by
          simp [A, B] <;> ring
        rw [h_eq] at h
        exact h
      have hint : IntervalIntegrable (fun x => A x + s * B x) MeasureTheory.volume a b := by
        sorry
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint
    rw [h_fTC, g_right b (by linarith), g_left a (by linarith)] <;> ring
  have hlin : ∫ x in Set.Ioi (0:ℝ), (A x + s * B x) =
      (∫ x in Set.Ioi (0:ℝ), A x) + s * (∫ x in Set.Ioi (0:ℝ), B x) := by
    -- B = f·x^{s-1}，其可积性由 mellin_integrand_integrable f s 给出
    -- （B 在 Ioi 0 上等于 mellin_integrand_integrable 的被积函数）
    have hB_int : MeasureTheory.Integrable B
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
      sorry
    -- A = f'·x^s，deriv f 也是紧支光滑，故 A 同样可积
    have hA_int : MeasureTheory.Integrable A
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
      sorry
    have h_sB_int : MeasureTheory.Integrable (fun x => s * B x)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
      hB_int.const_mul s
    have h1 : ∫ x in Set.Ioi (0:ℝ), (A x + s * B x) =
        (∫ x in Set.Ioi (0:ℝ), A x) + ∫ x in Set.Ioi (0:ℝ), (s * B x) :=
      MeasureTheory.integral_add hA_int h_sB_int
    have h2 : ∫ x in Set.Ioi (0:ℝ), (s * B x) = s * (∫ x in Set.Ioi (0:ℝ), B x) := by
      exact?
    rw [h1, h2]
  have h_eq1 : melinTransform (differentialOperatorTestFunction f : TestFunction) s =
      ∫ x in Set.Ioi (0:ℝ), A x := by
    unfold melinTransform realIntegral
    have h_ae : (fun x : ℝ => (if 0 < x then
          (differentialOperatorTestFunction f : TestFunction).eval x *
            Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] A := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (by simp : MeasurableSet (Set.Ioi (0:ℝ)))]
        with x hx
      have hxpos : 0 < x := hx
      simp only [if_pos hxpos]
      have h_eval : (differentialOperatorTestFunction f : TestFunction).eval x =
          (x : ℂ) * deriv f.eval x := by rfl
      rw [h_eval, h1 x hxpos] <;> rfl
    exact MeasureTheory.integral_congr_ae h_ae
  have h_eq2 : melinTransform f s = ∫ x in Set.Ioi (0:ℝ), B x := by
    unfold melinTransform realIntegral
    have h_ae : (fun x : ℝ => (if 0 < x then
          f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] B := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (by simp : MeasurableSet (Set.Ioi (0:ℝ)))]
        with x hx
      have hxpos : 0 < x := hx
      simp only [if_pos hxpos] <;> rfl
    exact MeasureTheory.integral_congr_ae h_ae
  have h_sum : (∫ x in Set.Ioi (0:ℝ), A x) + s * (∫ x in Set.Ioi (0:ℝ), B x) = 0 := by
    rw [←hlin]; exact h_integral_deriv
  have h_main : (∫ x in Set.Ioi (0:ℝ), A x) = -s * (∫ x in Set.Ioi (0:ℝ), B x) := by
    calc
      (∫ x in Set.Ioi (0:ℝ), A x)
        = (∫ x in Set.Ioi (0:ℝ), A x) + s * (∫ x in Set.Ioi (0:ℝ), B x) -
            s * (∫ x in Set.Ioi (0:ℝ), B x) := by ring
      _ = 0 - s * (∫ x in Set.Ioi (0:ℝ), B x) := by rw [h_sum] <;> ring
      _ = -s * (∫ x in Set.Ioi (0:ℝ), B x) := by ring
  calc
    melinTransform (differentialOperatorTestFunction f : TestFunction) s
      = ∫ x in Set.Ioi (0:ℝ), A x := h_eq1
    _ = -s * (∫ x in Set.Ioi (0:ℝ), B x) := h_main
    _ = -s * melinTransform f s := by rw [h_eq2] <;> ring

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
