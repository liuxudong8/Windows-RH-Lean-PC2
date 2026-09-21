import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 紧集上的有界可测函数是可积的 -/
theorem integrableOn_bdd (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (f : ℝ → ℝ), Measurable f → (∃ C, 0 < C ∧ ∀ x ∈ Set.Icc ε₀ R₀, |f x| ≤ C) →
      MeasureTheory.IntegrableOn f (Set.Icc ε₀ R₀) := by
  intro f hf_meas ⟨C, hC_pos, hC⟩
  have h_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)), x ∈ Set.Icc ε₀ R₀ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have h_bound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)), ‖f x‖ ≤ C := by
    filter_upwards [h_ae] with x hx
    have h1 : |f x| ≤ C := hC x hx
    simpa using h1
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)) := by
    exact?
  exact MeasureTheory.Integrable.of_bound hf_meas.aestronglyMeasurable C h_bound

/-- 测试 Set.indicator 的用法 -/
theorem test_indicator (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (f1 f2 : ℝ → ℝ),
    (∀ x ∈ Set.Icc ε₀ R₀, f1 x ≤ f2 x) →
    MeasureTheory.IntegrableOn f1 (Set.Icc ε₀ R₀) →
    MeasureTheory.IntegrableOn f2 (Set.Icc ε₀ R₀) →
    ∫ x in Set.Icc ε₀ R₀, f1 x ≤ ∫ x in Set.Icc ε₀ R₀, f2 x := by
  intro f1 f2 h_pointwise h_int1 h_int2
  let f1' : ℝ → ℝ := (Set.Icc ε₀ R₀).indicator f1
  let f2' : ℝ → ℝ := (Set.Icc ε₀ R₀).indicator f2
  have h_f1'_eq : ∀ x, x ∉ Set.Icc ε₀ R₀ → f1' x = 0 := by
    intro x hx
    simp [f1', Set.indicator, hx]
  have h_f2'_eq : ∀ x, x ∉ Set.Icc ε₀ R₀ → f2' x = 0 := by
    intro x hx
    simp [f2', Set.indicator, hx]
  have h_f1'_le_f2' : ∀ x, x ∈ Set.Icc ε₀ R₀ → f1' x ≤ f2' x := by
    intro x hx
    simp [f1', f2', Set.indicator, hx]
    exact h_pointwise x hx
  have h_int1' : MeasureTheory.Integrable f1' MeasureTheory.volume := by
    simpa [f1'] using h_int1.integrable_indicator measurableSet_Icc
  have h_int2' : MeasureTheory.Integrable f2' MeasureTheory.volume := by
    simpa [f2'] using h_int2.integrable_indicator measurableSet_Icc
  have h_integral1 :
      ∫ x in Set.Icc ε₀ R₀, f1 x = ∫ x, f1' x := by
    simpa [f1'] using
      (MeasureTheory.integral_indicator (μ := MeasureTheory.volume) (s := Set.Icc ε₀ R₀) (f := f1)
        measurableSet_Icc).symm
  have h_integral2 :
      ∫ x in Set.Icc ε₀ R₀, f2 x = ∫ x, f2' x := by
    simpa [f2'] using
      (MeasureTheory.integral_indicator (μ := MeasureTheory.volume) (s := Set.Icc ε₀ R₀) (f := f2)
        measurableSet_Icc).symm
  have h_f1'_le_f2'_global : ∀ x, f1' x ≤ f2' x := by
    intro x
    by_cases hx : x ∈ Set.Icc ε₀ R₀
    · exact h_f1'_le_f2' x hx
    · rw [h_f1'_eq x hx, h_f2'_eq x hx]
      <;> exact le_refl 0
  rw [h_integral1, h_integral2]
  exact MeasureTheory.integral_mono h_int1' h_int2' h_f1'_le_f2'_global

/-- Mellin 积分界（测试版） -/
theorem mellin_integral_bound_uniform_test (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (M : ℝ),
      (∀ x, ‖h.toFun x‖ ≤ M) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      (∀ (s : ℂ), 0 < s.re → s.re < 1 →
        ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)) := by
  intro h M h_bound h_left h_right s hs_re1 hs_re2
  -- 分情况讨论 M < 0
  by_cases hM : M < 0
  · -- 情况 1：M < 0，矛盾！
    have h1 : ∀ x, ‖h.toFun x‖ ≤ M := h_bound
    have h2 : ‖h.toFun 0‖ ≤ M := h1 0
    have h3 : 0 ≤ ‖h.toFun 0‖ := norm_nonneg _
    linarith
  · -- 情况 2：M ≥ 0
    have hM_nonneg : 0 ≤ M := by linarith
    by_cases hM0 : M = 0
    · -- 情况 2a：M = 0
      have h_h_zero : ∀ x, h.toFun x = 0 := by
        intro x
        have h1 : ‖h.toFun x‖ ≤ M := h_bound x
        rw [hM0] at h1
        have h2 : ‖h.toFun x‖ ≤ 0 := h1
        have h3 : ‖h.toFun x‖ = 0 := by linarith [norm_nonneg (h.toFun x)]
        exact norm_eq_zero.mp h3
      have h4 : melinTransform h.toTestFunction s = 0 := by
        simp [melinTransform, realIntegral, h_h_zero, TestFunction.eval]
        <;> apply MeasureTheory.integral_congr_ae
        <;> filter_upwards with x
        <;> simp [h_h_zero]
      rw [hM0]
      rw [h4]
      <;> simp
    · -- 情况 2b：M > 0
      have hM_pos : 0 < M := by
        by_contra h
        have : M = 0 := by linarith
        exact hM0 this
      -- Step 1: 把积分限制在 [ε₀, R₀] 上
      have h1 : melinTransform h.toTestFunction s =
          ∫ x in Set.Icc ε₀ R₀, (h.toFun x) * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
        rw [melinTransform, realIntegral]
        have h_eval : ∀ x, h.toTestFunction.eval x = h.toFun x := by
          intro x
          rfl
        have h_support_fun : ∀ x, x ∉ Set.Icc ε₀ R₀ → h.toFun x = 0 := by
          intro x hx
          by_cases h : x < ε₀
          · exact h_left x h
          · have h' : x > R₀ := by
              by_contra h''
              have h''': ε₀ ≤ x ∧ x ≤ R₀ := by
                exact ⟨by linarith, by linarith⟩
              exact hx (by exact ⟨h'''.1, h'''.2⟩)
            exact h_right x h'
        have h_support : ∀ x, x ∉ Set.Icc ε₀ R₀ →
            h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
          intro x hx
          rw [h_support_fun x hx, zero_mul]
        have hzero_Ioi : ∀ x, x ∉ Set.Ioi (0 : ℝ) →
            h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
          intro x hx
          apply h_support
          intro hxIcc
          exact hx (lt_of_lt_of_le hε₀_pos hxIcc.1)
        have h_fun_eq : ∀ x ∈ Set.Ioi (0 : ℝ),
            (if 0 < x then h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
            h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
          intro x hx
          have hx' : 0 < x := hx
          have h_if : (if 0 < x then h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
              h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
            rw [if_pos hx']
          rw [h_if, h_eval x]
        calc
          (∫ x in Set.Ioi (0 : ℝ),
              if 0 < x then
                h.toTestFunction.eval x *
                  Complex.exp ((s - 1) * (Real.log x : ℂ))
              else 0)
            = ∫ x in Set.Ioi (0 : ℝ),
                h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              exact h_fun_eq
          _ = ∫ x,
                h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) :=
              MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_Ioi
          _ = ∫ x in Set.Icc ε₀ R₀,
                h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) :=
              (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_support).symm
      -- Step 2: 用三角不等式
      have h2 : ‖melinTransform h.toTestFunction s‖ ≤
          ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
        rw [h1]
        have h_mul_norm : ∀ x ∈ Set.Icc ε₀ R₀,
            ‖(h.toFun x) * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
            ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
          intro x hx
          rw [norm_mul]
        have h_norm_integral : ‖∫ x in Set.Icc ε₀ R₀, (h.toFun x) * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ ≤
            ∫ x in Set.Icc ε₀ R₀, ‖(h.toFun x) * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
          exact?
        have h_eq_integral : ∫ x in Set.Icc ε₀ R₀, ‖(h.toFun x) * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
            ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          intro x hx
          exact h_mul_norm x hx
        rw [h_eq_integral] at h_norm_integral
        exact h_norm_integral
      -- Step 3: 计算 |x^{s-1}| = x^{s.re - 1}
      have h3 : ∀ x ∈ Set.Icc ε₀ R₀, ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ = x^(s.re - 1) := by
        intro x hx
        have hx_pos : 0 < x := by linarith [Set.mem_Icc.mp hx]
        have h_exp_norm : ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ = Real.exp (((s - 1) * (Real.log x : ℂ)).re) := by
          rw [Complex.norm_exp]
        rw [h_exp_norm]
        have h_re : ((s - 1) * (Real.log x : ℂ)).re = (s.re - 1) * Real.log x := by
          simp [Complex.mul_re, Complex.ofReal_re]
          <;> ring
        rw [h_re]
        have h_rpow : Real.exp ((s.re - 1) * Real.log x) = x^(s.re - 1) := by
          rw [Real.rpow_def_of_pos hx_pos]
          <;> ring
        rw [h_rpow]
      -- Step 4: 用 h 的界
      have h4 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x‖ ≤ M := by
        intro x hx
        exact h_bound x
      -- Step 5: 可测性
      have h_meas : Measurable h.toFun := h.measurable
      have h_meas1 : Measurable (fun x : ℝ => ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖) := by
        fun_prop
      have h_meas2 : Measurable (fun x : ℝ => M * x^(s.re - 1)) := by
        fun_prop
      -- Step 6: 有界性
      have h_x_bound : ∀ x ∈ Set.Icc ε₀ R₀, x^(s.re - 1) ≤ ε₀^(s.re - 1) := by
        intro x hx
        have hx_pos : 0 < x := by linarith [Set.mem_Icc.mp hx]
        have hε₀_pos' : 0 < ε₀ := hε₀_pos
        have h_le : ε₀ ≤ x := (Set.mem_Icc.mp hx).1
        have h_neg : s.re - 1 < 0 := by linarith
        exact?
      have h_C_pos : 0 < M * ε₀^(s.re - 1) := by
        apply mul_pos hM_pos
        apply Real.rpow_pos_of_pos hε₀_pos
      have h_bdd1 : ∃ (C : ℝ), 0 < C ∧ ∀ x ∈ Set.Icc ε₀ R₀, |(‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖)| ≤ C := by
        refine ⟨M * ε₀^(s.re - 1), h_C_pos, ?_⟩
        intro x hx
        have hx_pos : 0 < x := by linarith [Set.mem_Icc.mp hx]
        have h5 : ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ = ‖h.toFun x‖ * x^(s.re - 1) := by
          rw [h3 x hx]
        rw [h5]
        have h6 : ‖h.toFun x‖ ≤ M := h4 x hx
        have h7 : 0 ≤ x := by linarith [Set.mem_Icc.mp hx]
        have h8 : 0 ≤ x^(s.re - 1) := Real.rpow_nonneg h7 _
        have h9 : ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := mul_le_mul_of_nonneg_right h6 h8
        have h10 : M * x^(s.re - 1) ≤ M * ε₀^(s.re - 1) := mul_le_mul_of_nonneg_left (h_x_bound x hx) hM_nonneg
        have h11 : |‖h.toFun x‖ * x^(s.re - 1)| = ‖h.toFun x‖ * x^(s.re - 1) := by
          rw [abs_of_nonneg]
          exact mul_nonneg (norm_nonneg _) h8
        rw [h11]
        exact le_trans h9 h10
      have h_bdd2 : ∃ (C : ℝ), 0 < C ∧ ∀ x ∈ Set.Icc ε₀ R₀, |(M * x^(s.re - 1))| ≤ C := by
        refine ⟨M * ε₀^(s.re - 1), h_C_pos, ?_⟩
        intro x hx
        have hx_pos : 0 < x := by linarith [Set.mem_Icc.mp hx]
        have h7 : 0 ≤ x := by linarith [Set.mem_Icc.mp hx]
        have h8 : 0 ≤ x^(s.re - 1) := Real.rpow_nonneg h7 _
        have h6 : |M * x^(s.re - 1)| = M * x^(s.re - 1) := by
          rw [abs_of_nonneg]
          exact mul_nonneg hM_nonneg h8
        rw [h6]
        have h7 : M * x^(s.re - 1) ≤ M * ε₀^(s.re - 1) := mul_le_mul_of_nonneg_left (h_x_bound x hx) hM_nonneg
        exact h7
      -- Step 7: 可积性
      let f1 : ℝ → ℝ := fun x => ‖h.toFun x‖ * ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖
      let f2 : ℝ → ℝ := fun x => M * x^(s.re - 1)
      have h_pointwise : ∀ x ∈ Set.Icc ε₀ R₀, f1 x ≤ f2 x := by
        intro x hx
        have h5 : f1 x = ‖h.toFun x‖ * x^(s.re - 1) := by
          simpa [f1, h3 x hx] using rfl
        rw [h5]
        have h6 : ‖h.toFun x‖ ≤ M := h4 x hx
        have h7 : 0 ≤ x := by linarith [Set.mem_Icc.mp hx]
        have h8 : 0 ≤ x^(s.re - 1) := Real.rpow_nonneg h7 _
        exact mul_le_mul_of_nonneg_right h6 h8
      have h_int1 : MeasureTheory.IntegrableOn f1 (Set.Icc ε₀ R₀) :=
        integrableOn_bdd ε₀ R₀ hε₀_pos hε₀_lt_R₀ _ h_meas1 h_bdd1
      have h_int2 : MeasureTheory.IntegrableOn f2 (Set.Icc ε₀ R₀) :=
        integrableOn_bdd ε₀ R₀ hε₀_pos hε₀_lt_R₀ _ h_meas2 h_bdd2
      -- Step 8: 积分单调性（用 test_indicator 定理）
      have h5 : ∫ x in Set.Icc ε₀ R₀, f1 x ≤ ∫ x in Set.Icc ε₀ R₀, f2 x :=
        test_indicator ε₀ R₀ hε₀_pos hε₀_lt_R₀ f1 f2 h_pointwise h_int1 h_int2
      -- Step 9: 最后的结论
      have h6 : ‖melinTransform h.toTestFunction s‖ ≤ ∫ x in Set.Icc ε₀ R₀, f2 x := by
        calc
          ‖melinTransform h.toTestFunction s‖ ≤ ∫ x in Set.Icc ε₀ R₀, f1 x := h2
          _ ≤ ∫ x in Set.Icc ε₀ R₀, f2 x := h5
      sorry
