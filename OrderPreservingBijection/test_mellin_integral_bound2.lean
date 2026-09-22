import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.test_rpow_ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open OrderPreservingBijection

noncomputable section

/-- 测试 Mellin 积分界 -/
theorem test_mellin_integral_bound (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (M : ℝ),
      (∀ x, ‖h.toFun x‖ ≤ M) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      (∀ (s : ℂ), 0 < s.re → s.re < 1 →
        ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)) := by
  intro h M h_bound h_left h_right s hs_re1 hs_re2
  -- 第一步：把 Mellin 变换的积分限制到 [ε₀, R₀]
  have h1 : melinTransform h.toTestFunction s =
      ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
    have h_eval : ∀ x, h.toTestFunction.eval x = h.toFun x := by
      intro x
      rfl
    have h_support_fun : ∀ x, x ∉ Set.Icc ε₀ R₀ → h.toFun x = 0 := by
      intro x hx
      by_cases h : x < ε₀
      · exact h_left x h
      · by_cases h2 : x > R₀
        · exact h_right x h2
        · have h3 : x ∈ Set.Icc ε₀ R₀ := by
            simpa [Set.mem_Icc] using ⟨by linarith, by linarith⟩
          exact False.elim (hx h3)
    have h_support : ∀ x, x ∉ Set.Icc ε₀ R₀ →
        h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
      intro x hx
      rw [h_support_fun x hx, zero_mul]
    have hzero_Ioi : ∀ x, x ∉ Set.Ioi (0 : ℝ) →
        h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
      intro x hx
      have h_x_nonpos : x ≤ 0 := by
        simpa [Set.mem_Ioi] using hx
      have h_x_not_in_Icc : x ∉ Set.Icc ε₀ R₀ := by
        intro h
        have h_x_pos : 0 < x := by linarith [h.1, hε₀_pos]
        linarith
      exact h_support x h_x_not_in_Icc
    have h_eq1 : melinTransform h.toTestFunction s =
        ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      simp [melinTransform, realIntegral, h_eval]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := hx
      simp [hx', h_eval x]
    have h_eq2 : ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_Ioi
    have h_eq3 : ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_support).symm
    calc
      melinTransform h.toTestFunction s
        = ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq1
      _ = ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq2
      _ = ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq3
  rw [h1]
  -- 第二步：用三角不等式
  have h2 : ‖∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ ≤
      ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  -- 第三步：化简范数
  have h3 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
      ‖h.toFun x‖ * x^(s.re - 1) := by
    intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have h31 : ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ = x^(s.re - 1) := by
      have h311 : ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
          Real.exp (((s - 1) * (Real.log x : ℂ)).re) := by
        exact?
      rw [h311]
      have h312 : ((s - 1) * (Real.log x : ℂ)).re = (s.re - 1) * Real.log x := by
        simp [Complex.mul_re, Complex.add_re]
        <;> ring
      rw [h312]
      have h313 : Real.exp ((s.re - 1) * Real.log x) = x^(s.re - 1) := by
        have h_comm : (s.re - 1) * Real.log x = Real.log x * (s.re - 1) := by ring
        rw [h_comm]
        rw [Real.exp_mul]
        rw [Real.exp_log hx_pos]
        <;> ring
      exact h313
    rw [norm_mul, h31]
  -- 第四步：用 h_bound
  have h4 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x‖ ≤ M := by
    intro x hx
    exact h_bound x
  -- 第五步：积分单调性
  have h51 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := by
    intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have h_nonneg : 0 ≤ x^(s.re - 1) := by
      apply Real.rpow_nonneg
      linarith
    have h_bound' : ‖h.toFun x‖ ≤ M := h4 x hx
    have h' : ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := by
      exact mul_le_mul_of_nonneg_right h_bound' h_nonneg
    exact h'
  have h_le : ε₀ ≤ R₀ := by linarith
  have h_cont_pow : ContinuousOn (fun x : ℝ => x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    apply ContinuousOn.rpow
    · exact continuousOn_id
    · exact continuousOn_const
    · intro x hx
      have h_eps_le_x : ε₀ ≤ x := hx.1
      have h_pos_eps : 0 < ε₀ := hε₀_pos
      have h_ne_zero : x ≠ 0 := by linarith
      exact Or.inl h_ne_zero
  have h1_int : MeasureTheory.IntegrableOn (fun x : ℝ => ‖h.toFun x‖ * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    sorry
  have h2_int : MeasureTheory.IntegrableOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    have h_g_cont : ContinuousOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
      apply ContinuousOn.mul continuousOn_const h_cont_pow
    have h : MeasureTheory.IntegrableOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
      exact?
    exact h
  have h5 : ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) ≤
      ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) := by
    exact MeasureTheory.setIntegral_mono_on h1_int h2_int measurableSet_Icc h51
  -- 第六步：把常数 M 提出来
  have h6 : ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) =
      M * ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) := by
    exact MeasureTheory.integral_const_mul M _
  -- 第七步：计算积分 ∫_{ε₀}^{R₀} x^(σ-1) dx
  have h7 : ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) = (R₀^s.re - ε₀^s.re) / s.re := by
    have h_le : ε₀ ≤ R₀ := by linarith
    have h_deriv : ∀ x ∈ Set.uIcc ε₀ R₀,
        HasDerivAt (fun y : ℝ => y^s.re / s.re) (x^(s.re - 1)) x := by
      intro x hx
      have hx_in_Icc : x ∈ Set.Icc ε₀ R₀ := by
        rw [Set.uIcc_of_le h_le] at hx
        exact hx
      have hx_pos : 0 < x := by linarith [hx_in_Icc.1]
      have h1 : HasDerivAt (fun y : ℝ => y^s.re) (s.re * x^(s.re - 1)) x := by
        have h1' : HasDerivAt (fun x : ℝ => id x ^ s.re)
            (1 * s.re * id x ^ (s.re - 1) + 0 * id x ^ s.re * Real.log (id x)) x := by
          exact HasDerivAt.rpow (hasDerivAt_id x) (hasDerivAt_const x s.re) hx_pos
        have h_eq1 : (fun x : ℝ => id x ^ s.re) = (fun y : ℝ => y ^ s.re) := by
          funext y
          rfl
        have h_eq2 : (1 * s.re * id x ^ (s.re - 1) + 0 * id x ^ s.re * Real.log (id x)) = s.re * x ^ (s.re - 1) := by
          simp [mul_zero, zero_add, one_mul]
          <;> ring
        rw [h_eq1, h_eq2] at h1'
        exact h1'
      have h2 : HasDerivAt (fun y : ℝ => y^s.re / s.re) ((s.re * x^(s.re - 1)) / s.re) x := by
        exact h1.div_const (s.re : ℝ)
      have h3 : (s.re * x^(s.re - 1)) / s.re = x^(s.re - 1) := by
        field_simp [hs_re1.ne'] <;> ring
      rw [h3] at h2
      exact h2
    have h_interval_integrable : IntervalIntegrable (fun x : ℝ => x^(s.re - 1)) MeasureTheory.volume ε₀ R₀ := by
      exact ContinuousOn.intervalIntegrable_of_Icc h_le h_cont_pow
    have h_eq2 : ∫ x in ε₀..R₀, x^(s.re - 1) =
        (R₀^s.re / s.re) - (ε₀^s.re / s.re) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_interval_integrable
    have h_ioc_eq_iic : ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) = ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) := by
      exact MeasureTheory.integral_Icc_eq_integral_Ioc
    have h_eq1 : ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) = ∫ x in ε₀..R₀, x^(s.re - 1) := by
      rw [intervalIntegral.integral_of_le h_le]
    calc
      ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1)
        = ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) := h_ioc_eq_iic
      _ = ∫ x in ε₀..R₀, x^(s.re - 1) := h_eq1
      _ = (R₀^s.re / s.re) - (ε₀^s.re / s.re) := h_eq2
      _ = (R₀^s.re - ε₀^s.re) / s.re := by ring
  calc
    ‖∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖
      ≤ ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := h2
    _ = ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact h3 x hx
    _ ≤ ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) := h5
    _ = M * ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) := h6
    _ = M * ((R₀^s.re - ε₀^s.re) / s.re) := by rw [h7]
    _ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ‖h.toFun (ε₀ / 2)‖ := by positivity
        have h2 : ‖h.toFun (ε₀ / 2)‖ ≤ M := h_bound (ε₀ / 2)
        linarith
      have h_ineq : (R₀^s.re - ε₀^s.re) / s.re ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
        sorry
      exact mul_le_mul_of_nonneg_left h_ineq hM_nonneg
