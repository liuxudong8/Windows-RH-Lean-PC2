import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.test_rpow_ineq

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
    sorry
  calc
    ‖∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖
      ≤ ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := h2
    _ = ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) := by
      sorry
    _ ≤ ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) := h5
    _ = M * ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) := h6
    _ = M * ((R₀^s.re - ε₀^s.re) / s.re) := by rw [h7]
    _ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
      sorry
