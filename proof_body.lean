  intro s hs_re1 hs_re2
  set f : ℝ → ℂ := fun x => (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) with hf_def
  have h_s_ne_zero : s ≠ 0 := by
    intro h; rw [h] at hs_re1; norm_num at hs_re1
  have h_s1_ne_zero : s + 1 ≠ 0 := by
    intro h
    have hz : (s + 1).re = 0 := by rw [h]; norm_num
    simp [Complex.add_re] at hz; linarith [hs_re1]
  have h_int : MeasureTheory.IntegrableOn f (Set.Icc ε₀ R₀) := by admit
  have h_mellin_eq : melinTransform h.toTestFunction s = (1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x := by admit
  have h10b : ‖∫ x in Set.Icc ε₀ R₀, f x‖ ≤ ∫ x in Set.Icc ε₀ R₀, ‖f x‖ := by exact?
  have h_norm3 : ∀ x ∈ Set.Icc ε₀ R₀, ‖f x‖ = ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
    intro x hx
    have hx_pos : 0 < x := by have : ε₀ ≤ x := hx.1; linarith [hε₀_pos]
    simp only [hf_def]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx_pos] <;> rfl
  have h_norm4 : ∫ x in Set.Icc ε₀ R₀, ‖f x‖ = ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx; exact h_norm3 x hx
  have h_norm5 : ‖(1:ℂ)/(s*(s+1))‖ = 1/(‖s‖*‖s+1‖) := by
    simp [norm_div, norm_mul, h_s_ne_zero, h_s1_ne_zero] <;> field_simp [h_s_ne_zero, h_s1_ne_zero] <;> ring
  have h10c : ‖(1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x‖ ≤
      1/(‖s‖*‖s+1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
    have h_eq1 : ‖(1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x‖ =
        ‖(1:ℂ)/(s*(s+1))‖ * ‖∫ x in Set.Icc ε₀ R₀, f x‖ := by rw [norm_mul]
    rw [h_eq1, h_norm5]
    rw [h_norm4] at h10b
    exact mul_le_mul_of_nonneg_left h10b (by positivity)
  have h_s2_ne_zero : s.re + 2 ≠ 0 := by linarith
  have h8 := mellin_rapid_decay_step4 h s ε₀ R₀ hε₀_pos hε₀_lt_R₀ B' hB hC2 h_s2_ne_zero hs_re1
  have h8' : 1/(‖s‖*‖s+1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) ≤
      1/(‖s‖*‖s+1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := by
    exact mul_le_mul_of_nonneg_left h8 (by positivity)
  have h9 : 1/(‖s‖*‖s+1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) ≤
      8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by admit
  have h10 : ‖(1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 :=
    le_trans h10c (le_trans h8' h9)
  rw [h_mellin_eq]
  exact h10
