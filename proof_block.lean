  intro s hs_re1 hs_re2
  set f : ℝ → ℂ := fun x => (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) with hf_def
  have h_s_ne_zero : s ≠ 0 := by
    intro h; rw [h] at hs_re1; norm_num at hs_re1
  have h_s1_ne_zero : s + 1 ≠ 0 := by
    intro h; have : s.re = -1 := by exact_mod_cast (by rw [h] at * <;> norm_num at * <;> linarith); linarith
  have h_mellin_eq : melinTransform h.toTestFunction s = (1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x := by admit
  have h_int : MeasureTheory.IntegrableOn f (Set.Icc ε₀ R₀) := by admit
  have h10b : ‖∫ x in Set.Icc ε₀ R₀, f x‖ ≤ ∫ x in Set.Icc ε₀ R₀, ‖f x‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h_norm3 : ∀ x ∈ Set.Icc ε₀ R₀, ‖f x‖ = ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
    intro x hx
    have hx_pos : 0 < x := by have : ε₀ ≤ x := hx.1; linarith [hε₀_pos]
    simp only [hf_def]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx_pos] <;> ring
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
  have h9 : 1/(‖s‖*‖s+1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) ≤
      8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by
    have h10 : ‖s‖*‖s+1‖ ≥ |s.im|^2 := mellin_rapid_decay_step5 s
    have h11 : 0 ≤ B' := by linarith [hB_pos]
    have h12 : 0 ≤ R₀^(s.re + 2) - ε₀^(s.re + 2) := by gcongr <;> linarith [hε₀_pos]
    have h13 : R₀^(s.re + 2) ≤ R₀^3 + 1 := by
      have h14 : s.re + 2 ≤ 3 := by linarith
      have h15 : 0 ≤ s.re + 2 := by linarith
      by_cases hR : R₀ ≥ 1
      · have h16 : R₀^(s.re + 2) ≤ R₀^3 := by gcongr <;> linarith; exact hR
        linarith
      · have h17 : R₀^(s.re + 2) ≤ 1 := by gcongr <;> linarith [hε₀_pos, hε₀_lt_R₀] <;> norm_num; exact hR
        linarith
    have h18 : 0 < |s.im|^2 := by
      by_cases h : s.im = 0
      · rw [h] <;> norm_num
      · exact sq_pos_of_ne_zero h
    have h19 : 1/(‖s‖*‖s+1‖) ≤ 1/|s.im|^2 := by
      apply one_div_le_one_div_of_le <;> linarith
    calc
      1/(‖s‖*‖s+1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2))
        ≤ 1/|s.im|^2 * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := by gcongr
      _ ≤ 1/|s.im|^2 * (B' * (R₀^3 + 1)) := by gcongr; rw [h13] <;> linarith
      _ = B' * (R₀^3 + 1) / |s.im|^2 := by ring
      _ ≤ 8 * B' * (R₀^3 + 1) / |s.im|^2 := by
        have h20 : 0 < B' * (R₀^3 + 1) / |s.im|^2 := by positivity
        linarith
  have h10 : ‖(1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 :=
    le_trans h10c (le_trans h8 h9)
  have h_final : ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by
    rw [h_mellin_eq]
    exact h10
  exact h_final
