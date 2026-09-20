import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- exp(z) = 1 ⟹ z.re = 0。 -/
theorem exp_eq_one_implies_re_zero (z : ℂ) (h : Complex.exp z = 1) : z.re = 0 := by
  have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
  have h_im : (Complex.exp z).im = 0 := by rw [h] <;> simp
  have h1 : Real.exp z.re * Real.cos z.im = 1 := by simpa [Complex.exp_re] using h_re
  have h2 : Real.exp z.re * Real.sin z.im = 0 := by simpa [Complex.exp_im] using h_im
  have h_exp_pos : 0 < Real.exp z.re := Real.exp_pos z.re
  have h_sin : Real.sin z.im = 0 := by
    apply (mul_eq_zero.mp h2).resolve_left
    exact ne_of_gt h_exp_pos
  have h_cos_sq : Real.cos z.im ^ 2 = 1 := by
    have h3 : Real.cos z.im ^ 2 + Real.sin z.im ^ 2 = 1 := Real.cos_sq_add_sin_sq z.im
    rw [h_sin] at h3 <;> linarith
  have h_cos : Real.cos z.im = 1 ∨ Real.cos z.im = -1 := by
    have h4 : (Real.cos z.im - 1) * (Real.cos z.im + 1) = 0 := by linarith
    have h5 : Real.cos z.im - 1 = 0 ∨ Real.cos z.im + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    rcases h5 with (h5 | h5)
    · left; linarith
    · right; linarith
  rcases h_cos with (h_cos1 | h_cos2)
  · have h6 : Real.exp z.re = 1 := by rw [h_cos1] at h1 <;> linarith
    have h7 : z.re = 0 := by
      have h8 : Real.exp z.re = Real.exp 0 := by rw [h6] <;> simp
      exact Real.exp_injective h8
    exact h7
  · rw [h_cos2] at h1
    have h6 : Real.exp z.re = -1 := by linarith
    have h7 : 0 < Real.exp z.re := h_exp_pos
    linarith

/-- exp(z) = 1 ⟹ ∃ k : ℤ, z.im = 2 * π * k。 -/
theorem exp_eq_one_implies_im_int (z : ℂ) (h : Complex.exp z = 1) :
    ∃ (k : ℤ), z.im = 2 * Real.pi * (k : ℝ) := by
  have h_re0 : z.re = 0 := exp_eq_one_implies_re_zero z h
  have h_cos1 : Real.cos z.im = 1 := by
    have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
    simpa [Complex.exp_re, h_re0] using h_re
  rw [Real.cos_eq_one_iff z.im] at h_cos1
  rcases h_cos1 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith

/-- 对 c ≠ 0，集合 {t : ℝ // exp(c * t) = 1} 是可数的。 -/
theorem exp_c_t_eq_one_set_countable (c : ℂ) (hc : c ≠ 0) :
    Set.Countable {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} := by
  have h_main : {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} ⊆
      Set.range (fun (k : ℤ) => ((2 * Real.pi * (k : ℝ)) * Complex.I / c).re) := by
    intro t ht
    have h2 : ∃ (k : ℤ), (c * (t : ℂ)).im = 2 * Real.pi * (k : ℝ) :=
      exp_eq_one_implies_im_int (c * (t : ℂ)) ht
    rcases h2 with ⟨k, hk⟩
    have h_re0 : (c * (t : ℂ)).re = 0 := exp_eq_one_implies_re_zero (c * (t : ℂ)) ht
    have h3 : c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := by
      apply Complex.ext
      · simpa using h_re0
      · simpa using hk
    have h4 : (t : ℂ) = ((2 * Real.pi * (k : ℝ)) * Complex.I) / c := by
      apply (mul_right_inj' hc).mp
      calc
        c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := h3
        _ = c * (((2 * Real.pi * (k : ℝ)) * Complex.I) / c) := by
          field_simp [hc] <;> ring
    have h5 : t = (((2 * Real.pi * (k : ℝ)) * Complex.I) / c).re := by
      exact_mod_cast congr_arg Complex.re h4
    exact ⟨k, by simp [h5]⟩
  exact Set.Countable.mono h_main (Set.countable_range _)

/-- (0, ∞) 不可数：Real.log '' (0,∞) = ℝ，若 (0,∞) 可数则 ℝ 可数，矛盾。 -/
theorem positive_reals_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := by
  intro h
  have h_image : Set.Countable (Real.log '' (Set.Ioi (0 : ℝ))) := Set.Countable.image h Real.log
  have h_eq : Real.log '' (Set.Ioi (0 : ℝ)) = (Set.univ : Set ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    refine ⟨Real.exp y, ?_, ?_⟩
    · have h_pos : 0 < Real.exp y := Real.exp_pos y
      exact h_pos
    · rw [Real.log_exp]
  rw [h_eq] at h_image
  have h_contra : Set.Countable (Set.univ : Set ℝ) := h_image
  have h_real_uncountable : ¬ Set.Countable (Set.univ : Set ℝ) := by exact?
  exact h_real_uncountable h_contra

/-- 存在性定理：对任意 s₁ ≠ s₂, s₁ ≠ 0, s₂ ≠ 0，存在 a > 1 使
    a^s₁ ≠ 1, a^s₂ ≠ 1, a^s₁ ≠ a^s₂。 -/
theorem exists_base_for_two_points (s1 s2 : ℂ) (h_ne : s1 ≠ s2) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) :
    ∃ (a : ℝ), 1 < a ∧
      Complex.exp (s1 * (Real.log a : ℂ)) ≠ 1 ∧
      Complex.exp (s2 * (Real.log a : ℂ)) ≠ 1 ∧
      Complex.exp (s1 * (Real.log a : ℂ)) ≠ Complex.exp (s2 * (Real.log a : ℂ)) := by
  have hc3 : s1 - s2 ≠ 0 := by
    intro h
    have h1 : s1 = s1 - s2 + s2 := by ring
    have h' : s1 = s2 := by
      rw [h1, h] <;> ring
    exact h_ne h'
  have hS1 : Set.Countable {t : ℝ | Complex.exp (s1 * (t : ℂ)) = 1} := exp_c_t_eq_one_set_countable s1 hs1
  have hS2 : Set.Countable {t : ℝ | Complex.exp (s2 * (t : ℂ)) = 1} := exp_c_t_eq_one_set_countable s2 hs2
  have hS3 : Set.Countable {t : ℝ | Complex.exp ((s1 - s2) * (t : ℂ)) = 1} := exp_c_t_eq_one_set_countable (s1 - s2) hc3
  set S : Set ℝ := {t : ℝ | Complex.exp (s1 * (t : ℂ)) = 1} ∪ {t : ℝ | Complex.exp (s2 * (t : ℂ)) = 1} ∪ {t : ℝ | Complex.exp ((s1 - s2) * (t : ℂ)) = 1} with hS_eq
  have hUnion : Set.Countable S := Set.Countable.union (Set.Countable.union hS1 hS2) hS3
  have h_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := positive_reals_uncountable
  have h_exists : ∃ (t : ℝ), t ∈ Set.Ioi (0 : ℝ) ∧ t ∉ S := by
    by_contra h
    push_neg at h
    have h_sub : Set.Ioi (0 : ℝ) ⊆ S := fun t ht => h t ht
    have h_contra : Set.Countable (Set.Ioi (0 : ℝ)) := Set.Countable.mono h_sub hUnion
    exact h_uncountable h_contra
  rcases h_exists with ⟨t, ht_pos, ht_notin⟩
  have h_t_pos' : 0 < t := ht_pos
  have ht_notin1 : t ∉ S := ht_notin
  rw [hS_eq] at ht_notin1
  simp at ht_notin1
  have ht_notin' : ¬(Complex.exp (s1 * (t : ℂ)) = 1 ∨ Complex.exp (s2 * (t : ℂ)) = 1 ∨ Complex.exp ((s1 - s2) * (t : ℂ)) = 1) := by
    tauto
  let a : ℝ := Real.exp t
  have ha_gt_one : 1 < a := by
    have h2 : Real.exp t > Real.exp 0 := Real.exp_strictMono h_t_pos'
    have h3 : Real.exp 0 = 1 := by simp
    rw [h3] at h2
    exact h2
  have h_log_a : Real.log a = t := by
    have h4 : a = Real.exp t := rfl
    rw [h4]
    exact Real.log_exp t
  have h_notin1 : ¬(Complex.exp (s1 * (t : ℂ)) = 1) := by
    intro h
    have h' : Complex.exp (s1 * (t : ℂ)) = 1 ∨ Complex.exp (s2 * (t : ℂ)) = 1 ∨ Complex.exp ((s1 - s2) * (t : ℂ)) = 1 := Or.inl h
    exact ht_notin' h'
  have h_notin2 : ¬(Complex.exp (s2 * (t : ℂ)) = 1) := by
    intro h
    have h' : Complex.exp (s1 * (t : ℂ)) = 1 ∨ Complex.exp (s2 * (t : ℂ)) = 1 ∨ Complex.exp ((s1 - s2) * (t : ℂ)) = 1 := Or.inr (Or.inl h)
    exact ht_notin' h'
  have h_notin3 : ¬(Complex.exp ((s1 - s2) * (t : ℂ)) = 1) := by
    intro h
    have h' : Complex.exp (s1 * (t : ℂ)) = 1 ∨ Complex.exp (s2 * (t : ℂ)) = 1 ∨ Complex.exp ((s1 - s2) * (t : ℂ)) = 1 := Or.inr (Or.inr h)
    exact ht_notin' h'
  have h1 : Complex.exp (s1 * (Real.log a : ℂ)) ≠ 1 := by
    rw [h_log_a]
    exact h_notin1
  have h2 : Complex.exp (s2 * (Real.log a : ℂ)) ≠ 1 := by
    rw [h_log_a]
    exact h_notin2
  have h3 : Complex.exp (s1 * (Real.log a : ℂ)) ≠ Complex.exp (s2 * (Real.log a : ℂ)) := by
    rw [h_log_a]
    intro h_eq
    have h41 : (s1 - s2) * (t : ℂ) = s1 * (t : ℂ) - s2 * (t : ℂ) := by ring
    have h42 : Complex.exp ((s1 - s2) * (t : ℂ)) = Complex.exp (s1 * (t : ℂ)) * Complex.exp (-(s2 * (t : ℂ))) := by
      rw [h41, ← Complex.exp_add] <;> ring
    have h43 : Complex.exp (-(s2 * (t : ℂ))) = (Complex.exp (s2 * (t : ℂ)))⁻¹ := by
      rw [Complex.exp_neg]
    have h4 : Complex.exp ((s1 - s2) * (t : ℂ)) = 1 := by
      rw [h42, h43]
      rw [h_eq]
      <;> field_simp
      <;> ring
    exact h_notin3 h4
  exact ⟨a, ha_gt_one, h1, h2, h3⟩

end RHSpectralDuality
end OrderPreservingBijection
