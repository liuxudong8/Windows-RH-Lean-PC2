import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 核心引理：Complex.exp z = 1 ⟹ z.re = 0。 -/
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
    rw [h_sin] at h3
    <;> linarith
  have h_cos : Real.cos z.im = 1 ∨ Real.cos z.im = -1 := by
    have h4 : Real.cos z.im ^ 2 - 1 = 0 := by linarith
    have h5 : (Real.cos z.im - 1) * (Real.cos z.im + 1) = 0 := by linarith
    have h6 : Real.cos z.im - 1 = 0 ∨ Real.cos z.im + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h5
    rcases h6 with (h6 | h6)
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

/-- 推论：2^s = 1 ⟹ s.re = 0。 -/
theorem two_pow_s_eq_one_implies_re_zero (s : ℂ) (h : Complex.exp (s * (Real.log 2 : ℂ)) = 1) : s.re = 0 := by
  have h1 : (s * (Real.log 2 : ℂ)).re = 0 := exp_eq_one_implies_re_zero (s * (Real.log 2 : ℂ)) h
  have h2 : (s * (Real.log 2 : ℂ)).re = s.re * Real.log 2 := by
    have h_re : ∀ (z w : ℂ), (z * w).re = z.re * w.re - z.im * w.im := by intro z w; rfl
    rw [h_re s (Real.log 2 : ℂ)]
    have h3 : ((Real.log 2 : ℂ).re) = Real.log 2 := by exact?
    have h4 : ((Real.log 2 : ℂ).im) = 0 := by exact?
    rw [h3, h4] <;> ring
  rw [h2] at h1
  have h_log2_pos : 0 < Real.log 2 := by apply Real.log_pos; norm_num
  have h3 : s.re = 0 := by
    apply (mul_eq_zero.mp h1).resolve_right
    exact ne_of_gt h_log2_pos
  exact h3

/-- ζ 非平凡零点满足 2^s ≠ 1。 -/
theorem zeta_nontrivial_zero_two_pow_ne_one (ρ : ℂ) (hz : _root_.riemannZeta ρ = 0)
    (hre1 : 0 < ρ.re) (hre2 : ρ.re < 1) : Complex.exp (ρ * (Real.log 2 : ℂ)) ≠ 1 := by
  intro h
  have h4 : ρ.re = 0 := two_pow_s_eq_one_implies_re_zero ρ h
  linarith

end RHSpectralDuality
end OrderPreservingBijection
