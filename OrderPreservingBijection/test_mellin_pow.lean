import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。 -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (by gcongr <;> linarith)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
  set v : ℂ := Complex.exp (s * (Real.log a : ℂ)) with hv_def
  have h_pos1 : 0 < a ^ i := by positivity
  have h_lt : a ^ i < a ^ (i + 1) := by
    have h2 : a ^ (i + 1) = a ^ i * a := by simp [pow_succ] <;> ring
    rw [h2]
    have h3 : 0 < a ^ i := by positivity
    nlinarith
  rw [intervalIndicator_mellinTransform (a ^ i) (a ^ (i + 1)) h_pos1 h_lt s hs]
  have h_log1 : Real.log (a ^ (i + 1)) = ((i + 1 : ℕ) : ℝ) * Real.log a := Real.log_pow a (i + 1)
  have h_log2 : Real.log (a ^ i) = (i : ℝ) * Real.log a := Real.log_pow a i
  rw [h_log1, h_log2]
  have h_eq1 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) := by
    have h5 : s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ) = ((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ)) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    have h6 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h5
    have h7 : Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) = v ^ (i + 1) := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) (i + 1)
    exact h6.trans h7
  have h_eq2 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ i := by
    have h5 : s * ((i : ℝ) * Real.log a : ℂ) = (i : ℂ) * (s * (Real.log a : ℂ)) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    have h6 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h5
    have h7 : Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) = v ^ i := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) i
    exact h6.trans h7
  have h_left : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) - v ^ i := by
    exact?
  rw [h_left]
  have h6 : v ^ (i + 1) - v ^ i = v ^ i * (v - 1) := by
    have h7 : v ^ (i + 1) = v ^ i * v := by simp [pow_succ] <;> ring
    rw [h7] <;> ring
  rw [h6] <;> ring

end RHSpectralDuality
end OrderPreservingBijection
