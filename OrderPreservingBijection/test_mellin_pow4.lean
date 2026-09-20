import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助：a > 1 时 a^i < a^(i+1)。 -/
lemma pow_lt_pow_succ (a : ℝ) (ha : 1 < a) (i : ℕ) : a ^ i < a ^ (i + 1) := by
  have h2 : a ^ (i + 1) = a ^ i * a := by simp [pow_succ] <;> ring
  rw [h2]
  have h3 : 0 < a ^ i := by positivity
  nlinarith

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。 -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (pow_lt_pow_succ a ha i)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
  set v : ℂ := Complex.exp (s * (Real.log a : ℂ)) with hv_def
  have h_pos1 : 0 < a ^ i := by positivity
  have h_lt : a ^ i < a ^ (i + 1) := pow_lt_pow_succ a ha i
  rw [intervalIndicator_mellinTransform (a ^ i) (a ^ (i + 1)) h_pos1 h_lt s hs]
  have h_log1 : Real.log (a ^ (i + 1)) = ((i + 1 : ℕ) : ℝ) * Real.log a := Real.log_pow a (i + 1)
  have h_log2 : Real.log (a ^ i) = (i : ℝ) * Real.log a := Real.log_pow a i
  rw [h_log1, h_log2]
  have h_alg1 : s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ) = ((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_alg2 : s * ((i : ℝ) * Real.log a : ℂ) = (i : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_exp1 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) := by
    have h_e : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg1
    have h_e2 : Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) = v ^ (i + 1) := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) (i + 1)
    exact h_e.trans h_e2
  have h_exp2 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ i := by
    have h_e : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg2
    have h_e2 : Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) = v ^ i := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) i
    exact h_e.trans h_e2
  have h_main : (Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))) / s = v ^ i * (v - 1) / s := by
    have h_diff : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) - v ^ i := by
      calc
        Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))
          = v ^ (i + 1) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) := by rw [h_exp1]
        _ = v ^ (i + 1) - v ^ i := by rw [h_exp2]
    rw [h_diff]
    have h6 : v ^ (i + 1) - v ^ i = v ^ i * (v - 1) := by
      have h7 : v ^ (i + 1) = v ^ i * v := by simp [pow_succ] <;> ring
      rw [h7] <;> ring
    rw [h6] <;> ring
  simpa [hv_def] using h_main

end RHSpectralDuality
end OrderPreservingBijection
