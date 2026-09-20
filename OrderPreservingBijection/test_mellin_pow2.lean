import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。 -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (by gcongr <;> linarith)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
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
  simp [Complex.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm, pow_succ]
  <;> ring

end RHSpectralDuality
end OrderPreservingBijection
