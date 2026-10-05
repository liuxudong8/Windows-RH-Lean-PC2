import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 测试：∑ (k+1)^2 / 2^k 收敛
lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h : ∀ (k : ℕ), ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ 4 * (3 / 4 : ℝ)^k := by
    intro k
    have h1 : (k : ℝ) + 1 ≤ 2 * (3 / 2 : ℝ)^k := by
      induction k with
      | zero => norm_num
      | succ k ih =>
        simp [pow_succ] at * <;> nlinarith
    have h2 : ((k : ℝ) + 1)^2 ≤ 4 * (9 / 4 : ℝ)^k := by
      have h3 : ((k : ℝ) + 1)^2 ≤ (2 * (3 / 2 : ℝ)^k)^2 := by gcongr
      have h4 : (2 * (3 / 2 : ℝ)^k)^2 = 4 * (9 / 4 : ℝ)^k := by
        have h5 : (3 / 2 : ℝ)^(2 * k) = (9 / 4 : ℝ)^k := by
          have h6 : (3 / 2 : ℝ)^(2 * k) = ((3 / 2 : ℝ)^2)^k := by rw [pow_mul]
          rw [h6]; ring_nf
        simp [h5] <;> ring
      linarith
    have h5 : 4 * (9 / 4 : ℝ)^k / (2 : ℝ)^k = 4 * (9 / 8 : ℝ)^k := by
      have h6 : (9 / 4 : ℝ)^k / (2 : ℝ)^k = (9 / 8 : ℝ)^k := by
        rw [← div_pow] <;> ring
      rw [h6] <;> ring
    calc ((k : ℝ) + 1)^2 / (2 : ℝ)^k
      ≤ 4 * (9 / 4 : ℝ)^k / (2 : ℝ)^k := by gcongr
      _ = 4 * (9 / 8 : ℝ)^k := h5
      _ ≤ 4 * (3 / 4 : ℝ)^k := by
        have h7 : (9 / 8 : ℝ)^k ≤ (3 / 4 : ℝ)^k := by
          apply pow_le_pow_of_le_one
          <;> norm_num
        gcongr
  have h_summable : Summable (fun (k : ℕ) => 4 * (3 / 4 : ℝ)^k) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one
    <;> norm_num
  exact Summable.of_nonneg_of_le (fun k => by positivity) h h_summable

#check summable_quadratic_over_geometric

end RHSpectralDuality
