import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 精确求和公式：∑_{i=0}^{n-1} (i+1)^2 / 2^i = 12 - (n^2 + 4n + 6) / 2^(n-1)
lemma sum_quadratic_geometric_formula (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) = 12 - ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^(n - 1) := by
  induction n with
  | zero =>
    simp [Finset.sum_range_zero]
    <;> norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    cases n with
    | zero => norm_num
    | succ n' =>
      simp [pow_succ, Nat.cast_add, Nat.cast_one]
      <;> field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_nonneg : ∀ (k : ℕ), 0 ≤ ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by intro k; positivity
  have h_bounded : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) ≤ 12 := by
    intro n
    have h_formula := sum_quadratic_geometric_formula n
    rw [h_formula]
    have h_pos : 0 ≤ ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^(n - 1) := by positivity
    linarith
  exact summable_of_sum_range_le h_nonneg 12 h_bounded

#check summable_quadratic_over_geometric

end RHSpectralDuality
