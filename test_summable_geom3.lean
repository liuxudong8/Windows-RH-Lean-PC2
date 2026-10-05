import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 引理：∀ k ≥ 14, (k+1)^2 ≤ (3/2)^k
lemma poly_le_geometric (k : ℕ) (h : k ≥ 14) : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := by
  induction' h with k h ih
  · norm_num
  · have h1 : ((k.succ : ℝ) + 1)^2 = ((k : ℝ) + 2)^2 := by simp [Nat.cast_add] <;> ring
    rw [h1]
    have h2 : ((k : ℝ) + 2)^2 ≤ (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 := by
      have h3 : (k : ℝ) ≥ 14 := by exact_mod_cast h
      nlinarith
    have h4 : (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ) * (3 / 2 : ℝ)^k := by gcongr
    have h5 : (3 / 2 : ℝ) * (3 / 2 : ℝ)^k = (3 / 2 : ℝ)^(k + 1) := by
      rw [← pow_succ] <;> ring
    rw [h5] at h4; exact le_trans h2 h4

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  -- 对 k ≥ 14, (k+1)^2 / 2^k ≤ (3/4)^k
  have h_bound : ∀ (k : ℕ), k ≥ 14 → ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ (3 / 4 : ℝ)^k := by
    intro k hk
    have h1 : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := poly_le_geometric k hk
    have h2 : ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ (3 / 2 : ℝ)^k / (2 : ℝ)^k := by gcongr
    have h3 : (3 / 2 : ℝ)^k / (2 : ℝ)^k = (3 / 4 : ℝ)^k := by
      rw [← div_pow] <;> ring
    rw [h3] at h2; exact h2
  -- 前 14 项是有限的，不影响收敛性
  have h_main : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
    apply Summable.of_eventually_le (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    · intro k; positivity
    · filter_upwards [Ici_mem_atTop 14] with k hk
      exact h_bound k hk
  exact h_main

#check summable_quadratic_over_geometric

end RHSpectralDuality
