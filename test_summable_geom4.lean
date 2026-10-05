import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma poly_le_geometric (k : ℕ) (h : k ≥ 14) : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := by
  induction k with
  | zero => exfalso; linarith
  | succ k ih =>
    by_cases h' : k ≥ 14
    · -- k ≥ 14, 用归纳假设
      have h_ih' := ih h'
      have h1 : ((k.succ : ℝ) + 1)^2 = ((k : ℝ) + 2)^2 := by simp [Nat.cast_add] <;> ring
      rw [h1]
      have h2 : ((k : ℝ) + 2)^2 ≤ (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 := by
        have h3 : (k : ℝ) ≥ 14 := by exact_mod_cast h'
        nlinarith
      have h4 : (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ) * (3 / 2 : ℝ)^k := by gcongr
      have h5 : (3 / 2 : ℝ) * (3 / 2 : ℝ)^k = (3 / 2 : ℝ)^(k + 1) := by rw [← pow_succ] <;> ring
      rw [h5] at h4; exact le_trans h2 h4
    · -- k < 14, 但 k+1 ≥ 14, 所以 k = 13
      have h_k : k = 13 := by omega
      rw [h_k]; norm_num

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  let g : ℕ → ℝ := fun k => if k ≥ 14 then ((k : ℝ) + 1)^2 / (2 : ℝ)^k else 0
  have h_bound : ∀ (k : ℕ), g k ≤ (3 / 4 : ℝ)^k := by
    intro k
    by_cases hk : k ≥ 14
    · have h1 : g k = ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by simp [g, hk]
      rw [h1]
      have h2 : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := poly_le_geometric k hk
      have h3 : ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ (3 / 2 : ℝ)^k / (2 : ℝ)^k := by gcongr
      have h4 : (3 / 2 : ℝ)^k / (2 : ℝ)^k = (3 / 4 : ℝ)^k := by rw [← div_pow] <;> ring
      rw [h4] at h3; exact h3
    · have h1 : g k = 0 := by simp [g, hk]
      rw [h1]; positivity
  have h_nonneg : ∀ (k : ℕ), 0 ≤ g k := by intro k; simp [g]; split_ifs <;> positivity
  have h_summable_g : Summable g := Summable.of_nonneg_of_le h_nonneg h_bound (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  -- f 和 g 只差前 14 项
  let f : ℕ → ℝ := fun k => ((k : ℝ) + 1)^2 / (2 : ℝ)^k
  have h_diff : f = g + (fun k => if k < 14 then f k else 0) := by
    funext k; by_cases hk : k < 14 <;> simp [f, g, hk] <;> ring
  rw [h_diff]
  have h_summable_tail : Summable (fun k : ℕ => if k < 14 then f k else 0) := by
    apply Summable.comp_injective (f := fun (i : Fin 14) => f i)
    · exact Fin.val_injective
    · exact Fintype.summable
  exact h_summable_g.add h_summable_tail

#check summable_quadratic_over_geometric

end RHSpectralDuality
