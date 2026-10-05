import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma poly_le_geometric (k : ℕ) (h : k ≥ 14) : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := by
  induction k with
  | zero => exfalso; linarith
  | succ k ih =>
    by_cases h' : k ≥ 14
    · have h_ih' := ih h'
      have h1 : ((k.succ : ℝ) + 1)^2 = ((k : ℝ) + 2)^2 := by simp [Nat.cast_add] <;> ring
      rw [h1]
      have h2 : ((k : ℝ) + 2)^2 ≤ (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 := by
        have h3 : (k : ℝ) ≥ 14 := by exact_mod_cast h'
        nlinarith
      have h4 : (3 / 2 : ℝ) * ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ) * (3 / 2 : ℝ)^k := by gcongr
      have h5 : (3 / 2 : ℝ) * (3 / 2 : ℝ)^k = (3 / 2 : ℝ)^(k + 1) := by
        have h51 : (3 / 2 : ℝ)^(k + 1) = (3 / 2 : ℝ)^k * (3 / 2 : ℝ) := by rw [pow_succ]
        linarith
      rw [h5] at h4; exact le_trans h2 h4
    · have h_k : k = 13 := by omega
      rw [h_k]; norm_num

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_main : ∃ (C : ℝ), Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
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
    let tail : ℕ → ℝ := fun k => if k < 14 then ((k : ℝ) + 1)^2 / (2 : ℝ)^k else 0
    have h_summable_tail : Summable tail := by
      apply Summable.comp_injective (f := fun (i : Fin 14) => ((i : ℕ) : ℝ) + 1)
      · exact Fin.val_injective
      · exact Fintype.summable
    have h_eq : (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) = g + tail := by
      funext k
      by_cases hk : k < 14
      · have h_ge : ¬(k ≥ 14) := by linarith
        simp [g, tail, hk, h_ge] <;> ring
      · have h_lt : ¬(k < 14) := by linarith
        have h_ge : k ≥ 14 := by linarith
        simp [g, tail, h_lt, h_ge] <;> ring
    rw [h_eq]
    exact h_summable_g.add h_summable_tail
  exact h_main.choose_spec

#check summable_quadratic_over_geometric

end RHSpectralDuality
