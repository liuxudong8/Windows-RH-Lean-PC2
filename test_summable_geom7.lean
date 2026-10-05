import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

def tailGeom (k : ℕ) : ℝ := if k < 14 then ((k : ℝ) + 1)^2 / (2 : ℝ)^k else 0
def mainGeom (k : ℕ) : ℝ := if k ≥ 14 then ((k : ℝ) + 1)^2 / (2 : ℝ)^k else 0

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

lemma mainGeom_le : ∀ (k : ℕ), mainGeom k ≤ (3 / 4 : ℝ)^k := by
  intro k
  unfold mainGeom
  split_ifs with hk
  · have h2 : ((k : ℝ) + 1)^2 ≤ (3 / 2 : ℝ)^k := poly_le_geometric k hk
    have h3 : ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ (3 / 2 : ℝ)^k / (2 : ℝ)^k := by gcongr
    have h4 : (3 / 2 : ℝ)^k / (2 : ℝ)^k = (3 / 4 : ℝ)^k := by rw [← div_pow] <;> ring
    rw [h4] at h3; exact h3
  · positivity

lemma summable_mainGeom : Summable mainGeom :=
  Summable.of_nonneg_of_le (fun k => by unfold mainGeom; split_ifs <;> positivity) mainGeom_le (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma summable_tailGeom : Summable tailGeom := by
  have h_eq : tailGeom = fun (k : ℕ) => if k < 14 then ((k : ℝ) + 1)^2 / (2 : ℝ)^k else 0 := by funext k; rfl
  rw [h_eq]
  apply Summable.comp_injective (f := fun (i : Fin 14) => (((i : ℕ) : ℝ) + 1)^2 / (2 : ℝ)^(i : ℕ))
  · exact Fin.val_injective
  · exact Fintype.summable

lemma f_eq_main_add_tail : (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) = mainGeom + tailGeom := by
  funext k
  unfold mainGeom tailGeom
  by_cases hk : k < 14
  · have h_ge : ¬(k ≥ 14) := by linarith
    rw [if_pos hk, if_neg h_ge, if_pos hk] <;> ring
  · have h_ge : k ≥ 14 := by linarith
    have h_lt : ¬(k < 14) := by linarith
    rw [if_neg h_lt, if_pos h_ge, if_neg h_lt] <;> ring

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  rw [f_eq_main_add_tail]
  exact summable_mainGeom.add summable_tailGeom

#check summable_quadratic_over_geometric

end RHSpectralDuality
