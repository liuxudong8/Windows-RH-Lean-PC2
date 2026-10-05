import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  have h_pos : 0 < t + 1 := by linarith
  let N := Nat.ceil (Real.logb 2 (t + 1))
  have h1 : t + 1 = (2 : ℝ) ^ (Real.logb 2 (t + 1)) := by
    rw [Real.rpow_logb h_pos (by norm_num)]
  have h2 : Real.logb 2 (t + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have h3 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) ≤ (2 : ℝ) ^ (N : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> exact h2
  have h4 : t + 1 ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc t + 1 = (2 : ℝ) ^ (Real.logb 2 (t + 1)) := h1
         _ ≤ (2 : ℝ) ^ (N : ℝ) := h3
  have h5 : t < (2 : ℝ) ^ (N : ℝ) := by linarith
  have h6 : (2 : ℝ) ^ (N : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    have h7 : (N : ℝ) ≤ (N + 1 : ℝ) := by simp
    apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> exact h7
  have h_exists : ∃ k : ℕ, t < (2^(k+1) : ℝ) := ⟨N, by
    have h8 : t < (2 : ℝ) ^ (N : ℝ) := h5
    have h9 : (2 : ℝ) ^ (N : ℝ) ≤ (2 : ℝ) ^ (N + 1 : ℝ) := h6
    have h10 : (2 : ℝ) ^ (N + 1 : ℝ) = (2^(N+1) : ℝ) := by norm_cast
    rw [h10] at h9; linarith⟩
  let k := Nat.find h_exists
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := fun m hm => Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not
      have h' : (2^k : ℝ) ≤ t := by linarith
      exact h'
  exact ⟨k, h_k_ge, h_k_prop⟩

#check exists_layer_index

end RHSpectralDuality
