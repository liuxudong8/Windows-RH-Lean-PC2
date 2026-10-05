import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  have h_pos : 0 < t + 1 := by linarith
  have h_exists : ∃ k : ℕ, t < (2^(k+1) : ℝ) := by
    let K := Nat.ceil (Real.logb 2 (t + 1)) + 1
    refine ⟨K, ?_⟩
    have h1 : t + 1 = (2 : ℝ) ^ (Real.logb 2 (t + 1)) := by
      rw [Real.rpow_logb (by linarith) (by norm_num)]
    have h2 : Real.logb 2 (t + 1) ≤ (Nat.ceil (Real.logb 2 (t + 1)) : ℝ) := Nat.le_ceil _
    have h3 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) ≤ (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (t + 1)) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> linarith
    have h4 : t + 1 ≤ (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (t + 1)) : ℝ) := by
      rw [h1] at *; exact h3
    have h5 : (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (t + 1)) : ℝ) < (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (t + 1)) + 1) := by
      apply pow_lt_pow_right₀ <;> norm_num
    have h6 : t < (2 : ℝ) ^ (Nat.ceil (Real.logb 2 (t + 1)) + 1) := by linarith
    simpa [K] using h6
  let k := Nat.find h_exists
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := fun m hm => Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k0
      have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not
      have h : ¬(t < (2^k : ℝ)) := h_not
      have h' : (2^k : ℝ) ≤ t := by linarith
      exact h'
  exact ⟨k, h_k_ge, h_k_prop⟩

#check exists_layer_index

end RHSpectralDuality
