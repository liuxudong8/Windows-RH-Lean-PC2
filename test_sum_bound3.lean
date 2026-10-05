import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma card_bound_simplified (C1 : ℝ) (hC1_pos : 0 < C1) (k : ℕ) :
    2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
  have h1 : (2^(k+1) : ℝ) + 1 ≤ 4 * (2 : ℝ)^k := by
    have h11 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h11]
    have h12 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h13 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h13
    linarith
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      norm_num at h2 ⊢; exact h2
    have h3 : Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h3; exact h3
  have h21 : (2^(k+1) : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
    have h22 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    have h23 : (2^(k+2) : ℝ) = 4 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h22, h23]
    have h24 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h25 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h25
    linarith
  have h25 : (1 : ℝ) ≤ (2^(k+1) : ℝ) + 2 := by
    have h26 : (0 : ℝ) ≤ (2^(k+1) : ℝ) := by positivity
    linarith
  have h_log_nonneg : 0 ≤ Real.log ((2^(k+1) : ℝ) + 2) := Real.log_nonneg h25
  have h23 : Real.log ((2^(k+1) : ℝ) + 2) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log (by positivity) h21
  have h241 : Real.log (2^(k+2) : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
    <;> simp
  have h242 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by simp
  have h24 : Real.log (2^(k+2) : ℝ) = ((k : ℝ) + 2) * Real.log 2 := by
    rw [h241, h242] <;> ring
  have h2 : Real.log ((2^(k+1) : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
    calc Real.log ((2^(k+1) : ℝ) + 2)
      ≤ Real.log (2^(k+2) : ℝ) := h23
      _ = ((k : ℝ) + 2) * Real.log 2 := h24
      _ ≤ ((k : ℝ) + 2) * 1 := by gcongr
      _ ≤ 2 * ((k : ℝ) + 1) := by
        have h26 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
        linarith
  have h3 : 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤
           2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := by
    gcongr
    <;> linarith
  have h4 : 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := by ring
  have h5 : (2 : ℝ) ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h51 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h52 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h52
    have h53 : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
    nlinarith
  have h6 : 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h7 : 2 ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := h5
    nlinarith
  calc 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1)
    ≤ 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := h3
    _ = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := h4
    _ ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := h6

#check card_bound_simplified

end RHSpectralDuality
