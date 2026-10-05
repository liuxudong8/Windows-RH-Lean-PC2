import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- h_point_bound 核心代数估计（简化路径）
lemma point_bound_algebra (C2 : ℝ) (hC2_pos : 0 < C2) (k : ℕ) :
    C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ (C2 * 8 * Real.log 4 + 1) * ((k : ℝ) + 1) := by
  have h1 : (k : ℝ) + 2 ≤ 4 * ((k : ℝ) + 1) := by
    have h11 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
    linarith
  have h2 : (1 : ℝ) ≤ 4 * ((k : ℝ) + 1) := by
    have h21 : (k : ℝ) + 1 ≥ 1 := by exact_mod_cast Nat.succ_pos k
    linarith
  have h3 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : (1 : ℝ) < Real.log 4 := by
    have h41 : Real.log 4 > Real.log Real.exp 1 := Real.log_lt_log (by positivity) (by linarith [Real.exp_one_lt_d9])
    have h42 : Real.log (Real.exp 1) = 1 := by simp
    linarith
  have h5 : 1 + ((k : ℝ) + 2) * Real.log 2 ≤ 8 * Real.log 4 * ((k : ℝ) + 1) := by
    calc 1 + ((k : ℝ) + 2) * Real.log 2
      ≤ 4 * ((k : ℝ) + 1) + 4 * ((k : ℝ) + 1) * Real.log 4 := by gcongr <;> linarith
      _ = 4 * ((k : ℝ) + 1) * (1 + Real.log 4) := by ring
      _ ≤ 4 * ((k : ℝ) + 1) * (2 * Real.log 4) := by gcongr; linarith
      _ = 8 * Real.log 4 * ((k : ℝ) + 1) := by ring
  have h6 : C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ C2 * (8 * Real.log 4 * ((k : ℝ) + 1)) := by gcongr
  have h7 : C2 * (8 * Real.log 4 * ((k : ℝ) + 1)) ≤ (C2 * 8 * Real.log 4 + 1) * ((k : ℝ) + 1) := by
    have h8 : (1 : ℝ) * ((k : ℝ) + 1) ≥ 0 := by positivity
    nlinarith
  linarith

#check point_bound_algebra

end RHSpectralDuality
