import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- h_point_bound 核心代数估计
lemma point_bound_algebra (C2 : ℝ) (hC2_pos : 0 < C2) (k : ℕ) :
    C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ (C2 * 4 * Real.log 4 + 1) * ((k : ℝ) + 1) := by
  have h1 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    <;> ring
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (k : ℝ) + 1 ≥ 1 := by exact_mod_cast Nat.succ_pos k
  have h4 : 1 + ((k : ℝ) + 2) * Real.log 2 ≤ 4 * Real.log 4 * ((k : ℝ) + 1) := by
    rw [h1]
    have h5 : 1 + ((k : ℝ) + 2) * Real.log 2 ≤ 8 * Real.log 2 * ((k : ℝ) + 1) := by
      nlinarith [h2, h3]
    linarith
  have h6 : C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ C2 * (4 * Real.log 4 * ((k : ℝ) + 1)) := by gcongr
  have h7 : C2 * (4 * Real.log 4 * ((k : ℝ) + 1)) ≤ (C2 * 4 * Real.log 4 + 1) * ((k : ℝ) + 1) := by
    have h8 : (1 : ℝ) * ((k : ℝ) + 1) ≥ 0 := by positivity
    nlinarith
  linarith

#check point_bound_algebra

end RHSpectralDuality
