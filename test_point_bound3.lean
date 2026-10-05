import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- h_point_bound 核心代数估计（最简路径：log 2 ≤ 1）
lemma point_bound_algebra (C2 : ℝ) (hC2_pos : 0 < C2) (k : ℕ) :
    C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h2 : ∀ (x : ℝ), 0 ≤ x → 1 + x ≤ Real.exp x := by
        intro x hx; exact?
      exact h2 1 (by norm_num)
    have h3 : Real.log 2 ≤ 1 := Real.log_le_log (by norm_num) h1
    exact h3
  have h1 : (k : ℝ) + 2 ≤ 4 * ((k : ℝ) + 1) := by
    have h11 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
    linarith
  have h2 : (1 : ℝ) ≤ 4 * ((k : ℝ) + 1) := by
    have h21 : (k : ℝ) + 1 ≥ 1 := by exact_mod_cast Nat.succ_pos k
    linarith
  have h3 : 1 + ((k : ℝ) + 2) * Real.log 2 ≤ 4 * ((k : ℝ) + 1) := by
    calc 1 + ((k : ℝ) + 2) * Real.log 2
      ≤ 1 + ((k : ℝ) + 2) * 1 := by gcongr
      _ = 1 + ((k : ℝ) + 2) := by ring
      _ ≤ 4 * ((k : ℝ) + 1) := by linarith
  have h4 : C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ C2 * (4 * ((k : ℝ) + 1)) := by gcongr
  have h5 : C2 * (4 * ((k : ℝ) + 1)) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
    have h6 : (1 : ℝ) * ((k : ℝ) + 1) ≥ 0 := by positivity
    nlinarith
  linarith

#check point_bound_algebra

end RHSpectralDuality
