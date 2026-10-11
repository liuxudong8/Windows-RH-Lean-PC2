import BSD.LPrime

open BSD.LPrime
open MeasureTheory

set_option maxHeartbeats 4000000

-- g_sum_eq1：左 (n+4)，右 (((n+3:ℕ):ℝ)+1)
lemma g_sum_eq1 :
    (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) =
      (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := by
  funext n
  have h1 : (aE (n + 4) : ℝ) / (n + 4) = (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) := by
    congr 1
    · rw [Nat.cast_add]
      ring
  have h2 : E1 (bn (n + 4)) = E1 (bn (n + 3 + 1)) := by rfl
  calc
    (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))
        = (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1)) := by rw [h1, h2]

-- 1263 应用
example : Summable (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) := by
  have hs3 : Summable (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := by
    exact (summable_nat_add_iff 3).mpr lprime1_summable
  rw [g_sum_eq1]
  exact hs3

-- g_sum_eq2：左 (n+4)，右 (n+3+1) 无括号
lemma g_sum_eq2 :
    (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) =
      (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1))) := by
  funext n
  have h1 : (aE (n + 4) : ℝ) / (n + 4) = (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) := by
    congr 1
    · ring
  have h2 : E1 (bn (n + 4)) = E1 (bn (n + 3 + 1)) := by rfl
  calc
    (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))
        = (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1)) := by rw [h1, h2]

-- 1393 应用
example (htmp2 : |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤ (0.0125 : ℝ)) :
    |∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1))| ≤ (0.0125 : ℝ) := by
  rw [g_sum_eq2] at htmp2
  exact htmp2

-- habs 全拆右侧（v4 已过，复验）
example (hf_abs_sum : Summable (fun n : ℕ => |(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))|)) :
    |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤
      ∑' n : ℕ, |(aE (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |E1 (bn (n + 4))| := by
  have hnorm : Summable (fun n : ℕ => ‖(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))‖) := by
    convert hf_abs_sum using 1
    ext n
    rw [Real.norm_eq_abs]
  simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
