import BSD.LPrime

open BSD.LPrime
open MeasureTheory

set_option maxHeartbeats 4000000

example (m : ℕ) (hm4 : 4 ≤ m) :
    Real.exp (-(1.03 : ℝ) * m) / bn m ≤
      Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ)) := by
  have hinv : 1 / bn m ≤ 1 / (4 * (1.03 : ℝ)) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 * 1.03) (bn_ge_4c m hm4)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hm : (1 / bn m) * Real.exp (-(1.03 : ℝ) * m) ≤
      (1 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * m) := by
    have hEpos : (0 : ℝ) ≤ Real.exp (-(1.03 : ℝ) * m) := (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hinv hEpos
  simpa [mul_comm] using hm
