import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum

#check pow_le_pow_left₀
#check pow_le_pow_of_le_left
#check pow_le_pow_right₀
#check sq_le_sq
#check pow_two
#check Real.exp_le_exp_of_le

example {x : ℝ} (hx : x ≤ (0.358 : ℝ)) (hnn : 0 ≤ x) : x ^ 2 ≤ (0.358 : ℝ) ^ 2 := by
  exact pow_le_pow_left₀ hnn hx 2
