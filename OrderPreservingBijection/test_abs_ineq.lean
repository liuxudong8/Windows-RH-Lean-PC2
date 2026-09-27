import Mathlib
open Complex

-- 引理：当 |t| ≥ 1 时，1 / |t| ^ 2 ≤ 4 / (1 + |t|) ^ 2
lemma one_div_abs_sq_le_four_div_one_plus_abs_sq {t : ℝ} (ht : 1 ≤ |t|) :
    1 / |t| ^ 2 ≤ 4 / (1 + |t|) ^ 2 := by
  have h1 : 0 < |t| := by
    exact lt_of_lt_of_le (by norm_num) ht
  have h2 : 1 + |t| ≤ 2 * |t| := by
    linarith [abs_nonneg t]
  have h3 : (1 + |t|) ^ 2 ≤ (2 * |t|) ^ 2 := by
    gcongr
    <;> linarith [abs_nonneg t]
  have h4 : (2 * |t|) ^ 2 = 4 * |t| ^ 2 := by ring
  rw [h4] at h3
  have h5 : 0 < |t| ^ 2 := by positivity
  have h6 : 0 < (1 + |t|) ^ 2 := by positivity
  exact one_div_le_one_div_of_le (by positivity) h3
