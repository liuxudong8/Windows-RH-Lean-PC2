import BSD.LPrime

open BSD.LPrime
open MeasureTheory

example (b : ℝ) (hb : 0 < b) : 0 ≤ E1 b := by
  dsimp [E1]
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi b)]
      (fun t : ℝ => Real.exp (-t) / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt (lt_trans hb ht))
  exact MeasureTheory.integral_nonneg_of_ae hae
