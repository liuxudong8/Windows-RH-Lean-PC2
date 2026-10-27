import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

#check Real.cos_bound
#check Real.sin_bound
#check intervalIntegral

example (x : ℝ) (hx : |x| ≤ 1) : |Real.cos x - (1 - x ^ 2 / 2)| ≤ (5 / 96 : ℝ) * |x| ^ 4 := by
  exact Real.cos_bound x hx
