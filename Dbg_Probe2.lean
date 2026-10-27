import QRH.S7_1_Core
open Real
noncomputable section

namespace QRH

example (X : ℝ) (h1 : (12497 : ℝ) / 50000 ≤ X)
    (hone : (12497 : ℝ) / 50000 + 37503 / 50000 = 1) : 1 - X ≤ 37503 / 50000 := by
  linarith [h1, hone]

example (X : ℝ) (h1 : (12497 : ℝ) / 50000 ≤ X)
    (hone : (12497 : ℝ) / 50000 + 37503 / 50000 = 1) : 1 - X ≤ 37503 / 50000 := by
  nlinarith [h1, hone]

example (X : ℝ) (h1 : (12497 : ℝ) / 50000 ≤ X) : (12497 : ℝ) / 50000 - X ≤ 0 := by
  linarith [h1]

example : (12497 : ℝ) / 50000 + 37503 / 50000 = 1 := by
  norm_num

example (X : ℝ) (h1 : (12497 : ℝ) / 50000 - X ≤ 0) : 1 - X ≤ 37503 / 50000 := by
  linarith [h1]

end QRH
