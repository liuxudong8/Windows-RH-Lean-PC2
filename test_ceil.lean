import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 证明：对于非负 x，(Nat.ceil x : ℝ) ≤ x + 1
lemma ceil_le_add_one (x : ℝ) (hx : 0 ≤ x) : (Nat.ceil x : ℝ) ≤ x + 1 := by
  have h1 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  linarith

#check ceil_le_add_one

end RHSpectralDuality
