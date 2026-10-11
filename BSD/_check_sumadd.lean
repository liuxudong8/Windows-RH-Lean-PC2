import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

#check sum_add_tsum_nat_add
#check tsum_nat_add
#check tsum_eq_sum_add_tsum

open scoped BigOperators

example {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n : ℕ, f n) = (∑ i ∈ Finset.range 3, f i) + ∑' n : ℕ, f (n + 3) := by
  exact (sum_add_tsum_nat_add hf 3).symm
