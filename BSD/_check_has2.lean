import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

-- named args 方式传 f/g，避开 @
example (f : ℕ → ℝ) (hf : Summable f) :
    HasSum f ((∑' n : ℕ, f (n + 3)) + ∑ i ∈ Finset.range 3, f i) := by
  have hs : HasSum (fun n : ℕ => f (n + 3)) (∑' n : ℕ, f (n + 3)) :=
    (summable_nat_add_iff 3).mpr hf |>.hasSum
  exact (hasSum_nat_add_iff (k := 3) (f := f) (g := (∑' n : ℕ, f (n + 3)))).mpr hs

-- 全链验证：拆分恒等式
example (f : ℕ → ℝ) (hf : Summable f) :
    (∑' n : ℕ, f n) = (∑ i ∈ Finset.range 3, f i) + ∑' n : ℕ, f (n + 3) := by
  have hs : HasSum (fun n : ℕ => f (n + 3)) (∑' n : ℕ, f (n + 3)) :=
    (summable_nat_add_iff 3).mpr hf |>.hasSum
  have hfull : HasSum f ((∑' n : ℕ, f (n + 3)) + ∑ i ∈ Finset.range 3, f i) :=
    (hasSum_nat_add_iff (k := 3) (f := f) (g := (∑' n : ℕ, f (n + 3)))).mpr hs
  rw [hfull.tsum_eq]
  ring
