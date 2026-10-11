import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

#check @hasSum_nat_add_iff
#check @Summable.comp_injective
#check summable_nat_add_iff

open scoped BigOperators

-- 用 @ 显式 f 试 hasSum_nat_add_iff 的 mpr
example (f : ℕ → ℝ) (hf : Summable f) :
    HasSum f ((∑' n : ℕ, f (n + 3)) + ∑ i ∈ Finset.range 3, f i) := by
  have hs : HasSum (fun n : ℕ => f (n + 3)) (∑' n : ℕ, f (n + 3)) :=
    (summable_nat_add_iff 3).mpr hf |>.hasSum
  exact (@hasSum_nat_add_iff ℝ (∑' n : ℕ, f (n + 3)) f 3).mpr hs

-- comp_injective 用法确认
example (f : ℕ → ℝ) (hf : Summable f) :
    Summable (fun n : ℕ => f (n + 3)) := by
  have hinj : Function.Injective (fun n : ℕ => n + 3) := by
    intro a b h
    dsimp at h
    omega
  exact hf.comp_injective hinj
