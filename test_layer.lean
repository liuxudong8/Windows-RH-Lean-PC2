import OrderPreservingBijection.stage_4

open RHSpectralDuality

-- Test 1: Set.ncard upper bound implies finite
variable (s : Set ℂ) (h : Set.ncard s ≤ (10 : ENat))
#check Set.ncard_lt_top
#check Set.Finite.of_ncard_ne_top

-- Test 2: Set.Finite.subset
#check Set.Finite.subset

-- Test 3: image of finite set under injective function
variable (f : ℕ → ℂ) (hf : Function.Injective f) (t : Set ℕ) (ht : t.Finite)
#check Set.Finite.image f ht
#check Set.Finite.preimage

-- Test 4: tsum countable additivity for nonnegative functions
variable (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
#check @tsum_iUnion
#check @Summable.of_nonneg_of_le

-- Test 5: geometric series with polynomial
#check @summable_geometric_of_lt_one
#check @summable_pow_mul_geometric_of_norm_lt_one
