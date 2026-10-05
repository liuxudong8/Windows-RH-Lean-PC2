import OrderPreservingBijection.stage_4

open RHSpectralDuality

-- Search for conjugation property
#check @Complex.conj
#check @riemannZeta

-- Search for tsum partition
#check @tsum
#check @Summable
#check @Finset.sum
#check @Set.Finite
#check @Set.ncard

-- Try to find tsum over countable union
variable (f : ℕ → ℝ)
#check @tsum_eq_tsum_add_tsum
#check @Summable.add
