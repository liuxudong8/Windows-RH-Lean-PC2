import OrderPreservingBijection.stage_4

open RHSpectralDuality

variable (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g) (h_le : ∀ n, f n ≤ g n)

-- tsum comparison
#check @tsum_le_tsum
#check @tsum_mono
#check @tsum_le_tsum_of_le
#check @Summable.tsum_le_tsum
#check @le_tsum
#check @tsum_add_le
#check @tsum_sub
#check @tsum_neg
#check @tsum_abs
