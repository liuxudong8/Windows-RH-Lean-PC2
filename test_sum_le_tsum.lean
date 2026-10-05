import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 测试 h8 的证明
lemma test_sum_le_tsum (g : ℕ → ℝ) (hg : Summable g) (hnonneg : ∀ n, 0 ≤ g n) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), g k ≤ ∑' k : ℕ, g k := by
  have h1 : HasSum g (∑' k, g k) := hg.hasSum
  exact?

#check test_sum_le_tsum

end RHSpectralDuality
