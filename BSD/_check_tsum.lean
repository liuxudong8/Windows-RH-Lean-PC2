import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum

#check tsum_eq_sum_add_tsum
#check tsum_eq_tsum_nat_add
#check tsum_eq_tsum_range
#check tsum_comp
#check Summable.comp_injective
#check tsum_eq_tsum_ite
#check tsum_eq_add_tsum_ite
#check tsum_subtype
#check tsum_set
#check tsum_congr
#check tsum_eq_tsum_sum
#check Finset.tsum_eq_tsum
#check tsum_le_tsum
#check norm_tsum_le_tsum_norm
#check tsum_mul_left
#check tsum_mul_right
#check tsum_abs
#check tsum_neg
#check Summable.tsum_le_tsum
#check Summable.norm

-- 验证：∑' n, g (n + K) + Σ_{n<K} g n = ∑' n, g n
example {g : ℕ → ℝ} (hg : Summable g) (K : ℕ) :
    (∑' n : ℕ, g (n + K)) + (∑ n ∈ Finset.range K, g n) = ∑' n : ℕ, g n := by
  -- 尝试用 hasSum 分解
  sorry
