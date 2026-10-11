import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

#check tsum_geometric_of_lt_one
#check hasSum_geometric_of_lt_one
#check Summable.hasSum
#check hasSum_nat_add_iff

open scoped BigOperators

-- 验证 hasSum_nat_add_iff 拆分 + tsum_eq 的组合
example {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, f n) = (∑ i ∈ Finset.range 3, f i) + ∑' n, f (n + 3) := by
  have hs : HasSum (fun n => f (n + 3)) (∑' n, f (n + 3)) := hf.hasSum
  -- 用 hasSum_nat_add_iff 的 mpr 方向
  have hfull : HasSum f ((∑' n, f (n + 3)) + ∑ i ∈ Finset.range 3, f i) := by
    exact (hasSum_nat_add_iff 3).mpr hs
  rw [← hfull.tsum_eq]
  ring

-- 验证几何级数
example (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : (∑' n : ℕ, q ^ n) = (1 - q)⁻¹ := by
  exact tsum_geometric_of_lt_one h0 h1

example (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : (∑' n : ℕ, q ^ (n + 4)) = q ^ 4 * (1 - q)⁻¹ := by
  rw [← tsum_mul_left (a := q ^ 4)]
  congr 1
  funext n
  ring_nf
  -- q^(n+4) = q^n * q^4？ring_nf 处理幂？可能不行——换 pow_add
  sorry

-- 尾项逐点：|g(n+3)| 与几何项
example (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : (∑' n : ℕ, 2 * q ^ (n + 4)) = 2 * q ^ 4 * (1 - q)⁻¹ := by
  rw [← tsum_mul_left (a := 2 * q ^ 4)]
  congr 1
  funext n
  rw [mul_comm (2 * q ^ 4) (q ^ n)]
  -- 需要 q^(n+4) = q^n * q^4：pow_add
  rw [pow_add]
  ring
