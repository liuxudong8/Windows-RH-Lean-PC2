import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 测试：所有标识符可用
#check nontrivialZeroEnum
#check nontrivialZeroEnum_injective
#check nontrivialZeroEnum_are_zeros
#check zero_counting_estimate
#check zero_multiplicity_log_growth

-- 测试 star 单射性
example (x y : ℂ) : star x = star y → x = y := by
  intro h; have h2 : star (star x) = star (star y) := by rw [h]
  have h3 : star (star x) = x := by simp
  have h4 : star (star y) = y := by simp
  rw [h3, h4] at h2; exact h2

-- 测试 Nat.ceil 上界
#check @Nat.ceil_le
example (x : ℝ) : (Nat.ceil x : ℝ) ≤ x + 1 := by
  have h1 : Nat.ceil x ≤ Nat.ceil x := by rfl
  have h2 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  exact?

end RHSpectralDuality
