import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 搜索相关定理
#check summable_geometric_of_lt_one
#check Summable.mul_left
#check Summable.of_nonneg_of_le

-- 简单方法：(k+1)^2 / 2^k ≤ (3/4)^k 对 k ≥ 某个 N
-- 验证：k=10, (11)^2/1024 = 121/1024 ≈ 0.118, (3/4)^10 ≈ 0.056 — 不成立
-- 换用 (4/5)^k：k=10, (4/5)^10 ≈ 0.107 — 还是不成立
-- 用更松的界：(k+1)^2 ≤ C * r^k, r > 1, 则 (k+1)^2/2^k ≤ C * (r/2)^k
-- 取 r=3/2, 则 (k+1)^2 ≤ C * (3/2)^k, 比值为 (3/4)^k

-- 归纳证明：∀ k, (k+1)^2 ≤ 16 * (3/2)^k
lemma poly_geometric_bound : ∀ (k : ℕ), ((k : ℝ) + 1)^2 ≤ 16 * (3 / 2 : ℝ)^k := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : ((k.succ : ℝ) + 1)^2 = ((k : ℝ) + 2)^2 := by simp [Nat.cast_add] <;> ring
    rw [h1]
    have h2 : ((k : ℝ) + 2)^2 ≤ 2 * ((k : ℝ) + 1)^2 := by
      have h3 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
      nlinarith
    have h4 : 2 * ((k : ℝ) + 1)^2 ≤ 2 * (16 * (3 / 2 : ℝ)^k) := by gcongr
    have h5 : 2 * (16 * (3 / 2 : ℝ)^k) = 16 * (3 / 2 : ℝ)^(k + 1) := by
      simp [pow_succ] <;> ring
    linarith

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_bound : ∀ (k : ℕ), ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ 16 * (3 / 4 : ℝ)^k := by
    intro k
    have h1 : ((k : ℝ) + 1)^2 ≤ 16 * (3 / 2 : ℝ)^k := poly_geometric_bound k
    have h2 : ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ 16 * (3 / 2 : ℝ)^k / (2 : ℝ)^k := by gcongr
    have h3 : 16 * (3 / 2 : ℝ)^k / (2 : ℝ)^k = 16 * (3 / 4 : ℝ)^k := by
      have h4 : (3 / 2 : ℝ)^k / (2 : ℝ)^k = (3 / 4 : ℝ)^k := by
        rw [← div_pow] <;> ring
      rw [h4] <;> ring
    rw [h3] at h2; exact h2
  have h_summable : Summable (fun (k : ℕ) => 16 * (3 / 4 : ℝ)^k) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one
    <;> norm_num
  exact Summable.of_nonneg_of_le (fun k => by positivity) h_bound h_summable

#check summable_quadratic_over_geometric

end RHSpectralDuality
