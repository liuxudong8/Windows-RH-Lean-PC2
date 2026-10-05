# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到 zero_weighted_series_summable2 定理
old = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  sorry"""

new = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  let w1 : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2
  let w2 : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  have h_small_fin : small.Finite := small_finite
  have h_nonneg_w2 : ∀ n, 0 ≤ w2 n := by intro n; positivity
  have h_bound : ∀ n, n ∉ small → w2 n ≤ 4 * w1 n := by
    intro n hn
    have h1 : 1 ≤ |(nontrivialZeroEnum n).im| := by
      by_contra h2
      have h3 : |(nontrivialZeroEnum n).im| < 1 := by linarith
      exact hn h3
    have h4 : (1 + |(nontrivialZeroEnum n).im|)^2 ≤ 4 * |(nontrivialZeroEnum n).im|^2 := by
      have h5 : 1 ≤ |(nontrivialZeroEnum n).im| := h1
      nlinarith [sq_nonneg (1 - |(nontrivialZeroEnum n).im|)]
    have h6 : 0 < |(nontrivialZeroEnum n).im| := by linarith
    dsimp only [w1, w2]
    have h9 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
      have h10 : 0 ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) := by positivity
      have h11 : 0 < |(nontrivialZeroEnum n).im| ^ 2 := by positivity
      have h12 : 0 < (1 + |(nontrivialZeroEnum n).im|)^2 := by positivity
      rw [div_le_div_iff h11 h12]
      nlinarith
    exact h9
  have h_summable1 : Summable w1 := zero_weighted_series_summable
  have h_summable4w1 : Summable (fun n => 4 * w1 n) := Summable.mul_left 4 h_summable1
  let f_small : ℕ → ℝ := fun n => if n ∈ small then w2 n else 0
  have h_summable_small : Summable f_small := by
    exact?
  have h_main : ∀ n, w2 n ≤ f_small n + 4 * w1 n := by
    intro n
    by_cases h_small : n ∈ small
    · have h10 : f_small n = w2 n := by simp [f_small, h_small]
      rw [h10] <;> linarith [h_nonneg_w2 n]
    · have h10 : f_small n = 0 := by simp [f_small, h_small]
      rw [h10]
      exact h_bound n h_small
  exact Summable.of_nonneg_of_le h_nonneg_w2 h_main (h_summable_small.add h_summable4w1)"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
