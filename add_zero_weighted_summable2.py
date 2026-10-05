# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 在 Line 2630 (index 2629) 后面添加新的定理
new_theorem = '''

theorem zero_weighted_series_summable2 :
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
    dsimp only [w1, w2]
    have h4 : (1 + |(nontrivialZeroEnum n).im|)^2 ≤ 4 * |(nontrivialZeroEnum n).im|^2 := by
      have h5 : 1 ≤ |(nontrivialZeroEnum n).im| := h1
      nlinarith [sq_nonneg (1 - |(nontrivialZeroEnum n).im|)]
    have h6 : 0 < |(nontrivialZeroEnum n).im| := by linarith
    gcongr
  have h_summable1 : Summable w1 := zero_weighted_series_summable
  have h_summable4w1 : Summable (fun n => 4 * w1 n) := Summable.mul_left 4 h_summable1
  have h_summable_small : Summable (fun n => if n ∈ small then w2 n else 0) := by
    apply Summable.on_finite_set h_small_fin
  have h_main : Summable (fun n => w2 n) := by
    have h7 : (fun n => w2 n) = fun n => (if n ∈ small then w2 n else 0) + (if n ∉ small then w2 n else 0) := by
      funext n
      by_cases h : n ∈ small <;> simp [h] <;> ring
    rw [h7]
    apply Summable.add
    · exact h_summable_small
    · have h8 : ∀ n, n ∉ small → (if n ∉ small then w2 n else 0) ≤ 4 * w1 n := by
        intro n hn
        by_cases h9 : n ∈ small <;> simp [h9, h_bound n hn] <;> linarith
      exact Summable.of_nonneg_of_le (fun n => by positivity) h8 h_summable4w1
  exact h_main
'''

# 在 Line 2630 (index 2629) 后面插入
lines.insert(2630, new_theorem)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
