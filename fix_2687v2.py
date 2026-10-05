import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """  have h_main : ∀ n, |(nontrivialZeroEnum n).im| ≥ 1 →
      (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤
      4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
    intro n hn
    have h1 : 1 ≤ |(nontrivialZeroEnum n).im| := hn
    have h2 : |(nontrivialZeroEnum n).im| ^ 2 ≥ (1 + |(nontrivialZeroEnum n).im|)^2 / 4 := by
      nlinarith [abs_nonneg (nontrivialZeroEnum n).im]
    have h3 : 0 ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) := by positivity
    gcongr
    <;> linarith
  have h_small : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := small_finite
  exact Summable.on_finite_set h_small (zero_weighted_series_summable.mono (fun n hn => h_main n hn))"""

new = """  have h_main : ∀ n, |(nontrivialZeroEnum n).im| ≥ 1 →
      (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤
      4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
    intro n hn
    set t := |(nontrivialZeroEnum n).im| with ht
    have h1 : 1 ≤ t := hn
    have h2 : t ^ 2 ≥ (1 + t)^2 / 4 := by nlinarith
    have h3 : 0 ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) := by positivity
    have h4 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith
    exact h4
  have h_small : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := small_finite
  have h : Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
    apply Summable.mono' zero_weighted_series_summable (fun n => _)
    intro n
    by_cases hn : |(nontrivialZeroEnum n).im| < 1
    · exact Or.inr (by positivity)
    · have h5 : |(nontrivialZeroEnum n).im| ≥ 1 := by linarith
      exact Or.inl (h_main n h5)
  exact h"""

assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
