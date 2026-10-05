import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  admit"""

new = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  have h_main : ∀ n, |(nontrivialZeroEnum n).im| ≥ 1 →
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

assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
