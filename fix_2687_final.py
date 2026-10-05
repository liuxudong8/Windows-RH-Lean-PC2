import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  admit"""

new = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  let f : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2
  let g : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2
  have hg : Summable g := zero_weighted_series_summable
  have h_small : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := small_finite
  have h_bound : ∀ n, |(nontrivialZeroEnum n).im| ≥ 1 → f n ≤ 4 * g n := by
    intro n hn
    set t := |(nontrivialZeroEnum n).im| with ht
    have h1 : 1 ≤ t := hn
    have h2 : t^2 ≥ (1+t)^2 / 4 := by nlinarith
    have h3 : 0 ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) := by positivity
    have h4 : f n ≤ 4 * g n := by
      dsimp only [f, g]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith
    exact h4
  exact?
"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
