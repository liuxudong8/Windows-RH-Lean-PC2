import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """    have h4 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
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

new = """    have h4 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
      have h5 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
        calc
          (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2
            ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / ((1+t)^2 / 4) := by gcongr; nlinarith
          _ = 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
            field_simp; ring
      exact h5
  have h_small : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := small_finite
  have h : Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
    have h9 : ∀ n, (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤
        4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) ∨
        |(nontrivialZeroEnum n).im| < 1 := by
      intro n
      by_cases hn : |(nontrivialZeroEnum n).im| < 1
      · exact Or.inr hn
      · have h5 : |(nontrivialZeroEnum n).im| ≥ 1 := by linarith
        exact Or.inl (h_main n h5)
    exact?
  exact h"""

assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
