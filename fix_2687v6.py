import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """    have h4 : f n ≤ 4 * g n := by
      dsimp only [f, g]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith
    exact h4"""

new = """    have h4 : f n ≤ 4 * g n := by
      dsimp only [f, g]
      have h5 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2 ≤
          4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
        calc
          (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / t^2
            ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / ((1+t)^2 / 4) := by gcongr; nlinarith
          _ = 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1+t)^2) := by
            field_simp; ring
      exact h5"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
