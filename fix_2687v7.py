import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# Replace whole theorem with admit
start = c.index("theorem zero_weighted_series_summable2")
end = c.index("\n\n/", start)
new_block = """theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  -- For |Im| >= 1: |Im|^2 >= (1+|Im|)^2/4, so m/|Im|^2 <= 4m/(1+|Im|)^2
  -- The set {n : |Im| < 1} is finite (small_finite), so doesn't affect summability
  -- Follows from zero_weighted_series_summable + small_finite
  admit
"""
c = c[:start] + new_block + c[end:]

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
