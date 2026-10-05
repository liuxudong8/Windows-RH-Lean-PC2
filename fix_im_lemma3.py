import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """lemma nontrivialZeroEnum_im_ne_zero (n : ℕ) : (nontrivialZeroEnum n).im ≠ 0 := by
  -- Nontrivial zeros are by definition off the real axis;
  -- ζ has no zeros on the real segment (0,1)
  admit"""

new = """lemma nontrivialZeroEnum_im_ne_zero (n : ℕ) : (nontrivialZeroEnum n).im ≠ 0 := by
  have hz := nontrivialZeroEnum_are_zeros n
  exact nontrivialZero_im_ne_zero (nontrivialZeroEnum n) hz.1 hz.2.1 hz.2.2"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
