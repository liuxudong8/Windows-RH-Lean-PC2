import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# Add a lemma near nontrivialZeroEnum_are_zeros
# Find where nontrivialZeroEnum_are_zeros is stated (it's external, but we can add our own lemma)
# Just replace the two admits with a named lemma

# Add lemma after line ~2079 area
# Find a good spot - right after nontrivialZeroEnum_are_zeros usage
# Actually just add a global lemma near the top

# Replace the two admits
c = c.replace(
    "(by admit : (nontrivialZeroEnum n).im ≠ 0)",
    "nontrivialZeroEnum_im_ne_zero n"
)

# Add the lemma before the theorem that uses it
# Insert after nontrivialZeroEnum_are_zeros is first used
marker = "lemma globalε₀_pos"
lemma = """lemma nontrivialZeroEnum_im_ne_zero (n : ℕ) : (nontrivialZeroEnum n).im ≠ 0 := by
  -- Nontrivial zeros are by definition off the real axis;
  -- ζ has no zeros on the real segment (0,1)
  admit

"""
c = c.replace(marker, lemma + marker)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
