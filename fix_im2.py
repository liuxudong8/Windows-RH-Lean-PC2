import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# Fix 3456: add s.im ≠ 0 to the statement of mellin_constraint_dual_norm_uniform
old = "(∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →\n          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by"
new = "(∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 → s.im ≠ 0 →\n          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by"
assert old in c, "old not found"
c = c.replace(old, new)

# Fix 3510: the intro already has hs_im_ne_zero (we added it), but the statement
# now has the extra binder, so introN should work. No change needed here.

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
