import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = "  have h2 : ∀ s, s ∈ insert ρ T → 0 < s.re → s.re < 1 →\n      ‖melinTransform h.toTestFunction s‖ ≤ C * B := by"
new = "  have h2 : ∀ s, s ∈ insert ρ T → 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform h.toTestFunction s‖ ≤ C * B := by"
assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
