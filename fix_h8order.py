import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = "    exact mul_le_mul_of_nonneg_left h82 (by positivity)\n    rw [h83] at h82"
new = "    rw [h83] at h82\n    exact mul_le_mul_of_nonneg_left h82 (by positivity)"
assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
