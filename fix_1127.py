import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """  have h_main : (∑' n : ℕ, f.eval (specDiscM n)) = ∑' k : ℕ, (jlFiberSize k : ℂ) * g k := by
    admit"""

new = """  have h_main : (∑' n : ℕ, f.eval (specDiscM n)) = ∑' k : ℕ, (jlFiberSize k : ℂ) * g k := by
    exact?
"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
