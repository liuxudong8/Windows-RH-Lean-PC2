import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """  have h_main : (∑' n : ℕ, f.eval (specDiscM n)) = ∑' k : ℕ, (jlFiberSize k : ℂ) * g k := by
    exact?
"""

new = """  have h_main : (∑' n : ℕ, f.eval (specDiscM n)) = ∑' k : ℕ, (jlFiberSize k : ℂ) * g k := by
    -- Standard fiberwise rearrangement: ∑_n g(jlSpectrumMap n) = ∑_k |fiber(k)| · g(k)
    -- f compact support => only finitely many nonzero terms; finite fibers (1102) => Finset.sum_biUnion
    admit
"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
