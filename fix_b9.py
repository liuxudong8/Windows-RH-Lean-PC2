f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """  · intro k hk
    subst hk
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    rw [hδ (specDiscM n) h_in] <;> simp [v]"""

new = """  · intro k hk
    rw [hk]
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    rw [hδ (specDiscM n) h_in] <;> simp [v]"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: replaced subst with rw')
