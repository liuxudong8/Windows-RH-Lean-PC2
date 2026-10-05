path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old = """  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s.erase l0, f x + f l0 := by
    rw [Finset.sum_erase_add hl0 f] <;> abel
  have h2 : ∑ x ∈ s, f0 x = ∑ x ∈ s.erase l0, f0 x + f0 l0 := by
    rw [Finset.sum_erase_add hl0 f0] <;> abel"""

new = """  have h1 : ∑ x ∈ s.erase l0, f x = ∑ x ∈ s, f x - f l0 := Finset.sum_erase hl0 f
  have h2 : ∑ x ∈ s.erase l0, f0 x = ∑ x ∈ s, f0 x - f0 l0 := Finset.sum_erase hl0 f0
  have h1' : ∑ x ∈ s, f x = ∑ x ∈ s.erase l0, f x + f l0 := by rw [h1] <;> abel
  have h2' : ∑ x ∈ s, f0 x = ∑ x ∈ s.erase l0, f0 x + f0 l0 := by rw [h2] <;> abel"""

content = content.replace(old, new)

# Also update the rw to use h1' h2'
content = content.replace(
    "  rw [h1, h2, h3] <;> abel",
    "  rw [h1', h2', h3] <;> abel"
)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed sum_erase')
