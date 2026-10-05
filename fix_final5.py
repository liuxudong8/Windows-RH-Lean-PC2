path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old_block = """      rw [←h_one]
      rw [melinTransform_linear (f_i i) (∑ k ∈ s, c' k • f_i k) (c' i) (1 : ℂ) (t j)]
      rw [ih]
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    rw [h_melin_sum (Finset.univ) c]
    apply Finset.sum_congr rfl
    intro i _
    rfl"""

new_block = """      rw [←h_one]
      rw [melinTransform_linear (f_i i) (∑ k ∈ s, c' k • f_i k) (c' i) (1 : ℂ) (t j)]
      rw [ih]
      ring
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    rw [h_melin_sum (Finset.univ) c]
    rfl"""

content = content.replace(old_block, new_block)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed')
