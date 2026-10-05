path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old_block = """  have h_melin_zero : melinTransform (0 : TestFunction) (t j) = 0 := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (1 : ℂ) (0 : ℂ) (t j)
    simpa [one_smul, zero_smul] using h
  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
      melinTransform (∑ i ∈ s, c' i • f_i i) (t j) = ∑ i ∈ s, c' i * melinTransform (f_i i) (t j) := by
    intro s c'
    induction s using Finset.induction with
    | empty =>
      simpa using h_melin_zero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [melinTransform_linear (f_i i) (∑ k ∈ s, c' k • f_i k) (c' i) (1 : ℂ) (t j)]
      rw [ih]
      <;> ring"""

new_block = """  have h_melin_zero : melinTransform (0 : TestFunction) (t j) = 0 := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) (t j)
    have h0 : (0 : ℂ) • (0 : TestFunction) + (0 : ℂ) • (0 : TestFunction) = (0 : TestFunction) := by simp
    rw [h0] at h
    exact h
  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
      melinTransform (∑ i ∈ s, c' i • f_i i) (t j) = ∑ i ∈ s, c' i * melinTransform (f_i i) (t j) := by
    intro s c'
    induction s using Finset.induction with
    | empty =>
      simpa using h_melin_zero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have h_one : (1 : ℂ) • (∑ k ∈ s, c' k • f_i k) = ∑ k ∈ s, c' k • f_i k := by simp
      rw [←h_one]
      rw [melinTransform_linear (f_i i) (∑ k ∈ s, c' k • f_i k) (c' i) (1 : ℂ) (t j)]
      rw [ih]
      ring"""

content = content.replace(old_block, new_block)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed')
