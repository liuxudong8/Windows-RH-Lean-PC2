path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old_block = """  rcases h_surj w with ⟨c, hc⟩
  let f : TestFunction := ∑ i : Fin m, c i • intervalIndicator (a i) (b i) (ha i) (hab i)
  refine ⟨f, ?_⟩
  intro j
  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
      melinTransform (∑ i ∈ s, c' i • intervalIndicator (a i) (b i) (ha i) (hab i)) =
      ∑ i ∈ s, c' i * melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) := by
    intro s c'
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [melinTransform_linear]
      rw [ih]
      <;> ring
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    rw [h_melin_sum (Finset.univ) c]
    apply Finset.sum_congr rfl
    intro i _
    rfl"""

new_block = """  rcases h_surj w with ⟨c, hc⟩
  let f_i : Fin m → TestFunction := fun i => intervalIndicator (a i) (b i) (ha i) (hab i)
  let f : TestFunction := ∑ i : Fin m, c i • f_i i
  refine ⟨f, ?_⟩
  intro j
  have h_melin_zero : melinTransform (0 : TestFunction) (t j) = 0 := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) (t j)
    simpa using h
  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
      melinTransform (∑ i ∈ s, c' i • f_i i) (t j) = ∑ i ∈ s, c' i * melinTransform (f_i i) (t j) := by
    intro s c'
    induction s using Finset.induction with
    | empty =>
      simpa using h_melin_zero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [melinTransform_linear (c' i • f_i i) (∑ k ∈ s, c' k • f_i k) 1 1 (t j)]
      rw [ih]
      <;> ring
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    rw [h_melin_sum (Finset.univ) c]
    apply Finset.sum_congr rfl
    intro i _
    rfl"""

content = content.replace(old_block, new_block)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed type inference and empty case')
