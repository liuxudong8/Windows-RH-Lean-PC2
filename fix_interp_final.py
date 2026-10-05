path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Fix map_add'
old_add = """      map_add' := by
        intro c1 c2
        ext j
        have h : ∑ i : Fin m, (c1 i + c2 i) * v i j = (∑ i : Fin m, c1 i * v i j) + ∑ i : Fin m, c2 i * v i j := by
          rw [Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        exact h"""

new_add = """      map_add' := by
        intro c1 c2
        ext j
        have h1 : ∀ i, (c1 i + c2 i) * v i j = c1 i * v i j + c2 i * v i j := by intro i; ring
        have h : ∑ i : Fin m, (c1 i + c2 i) * v i j = (∑ i : Fin m, c1 i * v i j) + ∑ i : Fin m, c2 i * v i j := by
          rw [Finset.sum_congr rfl (fun i _ => h1 i)]
          rw [Finset.sum_add_distrib]
        exact h"""

content = content.replace(old_add, new_add)

# Fix h_inj sum_sub
old_sub = """      have h5 : ∑ i : Fin m, (c1 i - c2 i) * v i j = ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j := by
        rw [Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring"""

new_sub = """      have h1 : ∀ i, (c1 i - c2 i) * v i j = c1 i * v i j - c2 i * v i j := by intro i; ring
      have h5 : ∑ i : Fin m, (c1 i - c2 i) * v i j = ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j := by
        rw [Finset.sum_congr rfl (fun i _ => h1 i)]
        rw [Finset.sum_sub_distrib]"""

content = content.replace(old_sub, new_sub)

# Fix h_main - need finite sum Mellin linearity
old_main = """  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    simp only [f, melinTransform_linear, v]
    <;> rfl"""

new_main = """  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
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

content = content.replace(old_main, new_main)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed 3 errors')
