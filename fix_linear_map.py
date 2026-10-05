path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old_proof = """  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun c => fun j => ∑ i : Fin m, c i * v i j
      map_add' := by
        intro c1 c2
        ext j
        simp [Finset.sum_add_distrib] <;> ring
      map_smul' := by
        intro z c
        ext j
        simp [Finset.smul_sum] <;> ring }
  have h_inj : Function.Injective L := by
    intro c1 c2 h
    have h_eq : ∀ j, ∑ i : Fin m, (c1 i - c2 i) * v i j = 0 := by
      intro j
      have h1 : L c1 j = L c2 j := by rw [h]
      simpa [L, v] using h1
    have h_zero : c1 - c2 = 0 := h_indep (c1 - c2) h_eq
    simpa [sub_eq_zero] using h_zero
  have h_surj : Function.Surjective L := by
    exact?"""

new_proof = """  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun c => fun j => ∑ i : Fin m, c i * v i j
      map_add' := by
        intro c1 c2
        ext j
        have h : ∑ i : Fin m, (c1 i + c2 i) * v i j = (∑ i : Fin m, c1 i * v i j) + ∑ i : Fin m, c2 i * v i j := by
          rw [Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        exact h
      map_smul' := by
        intro z c
        ext j
        have h : ∑ i : Fin m, (z * c i) * v i j = z * ∑ i : Fin m, c i * v i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        exact h }
  have h_inj : Function.Injective L := by
    intro c1 c2 h
    have h_eq : ∀ j, ∑ i : Fin m, (c1 i - c2 i) * v i j = 0 := by
      intro j
      have h1 : (L c1) j = (L c2) j := by rw [h]
      have h2 : (L c1) j = ∑ i : Fin m, c1 i * v i j := by rfl
      have h3 : (L c2) j = ∑ i : Fin m, c2 i * v i j := by rfl
      rw [h2, h3] at h1
      have h4 : ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j = 0 := by
        exact sub_eq_zero.mpr h1
      have h5 : ∑ i : Fin m, (c1 i - c2 i) * v i j = ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j := by
        rw [Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h5]
      exact h4
    have h_zero : c1 - c2 = 0 := h_indep (c1 - c2) h_eq
    have h_eq2 : c1 = c2 := by
      simpa [sub_eq_zero] using h_zero
    exact h_eq2
  have h_surj : Function.Surjective L := by
    have h_ker : LinearMap.ker L = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr h_inj
    have h_main : LinearMap.range L = ⊤ := by
      exact?
    intro y
    have h_y : y ∈ LinearMap.range L := by
      rw [h_main]
      trivial
    exact h_y"""

content = content.replace(old_proof, new_proof)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed LinearMap proof')
