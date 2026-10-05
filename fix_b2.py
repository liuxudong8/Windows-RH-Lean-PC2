f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """axiom mollified_spectral_delta :
    ∀ (n : ℕ), ∃ (δ : MollifiedTestFunction),
      (∀ (k : ℕ), k = n → δ.toTestFunction.eval (specDiscM k) = 1) ∧
      (∀ (k : ℕ), k ≠ n → δ.toTestFunction.eval (specDiscM k) = 0)"""

new = """theorem mollified_spectral_delta :
    ∀ (n : ℕ), ∃ (δ : MollifiedTestFunction),
      (∀ (k : ℕ), k = n → δ.toTestFunction.eval (specDiscM k) = 1) ∧
      (∀ (k : ℕ), k ≠ n → δ.toTestFunction.eval (specDiscM k) = 0) := by
  intro n
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun x => if x = specDiscM n then 1 else 0
  rcases spectral_point_countable_interpolation S hS_count v with ⟨δ, hδ⟩
  refine' ⟨δ, _⟩
  constructor
  · intro k hk
    subst hk
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    rw [hδ (specDiscM n) h_in] <;> simp [v]
  · intro k hk
    have h_in : specDiscM k ∈ S := Set.mem_range_self k
    rw [hδ (specDiscM k) h_in]
    have h_ne : specDiscM k ≠ specDiscM n := by
      intro h
      have h_inj : k = n := specDiscM_strict_mono_axiom.injective h
      exact hk h_inj
    simp [v, h_ne]"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: mollified_spectral_delta -> theorem')
