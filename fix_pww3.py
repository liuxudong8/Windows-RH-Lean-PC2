f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """theorem mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x) := by
  apply mellin_shift_countable_compactness f g S hS
  intro F hF_sub
  induction' F using Finset.induction with x F hx ih
  · -- 空集：取 f'=f
    refine' ⟨f, _⟩
    constructor
    · intro s; simp
    · intro x hx; exfalso; exact Finset.not_mem_empty x hx
  · -- 插入 x：先对 F\\{x} 构造 f₁，再对 x 构造 f'
    have hF'_sub : ∀ y ∈ F, y ∈ S := by intro y hy; exact hF_sub y (Finset.mem_insert_of_mem hy)
    rcases ih hF'_sub with ⟨f1, h_melin1, h_spec1⟩
    have hx_in_S : x ∈ S := hF_sub x (Finset.mem_insert_self x F)
    rcases mellin_shift_single_spectral_point f1 g x with ⟨f', h_melin, h_spec_x⟩
    refine' ⟨f', h_melin, _⟩
    intro y hy
    by_cases h_y_eq : y = x
    · rw [h_y_eq]; exact h_spec_x
    · have h_y_in_F : y ∈ F := by
        simpa [h_y_eq] using (Finset.mem_insert.mp hy).resolve_left h_y_eq
      exact h_spec1 y h_y_in_F"""

new = """theorem mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x) := by
  have h_finite : ∀ (F : Finset ℝ), (∀ x ∈ F, x ∈ S) →
      ∃ (f' : MollifiedTestFunction),
        (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                      melinTransform g.toTestFunction s) ∧
        (∀ x ∈ F, f'.toTestFunction.eval x = f.toTestFunction.eval x) := by
    intro F
    induction F using Finset.induction with
    | empty =>
      intro _
      refine' ⟨f, _⟩
      constructor
      · intro s; simp
      · intro x hx; exfalso; exact Finset.not_mem_empty x hx
    | @insert x F hx ih =>
      intro hF_sub
      have hF'_sub : ∀ y ∈ F, y ∈ S := by
        intro y hy; exact hF_sub y (Finset.mem_insert_of_mem hy)
      rcases ih hF'_sub with ⟨f1, h_melin1, h_spec1⟩
      rcases mellin_shift_single_spectral_point f1 g x with ⟨f', h_melin, h_spec_x⟩
      refine' ⟨f', h_melin, _⟩
      intro y hy
      by_cases h_y_eq : y = x
      · rw [h_y_eq]; exact h_spec_x
      · have h_y_in_F : y ∈ F := by
          simpa [h_y_eq] using (Finset.mem_insert.mp hy).resolve_left h_y_eq
        exact h_spec1 y h_y_in_F
  exact mellin_shift_countable_compactness f g S hS h_finite"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed finite intersection proof')
