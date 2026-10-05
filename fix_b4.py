f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. single_spectral_point_preserving_superposition
old1 = """axiom single_spectral_point_preserving_superposition (g : MollifiedTestFunction) (n : ℕ) :
    ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)"""

new1 = """theorem single_spectral_point_preserving_superposition (g : MollifiedTestFunction) (n : ℕ) :
    ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
  rcases mollified_spectral_delta 0 with ⟨f0, _, _⟩
  let S : Set ℝ := {specDiscM n}
  have hS_count : S.Countable := Set.countable_singleton _
  rcases mellin_shift_preserving_spectral_values f0 g S hS_count with ⟨f2, h_melin, h_spec⟩
  refine' ⟨f0, f2, _⟩
  constructor
  · exact (h_spec (specDiscM n) (Set.mem_singleton _)).symm
  · exact h_melin"""

content = content.replace(old1, new1, 1)

# 2. finite_spectral_points_intersection
old2 = """axiom finite_spectral_points_intersection (g : MollifiedTestFunction) (F : Finset ℕ) :
    (∀ (n : ℕ), n ∈ F → ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)) →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (n : ℕ), n ∈ F → f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)"""

new2 = """theorem finite_spectral_points_intersection (g : MollifiedTestFunction) (F : Finset ℕ) :
    (∀ (n : ℕ), n ∈ F → ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)) →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (n : ℕ), n ∈ F → f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
  intro _
  rcases mollified_spectral_delta 0 with ⟨f0, _, _⟩
  let S : Set ℝ := Set.image specDiscM (F : Set ℕ)
  have hS_count : S.Countable := Set.Countable.image specDiscM (Finset.countable_toSet F)
  rcases mellin_shift_preserving_spectral_values f0 g S hS_count with ⟨f2, h_melin, h_spec⟩
  refine' ⟨f0, f2, _⟩
  constructor
  · intro n hn
    have h_in : specDiscM n ∈ S := ⟨n, Finset.mem_coe.mpr hn, rfl⟩
    exact (h_spec (specDiscM n) h_in).symm
  · exact h_melin"""

content = content.replace(old2, new2, 1)

# 3. prefix_finite_intersection_compactness
old3 = """axiom prefix_finite_intersection_compactness (g : MollifiedTestFunction) :
    (∀ (n : ℕ), ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (k : ℕ), k ≤ n → f1.toTestFunction.eval (specDiscM k) = f2.toTestFunction.eval (specDiscM k)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)) →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)"""

new3 = """theorem prefix_finite_intersection_compactness (g : MollifiedTestFunction) :
    (∀ (n : ℕ), ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (k : ℕ), k ≤ n → f1.toTestFunction.eval (specDiscM k) = f2.toTestFunction.eval (specDiscM k)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)) →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
  intro _
  rcases mollified_spectral_delta 0 with ⟨f0, _, _⟩
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  rcases mellin_shift_preserving_spectral_values f0 g S hS_count with ⟨f2, h_melin, h_spec⟩
  refine' ⟨f0, f2, _⟩
  constructor
  · intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    exact (h_spec (specDiscM n) h_in).symm
  · exact h_melin"""

content = content.replace(old3, new3, 1)

# 4. spectral_base_invariance
old4 = """axiom spectral_base_invariance (f g f1 f2 : MollifiedTestFunction) :
    (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) →
    (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                  melinTransform g.toTestFunction s) →
    ∃ (f' : MollifiedTestFunction),
      (∀ n : ℕ, f'.toTestFunction.eval (specDiscM n) = f.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s)"""

new4 = """theorem spectral_base_invariance (f g f1 f2 : MollifiedTestFunction) :
    (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) →
    (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                  melinTransform g.toTestFunction s) →
    ∃ (f' : MollifiedTestFunction),
      (∀ n : ℕ, f'.toTestFunction.eval (specDiscM n) = f.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
  intro _ _
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  exact mellin_shift_preserving_spectral_values f g S hS_count"""

content = content.replace(old4, new4, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: downgraded 4 B-group axioms to theorems')
