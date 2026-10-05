path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    lines = f.readlines()

content = ''.join(lines)

# === 1. spectral_preserving_melin_superposition_countable: 改用 mollified_point_fiber_mellin_rich ===
old_super = """theorem spectral_preserving_melin_superposition_countable
    (f g : MollifiedTestFunction) (T : Set ℂ) (hT : T.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (n : ℕ), f'.toTestFunction.eval (specDiscM n) = f.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), s ∈ T →
        melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
        melinTransform g.toTestFunction s) := by
  let S : Set ℝ := Set.range specDiscM
  have hS : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun x => f.toTestFunction.eval x
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := mollified_eval_support_finite f.toTestFunction
  let w : ℂ → ℂ := fun s => melinTransform f.toTestFunction s + melinTransform g.toTestFunction s
  rcases paley_wiener_whitney_joint_interpolation S hS specDiscM_separable v h_vfin T hT w with ⟨f', h_spec, h_melin⟩
  refine' ⟨f', _⟩
  constructor
  · intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    exact h_spec (specDiscM n) h_in
  · intro s hs
    have h : melinTransform f'.toTestFunction s = w s := h_melin s hs
    have h' : melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
              melinTransform g.toTestFunction s := by
      rw [h]
      dsimp only [w]
      ring
    exact h'"""

new_super = """theorem spectral_preserving_melin_superposition_countable
    (f g : MollifiedTestFunction) (T : Set ℂ) (hT : T.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (n : ℕ), f'.toTestFunction.eval (specDiscM n) = f.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), s ∈ T →
        melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
        melinTransform g.toTestFunction s) := by
  let S : Set ℝ := Set.range specDiscM
  have hS : S.Countable := Set.countable_range _
  rcases mollified_point_fiber_mellin_rich f S hS specDiscM_separable g.toTestFunction with ⟨f', h_pts, h_melin_eq⟩
  refine' ⟨f', _⟩
  constructor
  · intro n
    exact h_pts (specDiscM n) (Set.mem_range_self n)
  · intro s hs
    have h1 : melinTransform f'.toTestFunction s = melinTransform f.toTestFunction s + melinTransform g.toTestFunction s := by
      exact congrFun h_melin_eq s
    rw [h1] <;> ring"""

content = content.replace(old_super, new_super)

# === 2. spectral_point_countable_interpolation: PWW hT countable -> finite (∅) ===
old_spc = """  rcases paley_wiener_whitney_joint_interpolation S hS h_sep v h_vfin (∅ : Set ℂ) Set.countable_empty (fun _ => 0) with ⟨f, h_spec, _⟩"""
new_spc = """  rcases paley_wiener_whitney_joint_interpolation S hS h_sep v h_vfin (∅ : Set ℂ) (Set.finite_empty) (fun _ => 0) with ⟨f, h_spec, _⟩"""
content = content.replace(old_spc, new_spc)

# === 3. melin_transform_scalar_multiple: 直接取 g = c•f ===
old_scalar = """theorem melin_transform_scalar_multiple (f : MollifiedTestFunction) (c : ℂ) :
    ∃ (g : MollifiedTestFunction),
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        melinTransform g.toTestFunction ρ = c * melinTransform f.toTestFunction ρ) ∧
      (∀ (k : ℕ), melinTransform g.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                    c * melinTransform f.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∧
      melinTransform g.toTestFunction (1 : ℂ) = c * melinTransform f.toTestFunction (1 : ℂ) := by
  let S_nontriv : Set ℂ := {ρ' | _root_.riemannZeta ρ' = 0 ∧ 0 < ρ'.re ∧ ρ'.re < 1}
  let S_triv : Set ℂ := Set.range (fun k : ℕ => ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∪ {1}
  let S : Set ℂ := S_nontriv ∪ S_triv
  have h_nontriv_count : S_nontriv.Countable := by
    have h_sub : S_nontriv ⊆ Set.range nontrivialZeroEnum := by
      intro ρ' h
      have h1 : _root_.riemannZeta ρ' = 0 := h.1
      have h2 : 0 < ρ'.re := h.2.1
      have h3 : ρ'.re < 1 := h.2.2
      have h4 : ∃ (n : ℕ), nontrivialZeroEnum n = ρ' := nontrivialZeroEnum_covers_all ρ' h1 h2 h3
      exact h4
    exact Set.Countable.mono h_sub (Set.countable_range nontrivialZeroEnum)
  have h_triv_count : S_triv.Countable := Set.Countable.union (Set.countable_range _) (Set.countable_singleton _)
  have hS_count : S.Countable := Set.Countable.union h_nontriv_count h_triv_count
  let v : ℂ → ℂ := fun s => c * melinTransform f.toTestFunction s
  rcases mellin_countable_interpolation S hS_count v with ⟨g, hg⟩
  refine' ⟨g, _⟩
  constructor
  · intro ρ hz hre1 hre2
    exact hg ρ (Or.inl ⟨hz, hre1, hre2⟩)
  · constructor
    · intro k
      exact hg ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) (Or.inr (Or.inl (Set.mem_range_self k)))
    · exact hg (1 : ℂ) (Or.inr (Or.inr (Set.mem_singleton _)))"""

new_scalar = """theorem melin_transform_scalar_multiple (f : MollifiedTestFunction) (c : ℂ) :
    ∃ (g : MollifiedTestFunction),
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        melinTransform g.toTestFunction ρ = c * melinTransform f.toTestFunction ρ) ∧
      (∀ (k : ℕ), melinTransform g.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                    c * melinTransform f.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∧
      melinTransform g.toTestFunction (1 : ℂ) = c * melinTransform f.toTestFunction (1 : ℂ) := by
  let g : MollifiedTestFunction := c • f
  refine' ⟨g, _⟩
  have h_melin : ∀ (s : ℂ), melinTransform g.toTestFunction s = c * melinTransform f.toTestFunction s := by
    intro s
    have h := melinTransform_linear f.toTestFunction (0 : TestFunction) c (0 : ℂ) s
    simpa using h
  constructor
  · intro ρ hz hre1 hre2; exact h_melin ρ
  · constructor
    · intro k; exact h_melin _
    · exact h_melin _"""

content = content.replace(old_scalar, new_scalar)

# === 4. melin_pair_sum_nondegenerate: countable -> finite ===
old_pair1 = """    let S : Set ℂ := {s1}
    have hS : S.Countable := Set.countable_singleton _
    rcases mellin_countable_interpolation S hS (fun _ => (1 : ℂ)) with ⟨g, hg⟩"""
new_pair1 = """    let S : Set ℂ := {s1}
    have hS : S.Finite := Set.finite_singleton _
    rcases mellin_finite_interpolation S hS (fun _ => (1 : ℂ)) with ⟨g, hg⟩"""
content = content.replace(old_pair1, new_pair1)

old_pair2 = """    let S : Set ℂ := {s1, s2}
    have hS : S.Countable := by
      simp [S]
      <;> exact Set.countable_insert _ (Set.countable_singleton _)
    let v : ℂ → ℂ := fun s => if s = s1 then 1 else 0
    rcases mellin_countable_interpolation S hS v with ⟨g, hg⟩"""
new_pair2 = """    let S : Set ℂ := {s1, s2}
    have hS : S.Finite := by
      simp [S]
      <;> exact Set.finite_insert _ (Set.finite_singleton _)
    let v : ℂ → ℂ := fun s => if s = s1 then 1 else 0
    rcases mellin_finite_interpolation S hS v with ⟨g, hg⟩"""
content = content.replace(old_pair2, new_pair2)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Stage 1 modifications done')
