f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old_start = "theorem vanishing_subspace_pair_sum_nonzero_exists (ρ : ℂ) :"
idx = content.find(old_start)
next_comment = content.find("\n/--", idx + 10)
old_block = content[idx:next_comment]

new_block = """theorem vanishing_subspace_pair_sum_nonzero_exists (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    (∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0) →
    ∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0 ∧
      (melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0) := by
  intro hz hre1 hre2 _
  let S_nontriv : Set ℂ := {ρ' | _root_.riemannZeta ρ' = 0 ∧ 0 < ρ'.re ∧ ρ'.re < 1}
  let S_triv : Set ℂ := Set.range (fun k : ℕ => ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∪ {1}
  let S : Set ℂ := S_nontriv ∪ S_triv ∪ {ρ, 1 - ρ}
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
  have h_pair_count : ({ρ, 1 - ρ} : Set ℂ).Countable := by
    simp <;> exact Set.countable_insert _ (Set.countable_singleton _)
  have hS_count : S.Countable := by
    simp only [S]
    exact Set.Countable.union (Set.Countable.union h_nontriv_count h_triv_count) h_pair_count
  let v : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  rcases mellin_countable_interpolation S hS_count v with ⟨g0, hg0⟩
  have h_rho_in : ρ ∈ S := by simp [S]
  have h_1mrho_in : (1 - ρ) ∈ S := by simp [S]
  have h_rho : melinTransform g0.toTestFunction ρ = 1 := by
    rw [hg0 ρ h_rho_in] <;> simp [v]
  have h_pair : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0 := by
    by_cases h_eq : ρ = 1 - ρ
    · have h1 : 1 - ρ = ρ := h_eq.symm
      have h2 : melinTransform g0.toTestFunction (1 - ρ) = melinTransform g0.toTestFunction ρ := by rw [h1]
      have h_sum : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) = 2 := by
        rw [h2, h_rho] <;> norm_num
      rw [h_sum] <;> norm_num
    · have h_1mrho_val : melinTransform g0.toTestFunction (1 - ρ) = 0 := by
        rw [hg0 (1 - ρ) h_1mrho_in]
        have h_ne : (1 - ρ) ≠ ρ := by intro h; exact h_eq h.symm
        simp [v, h_ne]
      have h_sum : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) = 1 := by
        rw [h_rho, h_1mrho_val] <;> norm_num
      rw [h_sum] <;> norm_num
  have h_rho_nonneg : 0 < ρ.re := hre1
  have h_rho_lt1 : ρ.re < 1 := hre2
  refine' ⟨g0, _⟩
  constructor
  · intro ρ' hz' hre1' hre2' hne1 hne2
    have h_in : ρ' ∈ S := by simp [S, S_nontriv, hz', hre1', hre2']
    have h_eq : melinTransform g0.toTestFunction ρ' = v ρ' := hg0 ρ' h_in
    rw [h_eq]
    have h_ne : ρ' ≠ ρ := hne1
    simp [v, h_ne]
  · constructor
    · intro k
      let s : ℂ := ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)
      have h_in : s ∈ S := by simp [S, S_triv, s]
      have h_eq : melinTransform g0.toTestFunction s = v s := hg0 s h_in
      rw [h_eq]
      have h_ne : s ≠ ρ := by
        intro h
        have hre : s.re = ρ.re := by rw [h]
        simp [s, Complex.ext_iff] at hre <;> linarith
      simp [v, h_ne]
    · constructor
      · have h_in : (1 : ℂ) ∈ S := by simp [S, S_triv]
        have h_eq : melinTransform g0.toTestFunction (1 : ℂ) = v (1 : ℂ) := hg0 (1 : ℂ) h_in
        rw [h_eq]
        have h_ne : (1 : ℂ) ≠ ρ := by
          intro h
          have hre : (1 : ℂ).re = ρ.re := by rw [h]
          simp at hre <;> linarith
        simp [v, h_ne]
      · exact h_pair
"""

content = content[:idx] + new_block + content[next_comment:]

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: full rewrite with explicit ne proofs')
