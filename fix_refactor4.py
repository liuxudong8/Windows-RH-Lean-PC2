f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """  intro hz hre1 hre2
  rcases melin_zero_localization ρ g hz hre1 hre2 with ⟨g', h_other_zero, h_triv_zero, h_pole_zero, h_pair_eq⟩
  rcases spectral_preserving_melin_superposition g' with ⟨f1, f2, h_pts, h_super⟩
  have h_other : ∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
      ρ' ≠ ρ → ρ' ≠ 1 - ρ →
      melinTransform f1.toTestFunction ρ' = melinTransform f2.toTestFunction ρ' := by
    intro ρ' hz' hre1' hre2' hne1 hne2
    have h_diff : melinTransform f2.toTestFunction ρ' - melinTransform f1.toTestFunction ρ' =
                   melinTransform g'.toTestFunction ρ' := h_super ρ'
    have h_g'_zero : melinTransform g'.toTestFunction ρ' = 0 := h_other_zero ρ' hz' hre1' hre2' hne1 hne2
    rw [h_g'_zero] at h_diff
    exact (sub_eq_zero.mp h_diff).symm
  have h_pair_diff : (melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
                       (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ)) =
                     melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ) := by
    have h1 : melinTransform f2.toTestFunction ρ - melinTransform f1.toTestFunction ρ =
               melinTransform g'.toTestFunction ρ := h_super ρ
    have h2 : melinTransform f2.toTestFunction (1 - ρ) - melinTransform f1.toTestFunction (1 - ρ) =
               melinTransform g'.toTestFunction (1 - ρ) := h_super (1 - ρ)
    calc
      (melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
        (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ))
        = (melinTransform f2.toTestFunction ρ - melinTransform f1.toTestFunction ρ) +
          (melinTransform f2.toTestFunction (1 - ρ) - melinTransform f1.toTestFunction (1 - ρ)) := by ring
      _ = melinTransform g'.toTestFunction ρ + melinTransform g'.toTestFunction (1 - ρ) := by rw [h1, h2]
      _ = melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ) := h_pair_eq
  have h_triv_eq : trivialZeroContribution f1.toTestFunction = trivialZeroContribution f2.toTestFunction := by
    have h_all_triv : ∀ (k : ℕ), melinTransform f1.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                               melinTransform f2.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) := by
      intro k
      have h_diff : melinTransform f2.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) -
                    melinTransform f1.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0 := by
        rw [h_super ((-2 * (k + 1 : ℕ) : ℝ) : ℂ), h_triv_zero k]
      have h_eq : melinTransform f2.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                  melinTransform f1.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) := sub_eq_zero.mp h_diff
      exact h_eq.symm
    have h_pole_eq : melinTransform f1.toTestFunction (1 : ℂ) = melinTransform f2.toTestFunction (1 : ℂ) := by
      have h_diff : melinTransform f2.toTestFunction (1 : ℂ) - melinTransform f1.toTestFunction (1 : ℂ) = 0 := by
        rw [h_super (1 : ℂ), h_pole_zero]
      have h_eq : melinTransform f2.toTestFunction (1 : ℂ) = melinTransform f1.toTestFunction (1 : ℂ) := sub_eq_zero.mp h_diff
      exact h_eq.symm
    exact trivialZeroContribution_extensionality f1.toTestFunction f2.toTestFunction h_all_triv h_pole_eq
  exact ⟨f1, f2, h_pts, h_other, h_pair_diff, h_triv_eq⟩"""

new = """  intro hz hre1 hre2
  rcases melin_zero_localization ρ g hz hre1 hre2 with ⟨g', h_other_zero, h_triv_zero, h_pole_zero, h_pair_eq⟩
  rcases mollified_spectral_delta 0 with ⟨f1, _, _⟩
  let nontrivSet : Set ℂ := Set.range nontrivialZeroEnum
  let trivSet : Set ℂ := Set.range (fun k : ℕ => ((-2 * (k + 1 : ℕ) : ℝ) : ℂ))
  let T : Set ℂ := nontrivSet ∪ trivSet ∪ {1}
  have hT_count : T.Countable := by
    apply Set.Countable.union
    · apply Set.Countable.union
      · exact Set.countable_range _
      · exact Set.countable_range _
    · exact Set.countable_singleton _
  rcases spectral_preserving_melin_superposition_countable f1 g' T hT_count with ⟨f2, h_pts, h_super⟩
  have h_in_T : ∀ (s : ℂ), (∃ n : ℕ, nontrivialZeroEnum n = s) ∨
      (∃ k : ℕ, s = ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∨ s = (1 : ℂ) → s ∈ T := by
    intro s h
    rcases h with (h | h | h)
    · rcases h with ⟨n, hn⟩; exact Or.inl (Or.inl ⟨n, hn.symm⟩)
    · rcases h with ⟨k, hk⟩; exact Or.inl (Or.inr ⟨k, hk⟩)
    · rw [h]; exact Or.inr (Set.mem_singleton _)
  have h_other : ∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
      ρ' ≠ ρ → ρ' ≠ 1 - ρ →
      melinTransform f1.toTestFunction ρ' = melinTransform f2.toTestFunction ρ' := by
    intro ρ' hz' hre1' hre2' hne1 hne2
    have hρ'_in_T : ρ' ∈ T := by
      have h_exists : ∃ n : ℕ, nontrivialZeroEnum n = ρ' := nontrivialZeroEnum_covers_all ρ' hz' hre1' hre2'
      exact h_in_T ρ' (Or.inl h_exists)
    have h_diff : melinTransform f2.toTestFunction ρ' - melinTransform f1.toTestFunction ρ' =
                   melinTransform g'.toTestFunction ρ' := h_super ρ' hρ'_in_T
    have h_g'_zero : melinTransform g'.toTestFunction ρ' = 0 := h_other_zero ρ' hz' hre1' hre2' hne1 hne2
    rw [h_g'_zero] at h_diff
    exact (sub_eq_zero.mp h_diff).symm
  have hρ_in_T : ρ ∈ T := by
    have h_exists : ∃ n : ℕ, nontrivialZeroEnum n = ρ := nontrivialZeroEnum_covers_all ρ hz hre1 hre2
    exact h_in_T ρ (Or.inl h_exists)
  have h1mρ_in_T : (1 - ρ) ∈ T := by
    have h1mρ_zero : _root_.riemannZeta (1 - ρ) = 0 := (riemann_zeta_zero_symmetry ρ hz hre1 hre2).1
    have h1mρ_re1 : 0 < (1 - ρ).re := (riemann_zeta_zero_symmetry ρ hz hre1 hre2).2.1
    have h1mρ_re2 : (1 - ρ).re < 1 := (riemann_zeta_zero_symmetry ρ hz hre1 hre2).2.2
    have h_exists : ∃ n : ℕ, nontrivialZeroEnum n = (1 - ρ) := nontrivialZeroEnum_covers_all (1 - ρ) h1mρ_zero h1mρ_re1 h1mρ_re2
    exact h_in_T (1 - ρ) (Or.inl h_exists)
  have h_pair_diff : (melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
                       (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ)) =
                     melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ) := by
    have h1 : melinTransform f2.toTestFunction ρ - melinTransform f1.toTestFunction ρ =
               melinTransform g'.toTestFunction ρ := h_super ρ hρ_in_T
    have h2 : melinTransform f2.toTestFunction (1 - ρ) - melinTransform f1.toTestFunction (1 - ρ) =
               melinTransform g'.toTestFunction (1 - ρ) := h_super (1 - ρ) h1mρ_in_T
    calc
      (melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
        (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ))
        = (melinTransform f2.toTestFunction ρ - melinTransform f1.toTestFunction ρ) +
          (melinTransform f2.toTestFunction (1 - ρ) - melinTransform f1.toTestFunction (1 - ρ)) := by ring
      _ = melinTransform g'.toTestFunction ρ + melinTransform g'.toTestFunction (1 - ρ) := by rw [h1, h2]
      _ = melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ) := h_pair_eq
  have h_triv_eq : trivialZeroContribution f1.toTestFunction = trivialZeroContribution f2.toTestFunction := by
    have h_all_triv : ∀ (k : ℕ), melinTransform f1.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                               melinTransform f2.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) := by
      intro k
      let s : ℂ := ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)
      have hs_in_T : s ∈ T := h_in_T s (Or.inr (Or.inl ⟨k, rfl⟩))
      have h_diff : melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s = 0 := by
        rw [h_super s hs_in_T, h_triv_zero k]
      have h_eq : melinTransform f2.toTestFunction s = melinTransform f1.toTestFunction s := sub_eq_zero.mp h_diff
      exact h_eq.symm
    have h_pole_eq : melinTransform f1.toTestFunction (1 : ℂ) = melinTransform f2.toTestFunction (1 : ℂ) := by
      have h1_in_T : (1 : ℂ) ∈ T := h_in_T (1 : ℂ) (Or.inr (Or.inr rfl))
      have h_diff : melinTransform f2.toTestFunction (1 : ℂ) - melinTransform f1.toTestFunction (1 : ℂ) = 0 := by
        rw [h_super (1 : ℂ) h1_in_T, h_pole_zero]
      have h_eq : melinTransform f2.toTestFunction (1 : ℂ) = melinTransform f1.toTestFunction (1 : ℂ) := sub_eq_zero.mp h_diff
      exact h_eq.symm
    exact trivialZeroContribution_extensionality f1.toTestFunction f2.toTestFunction h_all_triv h_pole_eq
  exact ⟨f1, f2, h_pts, h_other, h_pair_diff, h_triv_eq⟩"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 3b done: spectral_preserving_perturbation_build uses countable version')
