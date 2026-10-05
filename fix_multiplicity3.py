f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old_proof = """  intro hz hre1 hre2 hne f1 f2 h_other h_triv
  have h_ne_rho : ρ ≠ 1 - ρ := by
    intro h
    have h_re : ρ.re = 1 / 2 := by
      simp [Complex.ext_iff] at h <;> linarith
    exact hne h_re
  have h_nontriv := nontrivialZeroSum_pair_localization ρ hz hre1 hre2 h_ne_rho f1 f2 h_other
  constructor
  · intro h_eq
    have h : nontrivialZeroSum f1 + trivialZeroContribution f1 =
             nontrivialZeroSum f2 + trivialZeroContribution f2 := by simpa [zetaZeroSide] using h_eq
    rw [h_triv] at h
    have h' : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by simpa using h
    have h_zero : (melinTransform f1 ρ - melinTransform f2 ρ) +
                  (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) = 0 := by
      rw [←h_nontriv, h'] <;> ring
    have h_goal : melinTransform f1 ρ + melinTransform f1 (1 - ρ) =
                  melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by
      calc
        melinTransform f1 ρ + melinTransform f1 (1 - ρ)
          = (melinTransform f1 ρ - melinTransform f2 ρ) +
            (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) +
            (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
        _ = 0 + (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by rw [h_zero]
        _ = melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by ring
    exact h_goal
  · intro h_pair
    have h_diff_zero : (melinTransform f1 ρ - melinTransform f2 ρ) +
                       (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) = 0 := by
      have h_alg : (melinTransform f1 ρ - melinTransform f2 ρ) +
                   (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) =
                   (melinTransform f1 ρ + melinTransform f1 (1 - ρ)) -
                   (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
      rw [h_alg, h_pair] <;> ring
    have h_nontriv_eq : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by
      have h : nontrivialZeroSum f1 - nontrivialZeroSum f2 = 0 := by
        rw [h_nontriv, h_diff_zero]
      exact sub_eq_zero.mp h"""

new_proof = """  intro hz hre1 hre2 hne f1 f2 h_other h_triv
  have h_ne_rho : ρ ≠ 1 - ρ := by
    intro h
    have h_re : ρ.re = 1 / 2 := by
      simp [Complex.ext_iff] at h <;> linarith
    exact hne h_re
  have h_m_pos : 0 < zeroMultiplicity ρ := zeroMultiplicity_positive_at_nontrivial_zeros ρ hz hre1 hre2
  have h_m_ne_zero : (zeroMultiplicity ρ : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_m_pos)
  have h_nontriv := nontrivialZeroSum_pair_localization ρ hz hre1 hre2 h_ne_rho f1 f2 h_other
  let pairDiff : ℂ := (melinTransform f1 ρ - melinTransform f2 ρ) +
                      (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ))
  constructor
  · intro h_eq
    have h : nontrivialZeroSum f1 + trivialZeroContribution f1 =
             nontrivialZeroSum f2 + trivialZeroContribution f2 := by simpa [zetaZeroSide] using h_eq
    rw [h_triv] at h
    have h' : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by simpa using h
    have h_mul_zero : (zeroMultiplicity ρ : ℂ) * pairDiff = 0 := by
      rw [←h_nontriv, h'] <;> ring
    have h_zero : pairDiff = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left h_m_ne_zero
    have h_goal : melinTransform f1 ρ + melinTransform f1 (1 - ρ) =
                  melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by
      calc
        melinTransform f1 ρ + melinTransform f1 (1 - ρ)
          = pairDiff + (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
        _ = 0 + (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by rw [h_zero]
        _ = melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by ring
    exact h_goal
  · intro h_pair
    have h_diff_zero : pairDiff = 0 := by
      have h_alg : pairDiff =
                   (melinTransform f1 ρ + melinTransform f1 (1 - ρ)) -
                   (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
      rw [h_alg, h_pair] <;> ring
    have h_nontriv_eq : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by
      have h : nontrivialZeroSum f1 - nontrivialZeroSum f2 = 0 := by
        rw [h_nontriv, h_diff_zero] <;> ring
      exact sub_eq_zero.mp h"""

content = content.replace(old_proof, new_proof, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 4 done: zero_side_melin_localization with multiplicity')
