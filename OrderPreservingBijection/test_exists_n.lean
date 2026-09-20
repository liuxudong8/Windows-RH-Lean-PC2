import OrderPreservingBijection.test_exists_base

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助：有限类型上可数集合的 iUnion 可数。 -/
lemma finite_iUnion_countable {α : Type*} [Fintype α] {β : Type*} {f : α → Set β}
    (h : ∀ i, Set.Countable (f i)) : Set.Countable (⋃ i : α, f i) := by
  have h1 : (⋃ i : α, f i) = ⋃ i ∈ (↑(Finset.univ : Finset α) : Set α), f i := by
    ext x; simp
  rw [h1]
  have h2 : (↑(Finset.univ : Finset α) : Set α).Finite := Finset.finite_toSet _
  have h3 : (↑(Finset.univ : Finset α) : Set α).Countable := Set.Finite.countable h2
  exact Set.Countable.biUnion h3 (fun i _ => h i)

/-- 推广的存在性定理：对任意有限点集 s : Fin n → ℂ（两两不同且非零），
    存在 a > 1 使 a^sᵢ ≠ 1 且 a^sᵢ ≠ a^sⱼ（i ≠ j）。 -/
theorem exists_base_for_finite_set (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) :
    ∃ (a : ℝ), 1 < a ∧
      (∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1) ∧
      (∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ))) := by
  let S1 : Set ℝ := ⋃ i : Fin n, {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1}
  let S2 : Set ℝ := ⋃ p : Fin n × Fin n, (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ))
  have hf1 : ∀ i : Fin n, Set.Countable {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1} :=
    fun i => exp_c_t_eq_one_set_countable (s i) (h_ne_zero i)
  have hf2 : ∀ p : Fin n × Fin n, Set.Countable (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) := by
    classical
    intro p
    by_cases hne : p.1 ≠ p.2
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} := by
        rw [if_pos hne]
      rw [h_if]
      have h_diff : s p.1 - s p.2 ≠ 0 := by
        intro h'
        have h1 : s p.1 = s p.1 - s p.2 + s p.2 := by ring
        have h'' : s p.1 = s p.2 := by
          rw [h1, h'] <;> ring
        exact hne (h_inj h'')
      exact exp_c_t_eq_one_set_countable (s p.1 - s p.2) h_diff
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = (∅ : Set ℝ) := by
        rw [if_neg hne]
      rw [h_if]
      exact Set.countable_empty
  have hS1 : Set.Countable S1 := by
    simpa [S1] using finite_iUnion_countable hf1
  have hS2 : Set.Countable S2 := by
    simpa [S2] using finite_iUnion_countable hf2
  let S := S1 ∪ S2
  have hUnion : Set.Countable S := Set.Countable.union hS1 hS2
  have h_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := positive_reals_uncountable
  have h_exists : ∃ (t : ℝ), t ∈ Set.Ioi (0 : ℝ) ∧ t ∉ S := by
    by_contra h
    push_neg at h
    have h_sub : Set.Ioi (0 : ℝ) ⊆ S := fun t ht => h t ht
    have h_contra : Set.Countable (Set.Ioi (0 : ℝ)) := Set.Countable.mono h_sub hUnion
    exact h_uncountable h_contra
  rcases h_exists with ⟨t, ht_pos, ht_notin⟩
  have h_t_pos' : 0 < t := ht_pos
  let a : ℝ := Real.exp t
  have ha_gt_one : 1 < a := by
    have h2 : Real.exp t > Real.exp 0 := Real.exp_strictMono h_t_pos'
    have h3 : Real.exp 0 = 1 := by simp
    rw [h3] at h2
    exact h2
  have h_log_a : Real.log a = t := by
    have h4 : a = Real.exp t := rfl
    rw [h4]
    exact Real.log_exp t
  have ht_notin1 : t ∉ S1 := by
    intro h
    have h' : t ∈ S := Or.inl h
    exact ht_notin h'
  have ht_notin2 : t ∉ S2 := by
    intro h
    have h' : t ∈ S := Or.inr h
    exact ht_notin h'
  have h1 : ∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1 := by
    intro i
    rw [h_log_a]
    intro h
    have h' : t ∈ S1 := by
      apply Set.mem_iUnion.mpr
      exact ⟨i, h⟩
    exact ht_notin1 h'
  have h2 : ∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ)) := by
    intro i j hne
    rw [h_log_a]
    intro h_eq
    have h3 : Complex.exp ((s i - s j) * (t : ℂ)) = 1 := by
      have h41 : (s i - s j) * (t : ℂ) = s i * (t : ℂ) - s j * (t : ℂ) := by ring
      rw [h41]
      have h42 : Complex.exp (s i * (t : ℂ) - s j * (t : ℂ)) = Complex.exp (s i * (t : ℂ)) * Complex.exp (-(s j * (t : ℂ))) := by
        rw [← Complex.exp_add] <;> ring
      rw [h42]
      have h43 : Complex.exp (-(s j * (t : ℂ))) = (Complex.exp (s j * (t : ℂ)))⁻¹ := by rw [Complex.exp_neg]
      rw [h43, h_eq] <;> field_simp <;> ring
    have h' : t ∈ S2 := by
      apply Set.mem_iUnion.mpr
      refine ⟨(i, j), ?_⟩
      have h4 : (if (i, j).1 ≠ (i, j).2 then {t : ℝ | Complex.exp ((s (i, j).1 - s (i, j).2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s i - s j) * (t : ℂ)) = 1} := by
        rw [if_pos hne] <;> rfl
      rw [h4]
      exact h3
    exact ht_notin2 h'
  exact ⟨a, ha_gt_one, h1, h2⟩

end RHSpectralDuality
end OrderPreservingBijection
