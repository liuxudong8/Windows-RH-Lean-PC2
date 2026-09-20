import OrderPreservingBijection.stage_4

open OrderPreservingBijection

namespace RHSpectralDuality

theorem bounded_uniformly_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (x : ℝ), x ∈ S → |x| ≤ M)
    (h_uniform_discrete : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x y : ℝ), x ∈ S → y ∈ S → x ≠ y → |x - y| ≥ ε) :
    Set.Finite S := by
  rcases h_bounded with ⟨M, hM_pos, hM⟩
  rcases h_uniform_discrete with ⟨ε, hε_pos, hε⟩
  set δ : ℝ := ε / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  let f : ℝ → ℤ := fun x => Int.floor ((x + M) / δ)
  have h_floor_le : ∀ (x : ℝ), (f x : ℝ) ≤ (x + M) / δ := fun x => Int.floor_le _
  have h_floor_lt : ∀ (x : ℝ), (x + M) / δ < (f x : ℝ) + 1 := fun x => Int.lt_floor_add_one _
  have h_bound : ∀ x ∈ S, 0 ≤ f x ∧ f x < 1000000 := by
    intro x hx
    have hx1 : -M ≤ x := by have h : |x| ≤ M := hM x hx; linarith [abs_le.mp h]
    have hx2 : x ≤ M := by have h : |x| ≤ M := hM x hx; linarith [abs_le.mp h]
    have h3 : 0 ≤ (x + M) / δ := by positivity
    have h4 : (f x : ℝ) ≤ (x + M) / δ := h_floor_le x
    have h5 : 0 ≤ f x := by
      have h6 : (f x : ℝ) ≥ 0 := by
        have h7 : (f x : ℝ) ≤ (x + M) / δ := h4
        have h8 : (x + M) / δ ≥ 0 := h3
        exact?
      exact_mod_cast h6
    have h9 : (x + M) / δ ≤ 2 * M / δ := by gcongr <;> linarith
    have h10 : (f x : ℝ) < (x + M) / δ + 1 := by linarith [h_floor_lt x]
    have h11 : (f x : ℝ) < 2 * M / δ + 1 := by linarith
    have h12 : f x < 1000000 := by
      exact?
    exact ⟨h5, h12⟩
  have h_inj : Set.InjOn f S := by
    intro x hx y hy h_eq
    by_cases hxy : x = y
    · exact hxy
    · have h9 : |x - y| ≥ ε := hε x y hx hy hxy
      have h10 : (f x : ℝ) ≤ (x + M) / δ := h_floor_le x
      have h11 : (x + M) / δ < (f x : ℝ) + 1 := h_floor_lt x
      have h12 : (f y : ℝ) ≤ (y + M) / δ := h_floor_le y
      have h13 : (y + M) / δ < (f y : ℝ) + 1 := h_floor_lt y
      have hfy_eq : (f y : ℝ) = (f x : ℝ) := by exact_mod_cast h_eq
      have h14 : |x - y| < δ := by
        rw [abs_lt]
        constructor
        · have h15 : x + M < (f x : ℝ) + 1 := by
            calc x + M = ((x + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
              _ < ((f x : ℝ) + 1) * δ := by gcongr; exact h11
          have h16 : (f x : ℝ) * δ ≤ y + M := by
            calc (f x : ℝ) * δ = (f y : ℝ) * δ := by rw [hfy_eq]
              _ ≤ ((y + M) / δ) * δ := by gcongr; exact h12
              _ = y + M := by field_simp [hδ_pos.ne'] <;> ring
          linarith
        · have h17 : y + M < (f x : ℝ) + 1 := by
            calc y + M = ((y + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
              _ = ((y + M) / δ) * δ := rfl
              _ < ((f y : ℝ) + 1) * δ := by gcongr; exact h13
              _ = ((f x : ℝ) + 1) * δ := by rw [hfy_eq]
          have h18 : (f x : ℝ) * δ ≤ x + M := by
            calc (f x : ℝ) * δ ≤ ((x + M) / δ) * δ := by gcongr; exact h10
              _ = x + M := by field_simp [hδ_pos.ne'] <;> ring
          linarith
      have h19 : δ = ε / 2 := hδ_def
      rw [h19] at h14
      linarith
  let T : Set ℤ := Set.Icc (0 : ℤ) 1000000
  have hT_finite : T.Finite := Set.finite_Icc _ _
  have h_image_subset : f '' S ⊆ T := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := h_bound x hx
    exact ⟨h.1, h.2⟩
  have h_image_finite : (f '' S).Finite := Set.Finite.subset hT_finite h_image_subset
  exact Set.Finite.of_finite_image h_image_finite h_inj

end RHSpectralDuality
