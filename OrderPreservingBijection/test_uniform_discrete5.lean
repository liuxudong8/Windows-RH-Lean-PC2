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
  set N : ℕ := Nat.ceil (2 * M / δ) + 1 with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]
    apply Nat.succ_pos
  have h_main : ∀ (x : ℝ), x ∈ S → ∃ (k : ℕ), k < N ∧ -M + (k : ℝ) * δ ≤ x ∧ x < -M + ((k : ℝ) + 1) * δ := by
    intro x hx
    have hx1 : -M ≤ x := by have h : |x| ≤ M := hM x hx; linarith [abs_le.mp h]
    have hx2 : x ≤ M := by have h : |x| ≤ M := hM x hx; linarith [abs_le.mp h]
    set k : ℕ := Nat.floor ((x + M) / δ) with hk_def
    have hk1 : (k : ℝ) ≤ (x + M) / δ := Nat.floor_le _
    have hk2 : (x + M) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (x + M) / δ ≤ 2 * M / δ := by gcongr <;> linarith
    have h4 : (k : ℝ) ≤ 2 * M / δ := by linarith
    have h5 : 2 * M / δ ≤ (Nat.ceil (2 * M / δ) : ℝ) := Nat.le_ceil (2 * M / δ)
    have h6 : (k : ℝ) ≤ (Nat.ceil (2 * M / δ) : ℝ) := by linarith
    have h7 : k ≤ Nat.ceil (2 * M / δ) := by
      exact Nat.cast_le.mp h6
    have hk_lt_N : k < N := by
      rw [hN_def]
      exact Nat.lt_succ_of_le h7
    have h6' : -M + (k : ℝ) * δ ≤ x := by
      have h7 : (k : ℝ) * δ ≤ x + M := by
        calc (k : ℝ) * δ ≤ ((x + M) / δ) * δ := by gcongr
          _ = x + M := by field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h8 : x < -M + ((k : ℝ) + 1) * δ := by
      have h9 : x + M < ((k : ℝ) + 1) * δ := by
        calc x + M = ((x + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ < ((k : ℝ) + 1) * δ := by gcongr
      linarith
    exact ⟨k, hk_lt_N, h6', h8⟩
  choose k hk using h_main
  let f : ℝ → Fin N := fun x =>
    if hx : x ∈ S then ⟨k x hx, (hk x hx).1⟩ else ⟨0, hN_pos⟩
  have h_inj_on : Set.InjOn f S := by
    intro x hx y hy h_eq
    by_cases hxy : x = y
    · exact hxy
    · have h9 : |x - y| ≥ ε := hε x y hx hy hxy
      have hfx : f x = (⟨k x hx, (hk x hx).1⟩ : Fin N) := by
        simp [f, hx]
      have hfy : f y = (⟨k y hy, (hk y hy).1⟩ : Fin N) := by
        simp [f, hy]
      have hk_eq : k x hx = k y hy := by
        have h10 : f x = f y := h_eq
        rw [hfx, hfy] at h10
        exact_mod_cast h10
      rcases hk x hx with ⟨_, hx_lo, hx_hi⟩
      rcases hk y hy with ⟨_, hy_lo, hy_hi⟩
      have h10 : |x - y| < ε := by
        have h11 : x < -M + ((k x hx : ℝ) + 1) * δ := hx_hi
        have h12 : -M + (k x hx : ℝ) * δ ≤ y := by
          have h13 : k y hy = k x hx := hk_eq.symm
          rw [h13] at hy_lo
          exact hy_lo
        have h14 : y < -M + ((k x hx : ℝ) + 1) * δ := by
          have h15 : k y hy = k x hx := hk_eq.symm
          rw [h15] at hy_hi
          exact hy_hi
        have h16 : -M + (k x hx : ℝ) * δ ≤ x := hx_lo
        have h17 : |x - y| < δ := by rw [abs_lt] <;> constructor <;> linarith
        have h18 : δ = ε / 2 := hδ_def
        rw [h18] at h17; linarith
      linarith
  have h_image_subset : f '' S ⊆ (Set.univ : Set (Fin N)) := by
    intro z _
    exact Set.mem_univ z
  have h_image_finite : (f '' S).Finite := Set.Finite.subset (Set.toFinite _) h_image_subset
  exact Set.Finite.of_finite_image h_image_finite h_inj_on

end RHSpectralDuality
