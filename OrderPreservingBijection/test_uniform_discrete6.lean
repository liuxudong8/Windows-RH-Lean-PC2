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
  let interval (k : ℕ) : Set ℝ := Set.Icc (-M + (k : ℝ) * δ) (-M + ((k : ℝ) + 1) * δ)
  -- 每个 interval k 最多含一个 S 中的点
  have h_one_point : ∀ k : ℕ, Set.Finite (S ∩ interval k) := by
    intro k
    by_cases h : (S ∩ interval k).Nonempty
    · rcases h with ⟨x, hx⟩
      have hxS : x ∈ S := hx.1
      have hxI : x ∈ interval k := hx.2
      have h_eq : S ∩ interval k = {x} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hyS, hyI⟩
          by_cases hxy : y = x
          · exact hxy
          · have h9 : |y - x| ≥ ε := hε y x hyS hxS hxy
            have h10 : y ∈ interval k := hyI
            have h11 : x ∈ interval k := hxI
            have h12 : |y - x| ≤ δ := by
              rcases h10 with ⟨y1, y2⟩
              rcases h11 with ⟨x1, x2⟩
              rw [abs_le] <;> constructor <;> linarith
            have h13 : δ = ε / 2 := hδ_def
            rw [h13] at h12
            linarith
        · rintro rfl
          exact ⟨hxS, hxI⟩
      rw [h_eq]
      exact Set.finite_singleton x
    · have h_empty : S ∩ interval k = (∅ : Set ℝ) := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty]
      exact Set.finite_empty
  -- intervals 覆盖 [-M, M]
  have h_cover : (Set.Icc (-M) M) ⊆ ⋃ k ∈ Finset.range N, interval k := by
    intro x hx
    have hx1 : -M ≤ x := hx.1
    have hx2 : x ≤ M := hx.2
    let k : ℕ := Nat.floor ((x + M) / δ)
    have hk1 : (k : ℝ) ≤ (x + M) / δ := by exact?
    have hk2 : (x + M) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (x + M) / δ ≤ 2 * M / δ := by gcongr <;> linarith
    have h4 : (k : ℝ) ≤ 2 * M / δ := by linarith
    have h5 : 2 * M / δ ≤ (Nat.ceil (2 * M / δ) : ℝ) := Nat.le_ceil (2 * M / δ)
    have h6 : (k : ℝ) ≤ (Nat.ceil (2 * M / δ) : ℝ) := by linarith
    have h7 : k ≤ Nat.ceil (2 * M / δ) := by exact?
    have hk_lt_N : k < N := by
      rw [hN_def]
      exact Nat.lt_succ_of_le h7
    have hk_in : k ∈ Finset.range N := Finset.mem_range.mpr hk_lt_N
    have h6' : -M + (k : ℝ) * δ ≤ x := by
      have h7 : (k : ℝ) * δ ≤ x + M := by
        calc (k : ℝ) * δ ≤ ((x + M) / δ) * δ := by gcongr
          _ = x + M := by field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h8 : x ≤ -M + ((k : ℝ) + 1) * δ := by
      have h9 : x + M ≤ ((k : ℝ) + 1) * δ := by
        calc x + M = ((x + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ ≤ ((k : ℝ) + 1) * δ := by gcongr; exact hk2.le
      linarith
    have h9 : x ∈ interval k := ⟨h6', h8⟩
    exact Set.subset_sUnion_of_mem hk_in h9
  have hS_sub : S ⊆ Set.Icc (-M) M := by
    intro x hx
    have h1 : |x| ≤ M := hM x hx
    have h2 : -M ≤ x := by linarith [abs_le.mp h1]
    have h3 : x ≤ M := by linarith [abs_le.mp h1]
    exact ⟨h2, h3⟩
  have hS_eq : S = ⋃ k ∈ Finset.range N, S ∩ interval k := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hxS
      have hx_in_union : x ∈ ⋃ k ∈ Finset.range N, interval k := h_cover (hS_sub hxS)
      rcases hx_in_union with ⟨k, hk, hxI⟩
      exact ⟨k, hk, hxS, hxI⟩
    · rintro ⟨k, _, hxS, _⟩
      exact hxS
  rw [hS_eq]
  have h_one_point' : ∀ k ∈ (Finset.range N : Set ℕ), Set.Finite (S ∩ interval k) := by
    intro k _
    exact h_one_point k
  exact Set.Finite.biUnion (Finset.finite_toSet _) h_one_point'

end RHSpectralDuality
