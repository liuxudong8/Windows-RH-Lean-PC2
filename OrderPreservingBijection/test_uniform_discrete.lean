import OrderPreservingBijection.stage_4

open OrderPreservingBijection

namespace RHSpectralDuality

/-- 有界一致离散集有限（正确定理）：
    如果 S ⊆ ℝ 有界且一致离散（∃ ε > 0, ∀ x y ∈ S, x ≠ y → |x-y| ≥ ε），则 S 有限。
    证明：把有界区间分成有限个长度为 ε/2 的子区间，每个子区间最多含一个 S 中的点。 -/
theorem bounded_uniformly_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (x : ℝ), x ∈ S → |x| ≤ M)
    (h_uniform_discrete : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x y : ℝ), x ∈ S → y ∈ S → x ≠ y → |x - y| ≥ ε) :
    Set.Finite S := by
  rcases h_bounded with ⟨M, hM_pos, hM⟩
  rcases h_uniform_discrete with ⟨ε, hε_pos, hε⟩
  let δ := ε / 2
  have hδ_pos : 0 < δ := by positivity
  -- 把 [-M, M] 分成有限个长度为 δ 的区间
  let N : ℕ := Nat.ceil (2 * M / δ)
  have hN_pos : 0 < N := by
    apply Nat.ceil_pos.mpr
    positivity
  let intervals : ℕ → Set ℝ := fun k => Set.Icc (-M + (k : ℝ) * δ) (-M + ((k : ℝ) + 1) * δ)
  have h_cover : (Set.Icc (-M) M) ⊆ ⋃ k ∈ Finset.range N, intervals k := by
    intro x hx
    have hx1 : -M ≤ x := hx.1
    have hx2 : x ≤ M := hx.2
    let k : ℕ := Nat.floor ((x + M) / δ)
    have hk_lt_N : k < N := by
      have h1 : (x + M) / δ ≤ 2 * M / δ := by
        gcongr
        <;> linarith
      have h2 : (k : ℝ) ≤ (x + M) / δ := Nat.floor_le ((x + M) / δ)
      have h3 : (k : ℝ) ≤ 2 * M / δ := by linarith
      have h4 : k ≤ N := by
        exact_mod_cast Nat.le_ceil (2 * M / δ)
      exact Nat.lt_succ_of_le h4
    have hk_in : k ∈ Finset.range N := Finset.mem_range.mpr hk_lt_N
    have h5 : -M + (k : ℝ) * δ ≤ x := by
      have h6 : (k : ℝ) ≤ (x + M) / δ := Nat.floor_le ((x + M) / δ)
      have h7 : (k : ℝ) * δ ≤ x + M := by
        calc
          (k : ℝ) * δ ≤ ((x + M) / δ) * δ := by gcongr
          _ = x + M := by
            field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h6 : x ≤ -M + ((k : ℝ) + 1) * δ := by
      have h7 : (x + M) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one ((x + M) / δ)
      have h8 : x + M < ((k : ℝ) + 1) * δ := by
        calc
          x + M = ((x + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ < ((k : ℝ) + 1) * δ := by gcongr
      linarith
    have h9 : x ∈ intervals k := ⟨h5, h6⟩
    exact Set.subset_sUnion_of_mem hk_in h9
  have hS_sub : S ⊆ Set.Icc (-M) M := by
    intro x hx
    have h1 : |x| ≤ M := hM x hx
    have h2 : -M ≤ x := by linarith [abs_le.mp h1]
    have h3 : x ≤ M := by linarith [abs_le.mp h1]
    exact ⟨h2, h3⟩
  have hS_sub_union : S ⊆ ⋃ k ∈ Finset.range N, intervals k :=
    Set.Subset.trans hS_sub h_cover
  -- 每个 intervals k 最多含一个 S 中的点
  have h_one_per_interval : ∀ k ∈ Finset.range N, Set.Finite (S ∩ intervals k) := by
    intro k _
    by_cases h : (S ∩ intervals k).Nonempty
    · rcases h with ⟨x, hx⟩
      have hxS : x ∈ S := hx.1
      have hxI : x ∈ intervals k := hx.2
      have h_eq : S ∩ intervals k = {x} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hyS, hyI⟩
          by_cases hxy : y = x
          · exact hxy
          · have h9 : |y - x| ≥ ε := hε y x hyS hxS hxy
            have h10 : y ∈ intervals k := hyI
            have h11 : x ∈ intervals k := hxI
            have h12 : |y - x| < ε := by
              have h13 : y ∈ Set.Icc (-M + (k : ℝ) * δ) (-M + ((k : ℝ) + 1) * δ) := h10
              have h14 : x ∈ Set.Icc (-M + (k : ℝ) * δ) (-M + ((k : ℝ) + 1) * δ) := h11
              have h15 : |y - x| ≤ δ := by
                rw [abs_le]
                constructor <;> linarith
              linarith [show δ = ε / 2 from rfl]
            linarith
        · rintro rfl
          exact ⟨hxS, hxI⟩
      rw [h_eq]
      exact Set.finite_singleton x
    · have h_empty : S ∩ intervals k = (∅ : Set ℝ) := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty]
      exact Set.finite_empty
  have h_finite_union : Set.Finite (⋃ k ∈ Finset.range N, S ∩ intervals k) :=
    Set.Finite.biUnion (Finset.finite_toSet _) h_one_per_interval
  have hS_eq : S = ⋃ k ∈ Finset.range N, S ∩ intervals k := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hxS
      have hx_in_union : x ∈ ⋃ k ∈ Finset.range N, intervals k := hS_sub_union hxS
      rcases Set.mem_iUnion.mp hx_in_union with ⟨k, hk, hxI⟩
      exact ⟨k, hk, hxS, hxI⟩
    · rintro ⟨k, _, hxS, _⟩
      exact hxS
  rw [hS_eq]
  exact h_finite_union

end RHSpectralDuality
