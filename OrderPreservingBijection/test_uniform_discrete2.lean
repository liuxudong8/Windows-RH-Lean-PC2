import OrderPreservingBijection.stage_4

open OrderPreservingBijection

namespace RHSpectralDuality

theorem bounded_uniformly_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (x : ℝ), x ∈ S → |x| ≤ M)
    (h_uniform_discrete : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x y : ℝ), x ∈ S → y ∈ S → x ≠ y → |x - y| ≥ ε) :
    Set.Finite S := by
  rcases h_bounded with ⟨M, hM_pos, hM⟩
  rcases h_uniform_discrete with ⟨ε, hε_pos, hε⟩
  let δ := ε / 2
  have hδ_pos : 0 < δ := by positivity
  let N : ℕ := Nat.ceil (2 * M / δ) + 1
  -- 对每个 x ∈ S，找到 k : Fin N 使 x ∈ [-M + k*δ, -M + (k+1)*δ)
  have h_index : ∀ (x : ℝ), x ∈ S → ∃ (k : ℕ), k < N ∧ -M + (k : ℝ) * δ ≤ x ∧ x < -M + ((k : ℝ) + 1) * δ := by
    intro x hx
    have hx1 : -M ≤ x := by
      have h : |x| ≤ M := hM x hx
      linarith [abs_le.mp h]
    have hx2 : x ≤ M := by
      have h : |x| ≤ M := hM x hx
      linarith [abs_le.mp h]
    let k : ℕ := Nat.floor ((x + M) / δ)
    have hk1 : (k : ℝ) ≤ (x + M) / δ := Nat.floor_le _
    have hk2 : (x + M) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk_lt_N : k < N := by
      have h3 : (x + M) / δ ≤ 2 * M / δ := by gcongr <;> linarith
      have h4 : (k : ℝ) ≤ 2 * M / δ := by linarith
      have h5 : k ≤ Nat.ceil (2 * M / δ) := by exact_mod_cast Nat.le_ceil _
      exact Nat.lt_succ_of_le h5
    have h6 : -M + (k : ℝ) * δ ≤ x := by
      have h7 : (k : ℝ) * δ ≤ x + M := by
        calc (k : ℝ) * δ ≤ ((x + M) / δ) * δ := by gcongr
          _ = x + M := by field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h8 : x < -M + ((k : ℝ) + 1) * δ := by
      have h9 : x + M < ((k : ℝ) + 1) * δ := by
        calc x + M = ((x + M) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ < ((k : ℝ) + 1) * δ := by gcongr
      linarith
    exact ⟨k, hk_lt_N, h6, h8⟩
  choose k hk using h_index
  have hk_lt_N : ∀ x hx, (k x hx) < N := fun x hx => (hk x hx).1
  have h_inj : ∀ (x y : ℝ), x ∈ S → y ∈ S → k x (by assumption) = k y (by assumption) → x = y := by
    intro x y hx hy h_eq
    by_cases hxy : x = y
    · exact hxy
    · have h9 : |x - y| ≥ ε := hε x y hx hy hxy
      have h10 : k x hx = k y hy := h_eq
      rcases hk x hx with ⟨_, hx1, hx2⟩
      rcases hk y hy with ⟨_, hy1, hy2⟩
      rw [h10] at hy1 hy2
      have h11 : |x - y| < ε := by
        have h12 : x < -M + ((k x hx : ℝ) + 1) * δ := hx2
        have h13 : -M + (k x hx : ℝ) * δ ≤ y := hy1
        have h14 : y < -M + ((k x hx : ℝ) + 1) * δ := hy2
        have h15 : -M + (k x hx : ℝ) * δ ≤ x := hx1
        have h16 : |x - y| < δ := by
          rw [abs_lt] <;> constructor <;> linarith
        have h17 : δ = ε / 2 := rfl
        rw [h17] at h16
        linarith
      linarith
  let f : S → Fin N := fun p => ⟨k p.val p.property, hk_lt_N p.val p.property⟩
  have hf_inj : Function.Injective f := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    have h1 : k x hx = k y hy := by
      simpa [f, Subtype.ext_iff] using h_eq
    have h2 : x = y := h_inj x y hx hy h1
    exact Subtype.ext h2
  have h_finite : Set.Finite (Set.univ : Set S) := Set.Finite.of_injective f hf_inj
  simpa [Set.finite_coe_iff] using h_finite

end RHSpectralDuality
