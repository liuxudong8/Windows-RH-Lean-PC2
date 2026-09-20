import OrderPreservingBijection.stage_4
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

namespace RHSpectralDuality

theorem test_bounded_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (ℓ : ℝ), ℓ ∈ S → |ℓ| ≤ M)
    (h_discrete : ∀ (ℓ : ℝ), ℓ ∈ S →
      ∃ (ε : ℝ), 0 < ε ∧ ∀ (ℓ' : ℝ), ℓ' ∈ S → |ℓ' - ℓ| < ε → ℓ' = ℓ) :
    Set.Finite S := by
  rcases h_bounded with ⟨M, hM_pos, hM⟩
  let K : Set ℝ := Set.Icc (-M) M
  have hK_compact : IsCompact K := isCompact_Icc
  have hS_sub_K : S ⊆ K := by
    intro ℓ hℓ
    have h1 : |ℓ| ≤ M := hM ℓ hℓ
    have h2 : -M ≤ ℓ := by linarith [abs_le.mp h1]
    have h3 : ℓ ≤ M := by linarith [abs_le.mp h1]
    exact ⟨h2, h3⟩
  -- 对每个 ℓ ∈ S，选一个开球 B(ℓ, ε_ℓ) 使 B ∩ S = {ℓ}
  choose ε hε_pos hε using fun (ℓ : ℝ) (hℓ : ℓ ∈ S) => h_discrete ℓ hℓ
  let U : ℝ → Set ℝ := fun ℓ => Set.Ioo (ℓ - ε ℓ (hS_sub_K hℓ)) (ℓ + ε ℓ (hS_sub_K hℓ))
  -- 开覆盖：{U(ℓ) : ℓ ∈ S} ∪ {ℝ \ closure S}
  let V : Set (Set ℝ) := (U '' S) ∪ {K \ S}
  have h_cover : K ⊆ ⋃₀ V := by
    intro x hx
    by_cases hxS : x ∈ S
    · have h1 : U x ∈ V := by
        exact Or.inl ⟨x, hxS, rfl⟩
      have h2 : x ∈ U x := by
        simp only [U, Set.mem_Ioo]
        have hε' : 0 < ε x (hS_sub_K hxS) := hε_pos x (hS_sub_K hxS)
        constructor <;> linarith
      exact Set.subset_sUnion_of_mem h1 h2
    · have h1 : K \ S ∈ V := Or.inr (by simp)
      have h2 : x ∈ K \ S := ⟨hx, hxS⟩
      exact Set.subset_sUnion_of_mem h1 h2
  have h_finite_subcover : ∃ (V0 : Finset (Set ℝ)), ↑V0 ⊆ V ∧ K ⊆ ⋃₀ (↑V0 : Set (Set ℝ)) :=
    hK_compact.elim_finite_subcover V h_cover
  rcases h_finite_subcover with ⟨V0, hV0_sub, hV0_cover⟩
  -- 每个 U(ℓ) 只包含 S 中的一个点 ℓ
  have h_one_point : ∀ (ℓ : ℝ), ℓ ∈ S → (U ℓ) ∩ S = {ℓ} := by
    intro ℓ hℓ
    ext y
    simp only [U, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy_U, hy_S⟩
      have h3 : |y - ℓ| < ε ℓ (hS_sub_K hℓ) := by
        simp only [Set.mem_Ioo] at hy_U
        rw [abs_lt] <;> constructor <;> linarith
      exact hε ℓ (hS_sub_K hℓ) y hy_S h3
    · rintro rfl
      have h4 : ℓ ∈ U ℓ := by
        simp only [U, Set.mem_Ioo]
        have hε' : 0 < ε ℓ (hS_sub_K hℓ) := hε_pos ℓ (hS_sub_K hℓ)
        constructor <;> linarith
      exact ⟨h4, hℓ⟩
  -- S 中的每个点必须属于某个 U(ℓ) ∈ V0（因为 K \ S 不含 S 中的点）
  have hS_sub_union_U : S ⊆ ⋃ (W ∈ V0), if ∃ (ℓ : ℝ), ℓ ∈ S ∧ W = U ℓ then W else (∅ : Set ℝ) := by
    intro x hx
    have hxK : x ∈ K := hS_sub_K hx
    have h_in_cover : x ∈ ⋃₀ (↑V0 : Set (Set ℝ)) := hV0_cover hxK
    rcases Set.mem_sUnion.mp h_in_cover with ⟨W, hW_in_V0, hxW⟩
    have hW_in_V : W ∈ V := hV0_sub hW_in_V0
    rcases hW_in_V with (hW_U | hW_Kdiff)
    · rcases hW_U with ⟨ℓ, hℓS, rfl⟩
      have h5 : x ∈ U ℓ := hxW
      have h6 : x = ℓ := by
        have h7 : x ∈ (U ℓ) ∩ S := ⟨h5, hx⟩
        rw [h_one_point ℓ hℓS] at h7
        simpa using h7
      have h8 : (∃ (ℓ' : ℝ), ℓ' ∈ S ∧ U ℓ = U ℓ') := ⟨ℓ, hℓS, rfl⟩
      apply Set.subset_sUnion_of_mem (show (U ℓ) ∈ (↑V0 : Set (Set ℝ)) from hW_in_V0)
      simpa [h8] using h5
    · simp only [Set.mem_singleton_iff] at hW_Kdiff
      rw [hW_Kdiff] at hxW
      exact hxW.2 hx
  -- S 被有限个 U(ℓ) 覆盖，每个 U(ℓ) 只含一个 S 中的点，所以 S 有限
  have h_finite : Set.Finite (⋃ (W ∈ V0), if ∃ (ℓ : ℝ), ℓ ∈ S ∧ W = U ℓ then W else (∅ : Set ℝ)) := by
    apply Set.Finite.biUnion (Finset.finite_toSet V0)
    intro W _
    by_cases h : ∃ (ℓ : ℝ), ℓ ∈ S ∧ W = U ℓ
    · rcases h with ⟨ℓ, hℓS, rfl⟩
      have h9 : (U ℓ ∩ S).Finite := by
        rw [h_one_point ℓ hℓS]
        exact Set.finite_singleton _
      exact h9
    · simp [h]
      exact Set.finite_empty
  exact Set.Finite.subset h_finite hS_sub_union_U

end RHSpectralDuality
