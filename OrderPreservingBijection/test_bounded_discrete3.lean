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
  choose ε hε using fun (ℓ : ℝ) (hℓ : ℓ ∈ S) => h_discrete ℓ hℓ
  have hε_pos : ∀ (ℓ : ℝ), ℓ ∈ S → 0 < ε ℓ hℓ := fun ℓ hℓ => (hε ℓ hℓ).1
  have hε_prop : ∀ (ℓ : ℝ), ℓ ∈ S → ∀ (ℓ' : ℝ), ℓ' ∈ S → |ℓ' - ℓ| < ε ℓ hℓ → ℓ' = ℓ :=
    fun ℓ hℓ => (hε ℓ hℓ).2
  let U : ℝ → Set ℝ := fun ℓ => Set.Ioo (ℓ - ε ℓ (hS_sub_K (show ℓ ∈ S from by tauto))) (ℓ + ε ℓ (hS_sub_K (show ℓ ∈ S from by tauto)))
  sorry

end RHSpectralDuality
