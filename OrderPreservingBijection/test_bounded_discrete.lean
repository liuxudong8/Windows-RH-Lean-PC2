import OrderPreservingBijection.stage_4
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

namespace RHSpectralDuality

-- 测试 bounded_discrete_real_set_finite
theorem test_bounded_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (ℓ : ℝ), ℓ ∈ S → |ℓ| ≤ M)
    (h_discrete : ∀ (ℓ : ℝ), ℓ ∈ S →
      ∃ (ε : ℝ), 0 < ε ∧ ∀ (ℓ' : ℝ), ℓ' ∈ S → |ℓ' - ℓ| < ε → ℓ' = ℓ) :
    Set.Finite S := by
  rcases h_bounded with ⟨M, hM_pos, hM⟩
  have h_subset : S ⊆ Set.Icc (-M) M := by
    intro ℓ hℓ
    have h1 : |ℓ| ≤ M := hM ℓ hℓ
    exact ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
  have h_closed : IsCompact (Set.Icc (-M : ℝ) M) := isCompact_Icc
  by_contra h_inf
  have h1 : Set.Infinite S := by exact?
  have h2 : ∃ (x : ℝ), x ∈ closure S ∧ ¬ IsolatedPt S x := by
    exact?
  rcases h2 with ⟨x, hx_closure, hx_not_isolated⟩
  have hx_in_S : x ∈ S := by
    have h3 : closure S ⊆ S := by
      sorry
    exact h3 hx_closure
  have h4 : ∃ (ε : ℝ), 0 < ε ∧ ∀ (ℓ' : ℝ), ℓ' ∈ S → |ℓ' - x| < ε → ℓ' = x := h_discrete x hx_in_S
  rcases h4 with ⟨ε, hε_pos, hε⟩
  have h5 : IsolatedPt S x := by
    refine ⟨ε, hε_pos, ?_⟩
    intro y hy
    exact hε y hy
  exact hx_not_isolated h5

end RHSpectralDuality
