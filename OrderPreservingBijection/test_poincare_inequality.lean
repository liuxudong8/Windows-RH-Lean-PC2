import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MollifiedFunction
import Mathlib.Analysis.Calculus.FDeriv.Basic

open OrderPreservingBijection
open MeasureTheory Set Complex
open Filter Topology

/-- Poincaré 不等式测试 -/
theorem test_poincare_inequality (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (B : ℝ),
      ContDiff ℝ 2 h.toFun →
      (∀ (x : ℝ), ‖(deriv (deriv h.toFun) x)‖ ≤ B) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
  intro h B hC2 h_deriv_bound h_left h_right x
  have hB_nonneg : 0 ≤ B := by
    have h1 : ‖(deriv (deriv h.toFun) 0)‖ ≤ B := h_deriv_bound 0
    have h2 : 0 ≤ ‖(deriv (deriv h.toFun) 0)‖ := by positivity
    exact le_trans h2 h1
  by_cases h_x_lt : x < ε₀
  · -- 情况 1：x < ε₀
    have h1 : h.toFun x = 0 := h_left x h_x_lt
    have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
      rw [h1]
      have h_norm_zero : ‖(0 : ℂ)‖ = 0 := by simp
      rw [h_norm_zero]
      have h_nonneg : 0 ≤ (R₀ - ε₀)^2 * B := by
        exact mul_nonneg (sq_nonneg (R₀ - ε₀)) hB_nonneg
      exact h_nonneg
    exact h_main
  · -- 情况 2：x ≥ ε₀
    by_cases h_x_gt : x > R₀
    · -- 情况 2a：x > R₀
      have h2 : h.toFun x = 0 := h_right x h_x_gt
      have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
        rw [h2]
        have h_norm_zero : ‖(0 : ℂ)‖ = 0 := by simp
        rw [h_norm_zero]
        have h_nonneg : 0 ≤ (R₀ - ε₀)^2 * B := by
          exact mul_nonneg (sq_nonneg (R₀ - ε₀)) hB_nonneg
        exact h_nonneg
      exact h_main
    · -- 情况 2b：ε₀ ≤ x ≤ R₀
      have h_x_le_R₀ : x ≤ R₀ := by linarith
      have h_x_ge_ε₀ : ε₀ ≤ x := by linarith
      -- 步骤 1：h.toFun 是连续的（从 hC2）
      have h_cont : Continuous h.toFun := ContDiff.continuous hC2
      have h_contAt : ContinuousAt h.toFun ε₀ := h_cont.continuousAt
      have h_tendsto : Tendsto h.toFun (𝓝 ε₀) (𝓝 (h.toFun ε₀)) := h_contAt.tendsto
      -- 步骤 2：h.toFun ε₀ = 0（从连续性 + h_left）
      have h_at_ε₀ : h.toFun ε₀ = 0 := by
        -- 左极限：从 h_left
        have h_left_tendsto : Tendsto h.toFun (𝓝[<] ε₀) (𝓝 0) := by
          rw [Filter.tendsto_def]
          intro s hs
          have h0_in_s : (0 : ℂ) ∈ s := mem_of_mem_nhds hs
          have h1 : {x : ℝ | x < ε₀ → h.toFun x ∈ s} = Set.univ := by
            ext x
            simp only [Set.mem_univ, Set.mem_setOf_eq, iff_true]
            intro hx
            have h2 : h.toFun x = 0 := h_left x hx
            rw [h2]
            exact h0_in_s
          have h3 : {x : ℝ | x < ε₀ → h.toFun x ∈ s} ∈ 𝓝 ε₀ := by
            rw [h1]
            exact univ_mem
          have h4 : {x : ℝ | h.toFun x ∈ s} ∈ 𝓝[<] ε₀ := by
            have h5 : {x : ℝ | h.toFun x ∈ s} ∈ 𝓝 ε₀ ⊓ 𝓟 (Set.Iio ε₀) := by
              rw [Filter.mem_inf_principal]
              simpa using h3
            simpa [nhdsWithin] using h5
          exact h4
        -- 左极限（从连续性）：从双边极限限制到左邻域
        have h_right_tendsto : Tendsto h.toFun (𝓝[<] ε₀) (𝓝 (h.toFun ε₀)) :=
          tendsto_nhdsWithin_of_tendsto_nhds h_contAt
        -- 用极限的唯一性证明
        exact tendsto_nhds_unique h_right_tendsto h_left_tendsto
      -- 数学：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt
      -- |h(x)| ≤ (x-ε₀)²/2 · ‖h''‖_∞ ≤ (R₀-ε₀)² · B
      have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
        sorry
      exact h_main
