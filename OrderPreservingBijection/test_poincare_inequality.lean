import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MollifiedFunction
import Mathlib.Analysis.Calculus.FDeriv.Basic

open OrderPreservingBijection
open MeasureTheory Set Complex
open Filter Topology

/-- Poincaré 不等式测试 -/
theorem test_poincare_inequality (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (B : ℝ),
      (∀ (x : ℝ), ‖(deriv (deriv h.toFun) x)‖ ≤ B) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
  intro h B h_deriv_bound h_left h_right x
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
      -- 步骤 1：h.toFun 是连续的（从 h.contDiff2）
      have h_cont : Continuous h.toFun := ContDiff.continuous h.contDiff2
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
      -- 步骤 1：证明 h(x) = ∫_{ε₀}^x h'(t) dt
      have h_eq : ∫ t in ε₀..x, deriv h.toFun t = h.toFun x - h.toFun ε₀ := by
        apply intervalIntegral.integral_deriv_eq_sub
        · -- hderiv: ∀ x ∈ uIcc ε₀ x, DifferentiableAt ℝ h.toFun x
          intro y hy
          have h_diff : Differentiable ℝ h.toFun :=
            ContDiff.differentiable h.contDiff2 (by norm_num)
          exact h_diff y
        · -- hint: IntervalIntegrable (deriv h.toFun) volume ε₀ x
          have h_cont : Continuous (deriv h.toFun) :=
            ContDiff.continuous_deriv h.contDiff2 (by norm_num)
          exact h_cont.intervalIntegrable ε₀ x
      -- 步骤 2：因为 h(ε₀) = 0，所以 h(x) = ∫_{ε₀}^x h'(t) dt
      have h_eq2 : ∫ t in ε₀..x, deriv h.toFun t = h.toFun x := by
        rw [h_eq, h_at_ε₀] <;> simp
      -- 数学：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt
      -- |h(x)| ≤ (x-ε₀)²/2 · ‖h''‖_∞ ≤ (R₀-ε₀)² · B
      have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
        have h_deriv_left : ∀ y < ε₀, deriv h.toFun y = 0 := by
          intro y hy
          have h_ev : ∀ᶠ z in 𝓝 y, h.toFun z = 0 := by
            filter_upwards [Iio_mem_nhds hy] with z hz
            exact h_left z hz
          have h2 : ∀ᶠ z in 𝓝 y, deriv h.toFun z = deriv (fun _ => (0 : ℂ)) z :=
            Filter.EventuallyEq.deriv h_ev
          have h3 : deriv h.toFun y = deriv (fun _ => (0 : ℂ)) y :=
            h2.self_of_nhds
          rw [h3, deriv_const]
        have h_deriv_eps0 : deriv h.toFun ε₀ = 0 := by
          have h_ev2 : ∀ᶠ y in 𝓝[<] ε₀, deriv h.toFun y = 0 := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            exact h_deriv_left y hy
          have h_lim : Tendsto (deriv h.toFun) (𝓝[<] ε₀) (𝓝 0) := by
            exact?
          have h_cont_at : ContinuousAt (deriv h.toFun) ε₀ :=
            (ContDiff.continuous_deriv h.contDiff2 (by norm_num)).continuousAt
          have h_lim2 : Tendsto (deriv h.toFun) (𝓝[<] ε₀) (𝓝 (deriv h.toFun ε₀)) :=
            h_cont_at.tendsto.mono_left nhdsWithin_le_nhds
          exact tendsto_nhds_unique h_lim2 h_lim
        have h1 : ContDiff ℝ 1 (deriv h.toFun) := ContDiff.deriv' h.contDiff2
        have h_cont_deriv : Continuous (deriv h.toFun) := ContDiff.continuous h1
        have h_deriv2_cont : Continuous (deriv (deriv h.toFun)) :=
          ContDiff.continuous_deriv h1 (by norm_num)
        have h_ftc2 : ∀ t ∈ Set.Icc ε₀ x,
            ∫ u in ε₀..t, deriv (deriv h.toFun) u = deriv h.toFun t - deriv h.toFun ε₀ := by
          intro t _ht
          apply intervalIntegral.integral_deriv_eq_sub
          · intro y _hy
            have h_diff1 : Differentiable ℝ (deriv h.toFun) :=
              ContDiff.differentiable h1 (by norm_num)
            exact h_diff1 y
          · exact h_deriv2_cont.intervalIntegrable ε₀ t
        have h_deriv_eq : ∀ t ∈ Set.Icc ε₀ x,
            deriv h.toFun t = ∫ u in ε₀..t, deriv (deriv h.toFun) u := by
          intro t ht
          have h := h_ftc2 t ht
          rw [h, h_deriv_eps0] <;> ring
        have h_le1 : ∀ t ∈ Set.Icc ε₀ x, ‖deriv h.toFun t‖ ≤ B * (R₀ - ε₀) := by
          intro t ht
          have hle : ε₀ ≤ t := ht.1
          have h_abs : ‖∫ u in ε₀..t, deriv (deriv h.toFun) u‖ ≤
              ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle
          have hfi : IntervalIntegrable (fun u => ‖deriv (deriv h.toFun) u‖) volume ε₀ t :=
            h_deriv2_cont.norm.intervalIntegrable ε₀ t
          have hgi : IntervalIntegrable (fun _ => B) volume ε₀ t :=
            continuous_const.intervalIntegrable ε₀ t
          have h_le : ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ ≤ ∫ u in ε₀..t, B := by
            exact?
          have h_int : ∫ u in ε₀..t, B = B * (t - ε₀) := by
            rw [intervalIntegral.integral_const] <;> ring
          have h_t_le_R : t - ε₀ ≤ R₀ - ε₀ := by
            have ht1 : t ≤ x := ht.2
            linarith [h_x_le_R₀, ht1]
          calc
            ‖deriv h.toFun t‖
              = ‖∫ u in ε₀..t, deriv (deriv h.toFun) u‖ := by rw [h_deriv_eq t ht]
            _ ≤ ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ := h_abs
            _ ≤ ∫ u in ε₀..t, B := h_le
            _ = B * (t - ε₀) := h_int
            _ ≤ B * (R₀ - ε₀) := by gcongr
        have hle_x : ε₀ ≤ x := by linarith
        have h_final : ‖h.toFun x‖ ≤ ∫ t in ε₀..x, ‖deriv h.toFun t‖ := by
          have h_abs : ‖∫ t in ε₀..x, deriv h.toFun t‖ ≤
              ∫ t in ε₀..x, ‖deriv h.toFun t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle_x
          rw [← h_eq2]
          exact h_abs
        have hfi2 : IntervalIntegrable (fun t => ‖deriv h.toFun t‖) volume ε₀ x :=
          h_cont_deriv.norm.intervalIntegrable ε₀ x
        have hgi2 : IntervalIntegrable (fun _ => B * (R₀ - ε₀)) volume ε₀ x :=
          continuous_const.intervalIntegrable ε₀ x
        have h_bound2 : ∫ t in ε₀..x, ‖deriv h.toFun t‖ ≤
            ∫ t in ε₀..x, B * (R₀ - ε₀) := by exact?
        have h_int2 : ∫ t in ε₀..x, B * (R₀ - ε₀) = B * (R₀ - ε₀) * (x - ε₀) := by
          rw [intervalIntegral.integral_const] <;> ring
        have h_last : B * (R₀ - ε₀) * (x - ε₀) ≤ B * (R₀ - ε₀)^2 := by
          have h1 : x - ε₀ ≤ R₀ - ε₀ := by linarith
          have h_pos : 0 ≤ B * (R₀ - ε₀) := by positivity
          have h4 : B * (R₀ - ε₀) * (x - ε₀) ≤ B * (R₀ - ε₀) * (R₀ - ε₀) :=
            mul_le_mul_of_nonneg_left h1 h_pos
          have h5 : B * (R₀ - ε₀) * (R₀ - ε₀) = B * (R₀ - ε₀)^2 := by ring
          exact h4.trans (le_of_eq h5)
        have h_last' : B * (R₀ - ε₀) * (x - ε₀) ≤ (R₀ - ε₀)^2 * B := by
          calc B * (R₀ - ε₀) * (x - ε₀)
            ≤ B * (R₀ - ε₀)^2 := h_last
          _ = (R₀ - ε₀)^2 * B := by ring
        exact le_trans (le_trans (le_trans h_final h_bound2) (le_of_eq h_int2)) h_last'
      exact h_main
