import OrderPreservingBijection.test_rpow_ineq
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

open Set Real

/-- 一般版本的 rpow 不等式：
    (b^σ - a^σ) / σ ≤ max (log (b/a)) (b - a)
    其中 0 < a < b，0 < σ ≤ 1
-/
theorem test_general_rpow_ineq (a b : ℝ) (ha_pos : 0 < a) (hab : a < b)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1) :
    (b^σ - a^σ) / σ ≤ max (Real.log (b / a)) (b - a) := by
  -- 令 X = b / a
  set X : ℝ := b / a with hX_def
  have hX_gt_one : 1 < X := by
    have h1 : 0 < a := ha_pos
    have h2 : a < b := hab
    have h3 : 1 < b / a := by
      apply (one_lt_div (by linarith)).mpr
      linarith
    exact h3
  have hX_pos : 0 < X := by linarith

  -- 我们有 test_rpow_ineq:
  -- (X^σ - 1) / σ ≤ max (log X) (X - 1)
  have h_test : (X^σ - 1) / σ ≤ max (Real.log X) (X - 1) :=
    test_rpow_ineq X hX_gt_one σ hσ_pos hσ_lt_one

  -- 我们需要直接证明：
  -- (b^σ - a^σ) / σ ≤ max (log (b/a)) (b - a)
  -- 用凸性！

  -- 令 C = max (log (b/a)) (b - a)
  set C : ℝ := max (Real.log (b / a)) (b - a) with hC_def

  -- 令 g(σ) = b^σ - a^σ - σ * C
  -- 我们需要证明 g(σ) ≤ 0
  have h_b_exp_eq : (fun σ : ℝ => Real.exp (σ * Real.log b)) = (fun σ : ℝ => b^σ) := by
    funext σ
    have h_pos_b : 0 < b := by linarith [hab]
    have h_comm : σ * Real.log b = Real.log b * σ := by ring
    have h1 : Real.exp (σ * Real.log b) = (Real.exp (Real.log b)) ^ σ := by
      rw [h_comm]
      rw [Real.exp_mul]
    have h2 : Real.exp (Real.log b) = b := Real.exp_log h_pos_b
    rw [h1, h2]
  have h_b_exp_convex : ConvexOn ℝ Set.univ (fun σ : ℝ => b^σ) := by
    have h1 : ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (σ * Real.log b)) :=
      test_exp_linear_convex (Real.log b)
    have h2 : (fun σ : ℝ => Real.exp (σ * Real.log b)) = (fun σ : ℝ => b^σ) := h_b_exp_eq
    rw [h2] at h1
    exact h1
  have h_a_exp_eq : (fun σ : ℝ => Real.exp (σ * Real.log a)) = (fun σ : ℝ => a^σ) := by
    funext σ
    have h_pos_a : 0 < a := ha_pos
    have h_comm : σ * Real.log a = Real.log a * σ := by ring
    have h1 : Real.exp (σ * Real.log a) = (Real.exp (Real.log a)) ^ σ := by
      rw [h_comm]
      rw [Real.exp_mul]
    have h2 : Real.exp (Real.log a) = a := Real.exp_log h_pos_a
    rw [h1, h2]
  have h_a_exp_convex : ConvexOn ℝ Set.univ (fun σ : ℝ => a^σ) := by
    have h1 : ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (σ * Real.log a)) :=
      test_exp_linear_convex (Real.log a)
    have h2 : (fun σ : ℝ => Real.exp (σ * Real.log a)) = (fun σ : ℝ => a^σ) := h_a_exp_eq
    rw [h2] at h1
    exact h1
  have h_linear_convex : ConvexOn ℝ Set.univ (fun σ : ℝ => σ * C) :=
    test_linear_convex C
  have h_g_convex_univ : ConvexOn ℝ Set.univ (fun σ : ℝ => b^σ - a^σ - σ * C) := by
    sorry
  have h_convex_Icc : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h_subset : (Set.Icc (0:ℝ) 1) ⊆ Set.univ := by
    exact Set.subset_univ (Set.Icc (0:ℝ) 1)
  have h_g_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun σ : ℝ => b^σ - a^σ - σ * C) :=
    h_g_convex_univ.subset h_subset h_convex_Icc
  have h_g0 : (fun σ : ℝ => b^σ - a^σ - σ * C) 0 = 0 := by
    simp [Real.rpow_zero] <;> ring
  have h_g1 : (fun σ : ℝ => b^σ - a^σ - σ * C) 1 ≤ 0 := by
    simp [Real.rpow_one, hC_def] <;> exact le_max_right _ _
  have h8 : ∀ σ ∈ Set.Icc (0 : ℝ) 1, b^σ - a^σ - σ * C ≤ 0 := by
    intro σ hσ
    have h_a_nonneg : 0 ≤ 1 - σ := by exact sub_nonneg.mpr hσ.2
    have h_b_nonneg : 0 ≤ σ := by exact hσ.1
    have h_sum_one : (1 - σ) + σ = 1 := by ring
    have h0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
    have h1_in : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
    have h_main : (fun σ : ℝ => b^σ - a^σ - σ * C) σ ≤
        (1 - σ) * ((fun σ : ℝ => b^σ - a^σ - σ * C) 0) +
        σ * ((fun σ : ℝ => b^σ - a^σ - σ * C) 1) := by
      have h_eq : σ = (1 - σ) • (0 : ℝ) + σ • (1 : ℝ) := by simp [smul_eq_mul] <;> ring
      rw [h_eq]
      have h := h_g_convex.2 h0_in h1_in h_a_nonneg h_b_nonneg h_sum_one
      simpa [smul_eq_mul] using h
    have h9 : (1 - σ) * ((fun σ : ℝ => b^σ - a^σ - σ * C) 0) + σ * ((fun σ : ℝ => b^σ - a^σ - σ * C) 1) ≤ 0 := by
      have h10 : (fun σ : ℝ => b^σ - a^σ - σ * C) 0 = 0 := h_g0
      rw [h10]
      have h11 : (fun σ : ℝ => b^σ - a^σ - σ * C) 1 ≤ 0 := h_g1
      nlinarith
    exact le_trans h_main h9
  have hs_re_Icc : σ ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by linarith [hσ_pos], by linarith [hσ_lt_one]⟩
  have h_goal : b^σ - a^σ - σ * C ≤ 0 := h8 σ hs_re_Icc
  have h_main : (b^σ - a^σ) / σ ≤ C := by
    have h : b^σ - a^σ ≤ σ * C := by linarith
    have h2 : 0 < σ := hσ_pos
    have h3 : (b^σ - a^σ) / σ ≤ (σ * C) / σ := by gcongr
    have h4 : (σ * C) / σ = C := by
      field_simp [h2.ne'] <;> ring
    rw [h4] at h3
    exact h3

  simpa [hC_def] using h_main
