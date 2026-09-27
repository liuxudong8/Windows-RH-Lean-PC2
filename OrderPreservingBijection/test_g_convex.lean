import OrderPreservingBijection.test_rpow_ineq
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set Real intervalIntegral

/-- 积分表示：(b^σ - a^σ) / σ = ∫_a^b x^(σ-1) dx -/
lemma integral_repr (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) (σ : ℝ) (hσ_pos : 0 < σ) :
    (b^σ - a^σ) / σ = ∫ x in a..b, x ^ (σ - 1) := by
  have h2 : -1 < (σ - 1 : ℝ) := by linarith
  have h_main : ∫ x in a..b, x ^ (σ - 1) = (b ^ ((σ - 1) + 1) - a ^ ((σ - 1) + 1)) / ((σ - 1) + 1) :=
    integral_rpow (Or.inl h2)
  have h3 : (σ - 1) + 1 = σ := by ring
  have h4 : (b ^ ((σ - 1) + 1) - a ^ ((σ - 1) + 1)) / ((σ - 1) + 1) = (b^σ - a^σ) / σ := by
    rw [h3]
  exact h4.symm.trans h_main.symm

/-- 加权 AM-GM 不等式：u^t * v^(1-t) ≤ t*u + (1-t)*v -/
lemma amgm (u v : ℝ) (hu_pos : 0 < u) (hv_pos : 0 < v) (t : ℝ) (ht1 : 0 ≤ t) (ht2 : t ≤ 1) :
    u ^ t * v ^ (1 - t) ≤ t * u + (1 - t) * v := by
  sorry

/-- 主定理：f(σ) = (b^σ - a^σ)/σ 在 (0,∞) 上是凸的 -/
theorem f_convex (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun σ : ℝ => (b^σ - a^σ) / σ) := by
  let f : ℝ → ℝ := fun σ : ℝ => (b^σ - a^σ) / σ
  have h_repr : ∀ σ ∈ Ioi (0 : ℝ), f σ = ∫ x in a..b, x ^ (σ - 1) := by
    intro σ hσ
    exact integral_repr a b ha_pos hab σ hσ
  sorry
