import OrderPreservingBijection.stage_4
import OrderPreservingBijection.Interpolation
import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

namespace RHSpectralDuality

-- 测试 1: finite_sum_single_point_change
theorem test_finite_sum_single_point_change (s : Finset ℝ) (l0 : ℝ) (hl0 : l0 ∈ s)
    (f f0 : ℝ → ℂ) (h : ∀ x ∈ s, x ≠ l0 → f x = f0 x) :
    ∑ x ∈ s, f x = (∑ x ∈ s, f0 x) + (f l0 - f0 l0) := by
  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s, (f0 x + if x = l0 then (f l0 - f0 l0) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hx2 : x = l0
    · rw [hx2] <;> simp
    · have h2 : f x = f0 x := h x hx hx2
      rw [h2, if_neg hx2] <;> ring
  rw [h1]
  have h2 : ∑ x ∈ s, (f0 x + if x = l0 then (f l0 - f0 l0) else 0) =
      (∑ x ∈ s, f0 x) + ∑ x ∈ s, (if x = l0 then (f l0 - f0 l0) else 0) := by
    rw [Finset.sum_add_distrib]
  rw [h2]
  have h3 : ∑ x ∈ s, (if x = l0 then (f l0 - f0 l0) else 0) = f l0 - f0 l0 := by
    rw [Finset.sum_ite_eq'] <;> simp [hl0]
  rw [h3] <;> ring

-- 测试 2: realIntegral_linear
theorem test_realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2 := by
  simp only [realIntegral]
  rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] <;> ring

end RHSpectralDuality
