import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 测试 setIntegral 的线性性 -/
theorem test_set_integral_const_mul (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (M : ℝ) (f : ℝ → ℝ),
    MeasureTheory.IntegrableOn f (Set.Icc ε₀ R₀) →
    ∫ x in Set.Icc ε₀ R₀, M * f x = M * ∫ x in Set.Icc ε₀ R₀, f x := by
  intro M f h_int
  exact?
