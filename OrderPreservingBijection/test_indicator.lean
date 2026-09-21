import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 测试 Set.indicator 的用法 -/
theorem test_indicator (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (f1 f2 : ℝ → ℝ),
    (∀ x ∈ Set.Icc ε₀ R₀, f1 x ≤ f2 x) →
    MeasureTheory.IntegrableOn f1 (Set.Icc ε₀ R₀) →
    MeasureTheory.IntegrableOn f2 (Set.Icc ε₀ R₀) →
    ∫ x in Set.Icc ε₀ R₀, f1 x ≤ ∫ x in Set.Icc ε₀ R₀, f2 x := by
  intro f1 f2 h_pointwise h_int1 h_int2
  let f1' : ℝ → ℝ := (Set.Icc ε₀ R₀).indicator f1
  let f2' : ℝ → ℝ := (Set.Icc ε₀ R₀).indicator f2
  have h_f1'_eq : ∀ x, x ∉ Set.Icc ε₀ R₀ → f1' x = 0 := by
    intro x hx
    simp [f1', Set.indicator, hx]
  have h_f2'_eq : ∀ x, x ∉ Set.Icc ε₀ R₀ → f2' x = 0 := by
    intro x hx
    simp [f2', Set.indicator, hx]
  have h_f1'_le_f2' : ∀ x, x ∈ Set.Icc ε₀ R₀ → f1' x ≤ f2' x := by
    intro x hx
    simp [f1', f2', Set.indicator, hx]
    exact h_pointwise x hx
  have h_int1' : MeasureTheory.Integrable f1' MeasureTheory.volume := by
    simpa [f1'] using h_int1.integrable_indicator measurableSet_Icc
  have h_int2' : MeasureTheory.Integrable f2' MeasureTheory.volume := by
    simpa [f2'] using h_int2.integrable_indicator measurableSet_Icc
  have h_integral1 :
      ∫ x in Set.Icc ε₀ R₀, f1 x = ∫ x, f1' x := by
    simpa [f1'] using
      (MeasureTheory.integral_indicator (μ := MeasureTheory.volume) (s := Set.Icc ε₀ R₀) (f := f1)
        measurableSet_Icc).symm
  have h_integral2 :
      ∫ x in Set.Icc ε₀ R₀, f2 x = ∫ x, f2' x := by
    simpa [f2'] using
      (MeasureTheory.integral_indicator (μ := MeasureTheory.volume) (s := Set.Icc ε₀ R₀) (f := f2)
        measurableSet_Icc).symm
  have h_f1'_le_f2'_global : ∀ x, f1' x ≤ f2' x := by
    intro x
    by_cases hx : x ∈ Set.Icc ε₀ R₀
    · exact h_f1'_le_f2' x hx
    · rw [h_f1'_eq x hx, h_f2'_eq x hx]
      <;> exact le_refl 0
  rw [h_integral1, h_integral2]
  exact MeasureTheory.integral_mono h_int1' h_int2' h_f1'_le_f2'_global
