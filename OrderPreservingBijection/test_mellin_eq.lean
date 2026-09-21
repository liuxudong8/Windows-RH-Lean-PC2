import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure

open OrderPreservingBijection

noncomputable section

/-- 证明我们的 melinTransform 和 mathlib 的标准 Mellin 变换是一样的 -/
theorem melinTransform_eq_mathlib_mellin (f : TestFunction) (s : ℂ) :
    melinTransform f s =
    ∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * f.eval t := by
  -- 我们的 melinTransform 定义是：
  -- realIntegral (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)
  -- 而 realIntegral h = ∫ t in Set.Ioi (0 : ℝ), h t
  have h1 : melinTransform f s =
      ∫ t in Set.Ioi (0 : ℝ), (if 0 < t then f.eval t * Complex.exp ((s - 1) * (Real.log t : ℂ)) else 0) := by
    rfl
  rw [h1]
  -- 现在我们需要证明：
  -- ∫ t in Set.Ioi (0 : ℝ), (if 0 < t then f.eval t * Complex.exp ((s - 1) * (Real.log t : ℂ)) else 0) =
  -- ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * f.eval t
  -- 我们只需要证明被积函数在 Set.Ioi (0 : ℝ) 上相等
  let g1 : ℝ → ℂ := fun t => (if 0 < t then f.eval t * Complex.exp ((s - 1) * (Real.log t : ℂ)) else 0)
  let g2 : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * f.eval t
  have h_eq : ∀ t ∈ Set.Ioi (0 : ℝ), g1 t = g2 t := by
    intro t ht
    have h_pos : 0 < t := ht
    have h_ne_zero : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h_pos
    have h_if : g1 t = f.eval t * Complex.exp ((s - 1) * (Real.log t : ℂ)) := by
      simp [g1, ite_eq_left h_pos]
    rw [h_if]
    -- 现在我们需要证明：
    -- f.eval t * Complex.exp ((s - 1) * (Real.log t : ℂ)) = g2 t
    have h_log : Complex.log (t : ℂ) = (Real.log t : ℂ) := by
      rw [Complex.ofReal_log] <;> linarith
    have h2 : (t : ℂ) ^ (s - 1) = Complex.exp (Complex.log (t : ℂ) * (s - 1)) := by
      rw [Complex.cpow_def]
      rw [ite_eq_right h_ne_zero]
      <;> ring
    have h3 : Complex.log (t : ℂ) * (s - 1) = (s - 1) * (Real.log t : ℂ) := by
      rw [h_log] <;> ring
    have h4 : Complex.exp (Complex.log (t : ℂ) * (s - 1)) = Complex.exp ((s - 1) * (Real.log t : ℂ)) := by
      rw [h3]
    have h5 : g2 t = (t : ℂ) ^ (s - 1) * f.eval t := by rfl
    rw [h5, h2, h4] <;> ring
  -- 现在我们有了 h_eq：在 Set.Ioi (0 : ℝ) 上，g1 t = g2 t！
  -- 所以 g1 和 g2 在 volume.restrict (Set.Ioi (0 : ℝ)) 上几乎处处相等！
  have h_ae : g1 =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] g2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact h_eq t ht
  -- 所以积分相等！
  exact MeasureTheory.integral_congr_ae h_ae
