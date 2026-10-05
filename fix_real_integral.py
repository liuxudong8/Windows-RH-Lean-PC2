with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = """/-- 实数积分的线性性（公理）。 -/
axiom realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2"""

new = """/-- 实数积分的线性性（定理，由 Bochner 积分线性性推出，需可积性条件）。 -/
theorem realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ)
    (h1_int : MeasureTheory.Integrable h1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h2_int : MeasureTheory.Integrable h2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2 := by
  let g1 : ℝ → ℂ := fun t => c1 * h1 t
  let g2 : ℝ → ℂ := fun t => c2 * h2 t
  have hg1_int : MeasureTheory.Integrable g1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [g1] using h1_int.const_mul c1
  have hg2_int : MeasureTheory.Integrable g2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [g2] using h2_int.const_mul c2
  have h_sum : (fun t : ℝ => c1 * h1 t + c2 * h2 t) = g1 + g2 := by
    funext t; simp [g1, g2] <;> ring
  have h_eq1 : realIntegral (fun t => c1 * h1 t + c2 * h2 t) =
      ∫ t, (g1 + g2) t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [h_sum] <;> rfl
  have h_eq2 : realIntegral h1 = ∫ t, h1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by rfl
  have h_eq3 : realIntegral h2 = ∫ t, h2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by rfl
  rw [h_eq1, h_eq2, h_eq3]
  have h4 : ∫ t, (g1 + g2) t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) =
      (∫ t, g1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) + (∫ t, g2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :=
    MeasureTheory.integral_add hg1_int hg2_int
  rw [h4]
  have h5 : ∫ t, g1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) = c1 * (∫ t, h1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h51 : g1 = fun t => c1 * h1 t := by rfl
    rw [h51]
    exact?
  have h6 : ∫ t, g2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) = c2 * (∫ t, h2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h61 : g2 = fun t => c2 * h2 t := by rfl
    rw [h61]
    exact?
  rw [h5, h6] <;> ring"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
