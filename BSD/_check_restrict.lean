import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
#check MeasureTheory.Measure.restrict_restrict
#check MeasureTheory.Measure.restrict_restrict_of_subset
#check ContinuousOn.mono
#check ContinuousOn.aestronglyMeasurable
#check zero_lt_one
#check one_div_le_one_div
example (x : ℝ) (hx : 1 < x) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
      (MeasureTheory.volume.restrict (Set.Icc x (x + 0.5))) := by
  have hx1 : 0 < x - 1 := by linarith
  have hsub : Set.Icc x (x + 0.5) ⊆ Set.Ioi (x - 1) := by
    intro t ht
    have htx : x ≤ t := (Set.mem_Icc.mp ht).1
    have hx1' : x - 1 < x := by linarith
    exact lt_of_lt_of_le hx1' htx
  have hae := (cont_div (x - 1) hx1).aestronglyMeasurable measurableSet_Ioi
  have hae' : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
      (MeasureTheory.volume.restrict (Set.Icc x (x + 0.5))) := by
    simpa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] using
      (MeasureTheory.AEStronglyMeasurable.restrict hae)
  exact hae'
