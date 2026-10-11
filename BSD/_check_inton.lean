import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum

#check integrableOn_exp_neg_Ioi
#check MeasureTheory.IntegrableOn.mono
#check MeasureTheory.IntegrableOn.mono'
#check MeasureTheory.IntegrableOn.const_mul
#check MeasureTheory.integrableOn_const
#check MeasureTheory.IntegrableOn.restrict
#check ae_restrict_mem
#check measurableSet_Icc
#check measurableSet_Ioi
#check Filter.Eventually.and
#check MeasureTheory.aestronglyMeasurable
#check MeasureTheory.Integrable.mono'
#check integral_mono_ae
#check MeasureTheory.IntegrableOn.congr
#check Set.Icc_subset_Ioi
#check Set.Ioi_subset_Ioi
#check MeasureTheory.IntegrableOn.mono_set

example (x : ℝ) (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Icc x (x + 0.5)) := by
  -- Icc ⊆ Ioi 0.5（0.5 < x）——用 integrableOn_exp_neg_Ioi 0.5 的 mono
  apply MeasureTheory.IntegrableOn.mono (integrableOn_exp_neg_Ioi (0.5 : ℝ))
  · intro t ht
    have htx : x ≤ t := (Set.mem_Icc.mp ht).1
    exact lt_of_lt_of_le (by norm_num : (0.5 : ℝ) < x) htx
