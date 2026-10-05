from pathlib import Path

p = Path(r"c:\proj2\OrderPreservingBijection\Interpolation.lean")
t = p.read_text(encoding="utf-8")

# Find the lemma and replace from "lemma intervalIndicator" to the next blank line
import re
start = t.index("lemma intervalIndicator_mellinTransform")
end = t.index("/-- exp(z) = 1")

new = """lemma intervalIndicator_mellinTransform (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator a b ha hab) s =
    (Complex.exp (s * (Real.log b : ℂ)) - Complex.exp (s * (Real.log a : ℂ))) / s := by
  have h1 : Set.Icc a b ⊆ Set.Ioi (0:ℝ) := by
    intro x hx; linarith [hx.1]
  have h_deriv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ => Complex.exp (s * (Real.log y : ℂ)) / s)
        (Complex.exp ((s - 1) * (Real.log x : ℂ))) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hlog : HasDerivAt Real.log x⁻¹ x := by exact?
    have hexp : HasDerivAt (fun y => Complex.exp (s * (Real.log y : ℂ)))
        (s * (x⁻¹ : ℂ) * Complex.exp (s * (Real.log x : ℂ))) x := by
      exact (hlog.const_mul s).exp
    have hdiv := hexp.div_const s
    have h_eq : (s * (x⁻¹ : ℂ) * Complex.exp (s * (Real.log x : ℂ))) / s =
        Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      field_simp [hs, hx0.ne]
      rw [Complex.exp_sub, Complex.exp_one]
      field_simp [hx0.ne] <;> ring
    rw [h_eq] at hdiv; exact hdiv
  have h_cont : ContinuousOn (fun x : ℝ => Complex.exp ((s - 1) * (Real.log x : ℂ))) (Set.Icc a b) := by
    fun_prop
  have h_fb : ∫ x in Set.Icc a b, Complex.exp ((s - 1) * (Real.log x : ℂ)) =
      Complex.exp (s * (Real.log b : ℂ)) / s - Complex.exp (s * (Real.log a : ℂ)) / s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont
    simpa [MeasureTheory.integral_Icc_eq_intervalIntegral] using h
  have h_main : realIntegral (fun x : ℝ => (if a ≤ x ∧ x ≤ b then (1:ℂ) else 0) * Complex.exp ((s - 1) * (Real.log x : ℂ))) =
      ∫ x in Set.Icc a b, Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
    simp only [realIntegral, MeasureTheory.integral_indicator, Set.indicator]
    rw [MeasureTheory.setIntegral_restrict_eq_of_subset h1]
    <;> rfl
  simpa [melinTransform, intervalIndicator] by
    rw [h_main, h_fb] <;> ring

"""

t = t[:start] + new + t[end:]
p.write_text(t, encoding="utf-8")
print("done")
