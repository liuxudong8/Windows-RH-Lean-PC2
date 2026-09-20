import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 原函数 F(x) = x^s / s = exp(s * log x) / s。 -/
noncomputable def mellinPrimitive (s : ℂ) (x : ℝ) : ℂ :=
    Complex.exp (s * (Real.log x : ℂ)) / s

/-- 原函数的导数：F'(x) = x^{s-1} = exp((s-1) * log x)。 -/
theorem mellinPrimitive_hasDeriv (s : ℂ) (hs : s ≠ 0) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (mellinPrimitive s) (Complex.exp ((s - 1) * (Real.log x : ℂ))) x := by
  let f' : ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (1 / x)
  have h_log_real : HasDerivAt Real.log f' x := by
    simpa [f', ContinuousLinearMap.smulRight] using Real.hasDerivAt_log hx
  have h_ofReal : HasDerivAt (fun z : ℝ => (z : ℂ)) Complex.ofRealCLM (Real.log x) :=
    Complex.ofRealCLM.hasDerivAt
  have h_log_complex : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) (Complex.ofRealCLM.comp f') x :=
    h_ofReal.comp x h_log_real
  have h_log_complex' : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((1 : ℂ) / (x : ℂ)) x := by
    convert h_log_complex using 1
    <;> simp [Complex.ofRealCLM, ContinuousLinearMap.smulRight] <;> ring
  have h_smul : HasDerivAt (fun y : ℝ => s * (Real.log y : ℂ)) (s * ((1 : ℂ) / (x : ℂ))) x := by
    convert h_log_complex'.const_mul s using 1 <;> ring
  have h_exp : HasDerivAt (fun y : ℝ => Complex.exp (s * (Real.log y : ℂ)))
      (Complex.exp (s * (Real.log x : ℂ)) * (s * ((1 : ℂ) / (x : ℂ)))) x :=
    h_smul.exp
  have h_div : HasDerivAt (fun y : ℝ => Complex.exp (s * (Real.log y : ℂ)) / s)
      ((Complex.exp (s * (Real.log x : ℂ)) * (s * ((1 : ℂ) / (x : ℂ)))) / s) x :=
    h_exp.div_const s
  have h_simp : (Complex.exp (s * (Real.log x : ℂ)) * (s * ((1 : ℂ) / (x : ℂ)))) / s =
      Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    field_simp [hs, hx'] <;> ring_nf
    <;> simp [Complex.ext_iff] <;> ring
  rw [h_simp] at h_div
  exact h_div

end RHSpectralDuality
end OrderPreservingBijection
