/-
  Completed Riemann zeta function xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s).

  Bridges our project to mathlib's completedRiemannZeta.
  - xi_one_sub: xi(1-s) = xi(s) (functional equation, from mathlib)
  - xi_eq_zero_iff_zeta_eq_zero: in the critical strip, xi zeros = zeta zeros

  IMPORTANT: xi is defined as (1/2) s(s-1) completedRiemannZeta₀ s + 1/2, NOT as
  (1/2) s(s-1) completedRiemannZeta s.  The un-tilded completedRiemannZeta has
  arbitrary total-division values at s = 0 and s = 1, so the naive product is
  discontinuous there; completedRiemannZeta₀ = completedRiemannZeta + 1/s + 1/(1-s)
  removes the poles and the + 1/2 term repairs the value.  Away from {0,1} the two
  definitions agree, and in the critical strip xi zeros coincide with zeta zeros.

  Future steps:
  - Growth estimate |xi(1/2+it)| = O(e^{-pi|t|/4} |t|^A) via Stirling
  - If xi has finitely many zeros, factor as e^{a+bs} P(s)
  - Functional equation forces b=0, contradicting exponential decay
-/

import OrderPreservingBijection.BasicInfrastructure
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

namespace OrderPreservingBijection

open Complex

/-- xi(s) = (1/2) s(s-1) completedRiemannZeta₀(s) + 1/2, entire with zeros exactly
    the nontrivial zeta zeros. -/
noncomputable def xi (s : ℂ) : ℂ :=
    (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2

/-- xi is entire: polynomial times the entire Λ₀ plus a constant. -/
theorem differentiable_xi : Differentiable ℂ xi := by
  change Differentiable ℂ
    (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2)
  apply Differentiable.add
  · have hpoly : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by
      fun_prop
    exact hpoly.mul differentiable_completedZeta₀
  · fun_prop

/-- Functional equation: xi(1-s) = xi(s). -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  have h2 : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
    completedRiemannZeta₀_one_sub s
  simp only [xi]
  rw [h2]
  ring

/-- In the critical strip (0 < Re < 1), Gamma_R(s) != 0. -/
theorem gammaR_nonzero_in_strip {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 1) :
    Gammaℝ s ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos h1

/-- In the critical strip, xi(s)=0 iff zeta(s)=0. -/
theorem xi_eq_zero_iff_zeta_eq_zero {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 1) :
    xi s = 0 ↔ _root_.riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h1
  -- ζ(s) = Λ(s) / Γℝ(s)  for s ≠ 0
  have hζ : _root_.riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  -- in the strip, xi(s) = (1/2) s(s-1) Λ(s) = (1/2) s(s-1) Γℝ(s) ζ(s)
  have hxi_Λ : xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
    simp only [xi, completedRiemannZeta_eq]
    field_simp [hs0, hs1]
    ring
  have hxi : xi s = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * _root_.riemannZeta s := by
    rw [hxi_Λ, hζ]
    field_simp [hΓ]
  rw [hxi]
  have hpre : (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s ≠ 0 := by
    have hpoly : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact hs0
      · exact sub_ne_zero.mpr hs1
    exact mul_ne_zero hpoly hΓ
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hleft | hz
    · exfalso
      exact hpre hleft
    · exact hz
  · intro hz
    exact mul_eq_zero.mpr (Or.inr hz)

end OrderPreservingBijection
