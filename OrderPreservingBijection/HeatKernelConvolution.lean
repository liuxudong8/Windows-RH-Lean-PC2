/-
  HeatKernelConvolution.lean
  Attack heatKernel_convolution_formula: decompose into spherical coordinates +
  hyperbolic law of cosines + angular integral + radial integral.

  Layer structure:
    L1: spherical coordinate decomposition (measure theory)
    L2: hyperbolic law of cosines (geometry)
    L3: angular integral formula (analysis, antiderivative + FTC)
    L4: radial integral formula (analysis, Gaussian integral)
    L5: convolution formula theorem (combines L1-L4)
-/

import OrderPreservingBijection.HeatKernelSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Group.Action

open MeasureTheory

namespace OrderPreservingBijection

/-- Spherical coordinate point constructor (opaque, to be instantiated later). -/
opaque sphericalPoint (z w : ManifoldM) (r θ : ℝ) : ManifoldM

/-- sphericalPoint satisfies d(z, sphericalPoint z w r theta) = r (axiom). -/
axiom sphericalPoint_radius (z w : ManifoldM) (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    hyperbolicDistance z (sphericalPoint z w r θ) = r

/-- Spherical coordinates on H3 centered at z: volume element sinh^2(r) sin(theta). -/
axiom heatKernel_spherical_coords (z w : ManifoldM) (f : ManifoldM → ℂ) :
    manifoldIntegral f =
    (2 * Real.pi : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
      ∫ θ in Set.Icc (0 : ℝ) Real.pi,
        ((Real.sinh r)^2 * Real.sin θ : ℂ) * f (sphericalPoint z w r θ)

/-- Hyperbolic law of cosines (axiom):
    cosh(rho) = cosh(r)cosh(d) - sinh(r)sinh(d)cos(theta), rho = d(u,w). -/
axiom hyperbolic_law_of_cosines (z w : ManifoldM) (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    Real.cosh (hyperbolicDistance (sphericalPoint z w r θ) w) =
    Real.cosh r * Real.cosh (hyperbolicDistance z w) -
    Real.sinh r * Real.sinh (hyperbolicDistance z w) * Real.cos θ

/-- Auxiliary: derivative of rho(theta) = arcosh(A - B cos theta) is B sin(theta)/sinh(rho).
    Requires 1 < A - B cos theta (so arcosh is differentiable).
    Proof: Real.hasDerivAt_arcosh + chain rule + sqrt(cosh^2(x)-1)=sinh(x) for x>=0. -/
lemma rho_deriv (d r s : ℝ) (hd : 0 < d) (hr : 0 < r) (θ : ℝ)
    (h : 1 < Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ) :
    HasDerivAt (fun θ : ℝ => Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ))
      (Real.sinh r * Real.sinh d * Real.sin θ /
       Real.sinh (Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ))) θ := by
  set u : ℝ → ℝ := fun θ => Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ with hu
  set B : ℝ := Real.sinh r * Real.sinh d with hB
  have h_u_deriv : HasDerivAt u (B * Real.sin θ) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => B * Real.cos θ) (-(B * Real.sin θ)) θ := by
      have h1a : HasDerivAt (fun θ : ℝ => B * Real.cos θ) (B * -Real.sin θ) θ :=
        HasDerivAt.const_mul B (Real.hasDerivAt_cos θ)
      have h_eq : B * -Real.sin θ = -(B * Real.sin θ) := by ring
      rw [h_eq] at h1a
      exact h1a
    have h2 : HasDerivAt (fun θ : ℝ => Real.cosh r * Real.cosh d - B * Real.cos θ) (0 - (-(B * Real.sin θ))) θ :=
      HasDerivAt.sub (hasDerivAt_const θ (Real.cosh r * Real.cosh d)) h1
    have h3 : (0 - (-(B * Real.sin θ))) = B * Real.sin θ := by ring
    rw [h3] at h2
    simpa [hu, hB] using h2
  have h_u_gt_one : 1 < u θ := h
  have h_arcosh_deriv : HasDerivAt Real.arcosh (Real.sqrt ((u θ)^2 - 1))⁻¹ (u θ) :=
    Real.hasDerivAt_arcosh (show (u θ) ∈ Set.Ioi (1 : ℝ) from h_u_gt_one)
  have h_main : HasDerivAt (Real.arcosh ∘ u) ((Real.sqrt ((u θ)^2 - 1))⁻¹ * (B * Real.sin θ)) θ :=
    h_arcosh_deriv.comp θ h_u_deriv
  have h_sqrt_eq : Real.sqrt ((u θ)^2 - 1) = Real.sinh (Real.arcosh (u θ)) := by
    set x : ℝ := Real.arcosh (u θ) with hx
    have h1 : (u θ) = Real.cosh x := by
      rw [Real.cosh_arcosh] <;> linarith
    have h3 : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    have h2 : (u θ)^2 - 1 = (Real.sinh x)^2 := by
      calc
        (u θ)^2 - 1 = (Real.cosh x)^2 - 1 := by rw [h1]
        _ = (Real.sinh x)^2 := by linarith
    have h4 : 0 ≤ Real.sinh x := by
      have h5 : 0 ≤ x := Real.arcosh_nonneg (show (1 : ℝ) ≤ u θ from by linarith)
      exact Real.sinh_nonneg_iff.mpr h5
    rw [h2, Real.sqrt_sq_eq_abs, abs_of_nonneg h4]
  have h_final : (Real.sqrt ((u θ)^2 - 1))⁻¹ * (B * Real.sin θ) =
      B * Real.sin θ / Real.sinh (Real.arcosh (u θ)) := by
    rw [h_sqrt_eq] <;> field_simp <;> ring
  rw [h_final] at h_main
  have h_goal : HasDerivAt (fun θ : ℝ => Real.arcosh (u θ)) (B * Real.sin θ / Real.sinh (Real.arcosh (u θ))) θ := by
    convert h_main using 1 <;> funext y <;> rfl
  simpa [hu, hB] using h_goal

/-- Auxiliary: Set.Icc integral equals intervalIntegral for 0 <= pi.
    Math: intervalIntegral 0..π = integral over uIoc = Ico [0,π); Icc = Ico ∪ {π};
    {π} has Lebesgue measure zero, so integrals agree.
    Lean formalization deferred: intervalIntegral.intervalIntegral_eq_integral_uIoc +
    setIntegral_congr_set + ae equality of Icc/Ico (technical bookkeeping). -/
lemma integral_Icc_eq_interval (f : ℝ → ℝ) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi, f θ = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  have h_le : (0 : ℝ) ≤ Real.pi := by positivity
  have h1 : ∫ θ in (0 : ℝ)..Real.pi, f θ = ∫ θ in Set.Ioc (0 : ℝ) Real.pi, f θ := intervalIntegral.integral_of_le h_le
  have h2 : ∫ θ in Set.Icc (0 : ℝ) Real.pi, f θ = ∫ θ in Set.Ioc (0 : ℝ) Real.pi, f θ :=
    integral_Icc_eq_integral_Ioc' (show volume ({0} : Set ℝ) = 0 from by simp)
  rw [h2, h1]

/-- Auxiliary: rho(0) = |r-d|, rho(pi) = r+d.
    Proof: cosh_sub/cosh_add + arcosh_cosh (with case split for r-d sign). -/
lemma rho_endpoints (d r : ℝ) (hd : 0 < d) (hr : 0 < r) :
    Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d) = |r - d| ∧
    Real.arcosh (Real.cosh r * Real.cosh d + Real.sinh r * Real.sinh d) = r + d := by
  have h1 : Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d = Real.cosh (r - d) := by
    rw [Real.cosh_sub]
  have h2 : Real.cosh r * Real.cosh d + Real.sinh r * Real.sinh d = Real.cosh (r + d) := by
    rw [Real.cosh_add]
  have h_first : Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d) = |r - d| := by
    rw [h1]
    by_cases h : r ≥ d
    · -- r ≥ d, so r - d ≥ 0
      have h3 : 0 ≤ r - d := by linarith
      rw [Real.arcosh_cosh h3]
      rw [abs_of_nonneg h3]
    · -- r < d, so d - r > 0, use cosh(r-d) = cosh(d-r)
      have h4 : r < d := by linarith
      have h5 : 0 ≤ d - r := by linarith
      have h6 : Real.cosh (r - d) = Real.cosh (d - r) := by
        rw [show r - d = -(d - r) by ring, Real.cosh_neg]
      rw [h6, Real.arcosh_cosh h5]
      rw [abs_of_neg (by linarith)] <;> linarith
  have h_second : Real.arcosh (Real.cosh r * Real.cosh d + Real.sinh r * Real.sinh d) = r + d := by
    rw [h2]
    have h7 : 0 ≤ r + d := by linarith
    rw [Real.arcosh_cosh h7]
  exact ⟨h_first, h_second⟩

/-- Auxiliary: F(pi) - F(0) = 2s/B * (exp(-(r-d)^2/(4s)) - exp(-(r+d)^2/(4s))).
    Proof: cos(pi)=-1, cos(0)=1; rho_endpoints gives arcosh values; |r-d|^2=(r-d)^2. -/
lemma F_endpoints_diff (d r s : ℝ) (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (B : ℝ) (hB : B = Real.sinh r * Real.sinh d) :
    (-2 * s / B * Real.exp (-(Real.arcosh (Real.cosh r * Real.cosh d - B * Real.cos Real.pi))^2 / (4 * s))) -
    (-2 * s / B * Real.exp (-(Real.arcosh (Real.cosh r * Real.cosh d - B * Real.cos 0))^2 / (4 * s)))
    = (2 * s / B) * (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s))) := by
  have h_ep := rho_endpoints d r hd hr
  have h_cos_pi : B * Real.cos Real.pi = -B := by
    rw [Real.cos_pi] <;> ring
  have h_cos0 : B * Real.cos 0 = B := by
    rw [Real.cos_zero] <;> ring
  have h_arg_pi : Real.cosh r * Real.cosh d - B * Real.cos Real.pi = Real.cosh r * Real.cosh d + B := by
    rw [h_cos_pi] <;> ring
  have h_arg0 : Real.cosh r * Real.cosh d - B * Real.cos 0 = Real.cosh r * Real.cosh d - B := by
    rw [h_cos0] <;> ring
  have h_arcosh_pi : Real.arcosh (Real.cosh r * Real.cosh d - B * Real.cos Real.pi) = r + d := by
    rw [h_arg_pi]
    have h : Real.arcosh (Real.cosh r * Real.cosh d + B) = r + d := by
      rw [hB] <;> exact h_ep.2
    exact h
  have h_arcosh0 : Real.arcosh (Real.cosh r * Real.cosh d - B * Real.cos 0) = |r - d| := by
    rw [h_arg0]
    have h : Real.arcosh (Real.cosh r * Real.cosh d - B) = |r - d| := by
      rw [hB] <;> exact h_ep.1
    exact h
  rw [h_arcosh_pi, h_arcosh0]
  have h_abs_sq : (|r - d|)^2 = (r - d)^2 := by rw [sq_abs]
  rw [h_abs_sq]
  <;> field_simp <;> ring

/-- Angular integral lemma (theorem, via antiderivative F(theta) = -2s/B exp(-rho^2/(4s))).
    F'(theta) = integrand by rho_deriv. FTC gives integral = F(pi)-F(0).
    Endpoints by F_endpoints_diff. Structure complete; rho_deriv/FTC/endpoints are sorry. -/
theorem heatKernel_angular_integral (d r s : ℝ) (hd : 0 < d) (hr : 0 < r) (hs : 0 < s) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi,
      Real.exp (-(Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ))^2 / (4 * s)) *
      (Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ) /
       Real.sinh (Real.arcosh (Real.cosh r * Real.cosh d - Real.sinh r * Real.sinh d * Real.cos θ))) *
      Real.sin θ
    = (2 * s / (Real.sinh r * Real.sinh d)) *
      (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s))) := by
  set B : ℝ := Real.sinh r * Real.sinh d with hB
  set rho : ℝ → ℝ := fun θ => Real.arcosh (Real.cosh r * Real.cosh d - B * Real.cos θ) with hrho
  set F : ℝ → ℝ := fun θ => -2 * s / B * Real.exp (-(rho θ)^2 / (4 * s)) with hF
  have hB_pos : 0 < B := by
    have h1 : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
    have h2 : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd
    positivity
  have hB_ne : B ≠ 0 := hB_pos.ne'
  have hs_ne : (4 * s : ℝ) ≠ 0 := by positivity
  have h_le : (0 : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  -- g(theta) = cosh r cosh d - B cos theta >= 1 on [0, pi]
  have h_g_ge_one : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi, 1 ≤ Real.cosh r * Real.cosh d - B * Real.cos θ := by
    intro θ hθ
    have h_cos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hB_nonneg : 0 ≤ B := by positivity
    have h : Real.cosh r * Real.cosh d - B * Real.cos θ ≥ Real.cosh r * Real.cosh d - B := by nlinarith
    have h2 : Real.cosh r * Real.cosh d - B = Real.cosh (r - d) := by
      rw [Real.cosh_sub] <;> ring
    rw [h2] at h
    have h3 : 1 ≤ Real.cosh (r - d) := Real.one_le_cosh (r - d)
    linarith
  -- g(theta) > 1 on (0, pi)
  have h_g_gt_one : ∀ θ ∈ Set.uIoo (0 : ℝ) Real.pi, 1 < Real.cosh r * Real.cosh d - B * Real.cos θ := by
    intro θ hθ
    have hθ_pos : 0 < θ := by
      have h : min (0 : ℝ) Real.pi < θ := hθ.1
      have h0 : min (0 : ℝ) Real.pi = 0 := by rw [min_eq_left] <;> linarith [Real.pi_pos]
      rw [h0] at h; exact h
    have hθ_lt : θ < Real.pi := by
      have h : θ < max (0 : ℝ) Real.pi := hθ.2
      have h0 : max (0 : ℝ) Real.pi = Real.pi := by rw [max_eq_right] <;> linarith [Real.pi_pos]
      rw [h0] at h; exact h
    have hθ_le : θ ≤ Real.pi := le_of_lt hθ_lt
    have h_cos_lt_one : Real.cos θ < 1 := by
      have h : Real.cos θ < Real.cos 0 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθ_le hθ_pos
      simpa using h
    have h : Real.cosh r * Real.cosh d - B * Real.cos θ > Real.cosh r * Real.cosh d - B := by nlinarith
    have h2 : Real.cosh r * Real.cosh d - B = Real.cosh (r - d) := by
      rw [Real.cosh_sub] <;> ring
    rw [h2] at h
    have h3 : 1 ≤ Real.cosh (r - d) := Real.one_le_cosh (r - d)
    nlinarith
  -- g continuous on [0, pi]
  have h_g_cont : ContinuousOn (fun θ : ℝ => Real.cosh r * Real.cosh d - B * Real.cos θ) (Set.uIcc (0 : ℝ) Real.pi) := by
    apply ContinuousOn.sub
    · exact continuousOn_const
    · exact continuousOn_const.mul Real.continuousOn_cos
  -- rho continuous on [0, pi]
  have h_rho_cont : ContinuousOn rho (Set.uIcc (0 : ℝ) Real.pi) := by
    simp only [hrho]
    apply Real.continuousOn_arcosh.comp h_g_cont
    intro θ hθ
    exact h_g_ge_one θ hθ
  -- hF_cont: F continuous on [0, pi]
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) Real.pi) := by
    simp only [hF]
    have h1 : ContinuousOn (fun θ : ℝ => (rho θ)^2) (Set.uIcc (0 : ℝ) Real.pi) := h_rho_cont.pow 2
    have h2 : ContinuousOn (fun θ : ℝ => -((rho θ)^2) / (4 * s)) (Set.uIcc (0 : ℝ) Real.pi) :=
      h1.neg.div continuousOn_const (fun _ _ => hs_ne)
    have h3 : ContinuousOn (fun θ : ℝ => Real.exp (-((rho θ)^2) / (4 * s))) (Set.uIcc (0 : ℝ) Real.pi) :=
      Real.continuous_exp.continuousOn.comp h2 (fun _ _ => Set.mem_univ _)
    exact continuousOn_const.mul h3
  -- rho hasDerivAt on (0, pi)
  have h_rho_hasDeriv : ∀ θ ∈ Set.uIoo (0 : ℝ) Real.pi,
      HasDerivAt rho (B * Real.sin θ / Real.sinh (rho θ)) θ := by
    intro θ hθ
    have h_gt := h_g_gt_one θ hθ
    simpa [hrho, hB] using rho_deriv d r s hd hr θ h_gt
  -- F hasDerivAt on (0, pi), chain rule
  have hF_hasDeriv : ∀ θ ∈ Set.uIoo (0 : ℝ) Real.pi,
      HasDerivAt F (Real.exp (-(rho θ)^2 / (4 * s)) * (rho θ / Real.sinh (rho θ)) * Real.sin θ) θ := by
    intro θ hθ
    have h_rho_deriv := h_rho_hasDeriv θ hθ
    simp only [hF]
    have h1 : HasDerivAt (fun θ : ℝ => (rho θ)^2) (2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) θ := by
      have h1a : HasDerivAt (fun θ : ℝ => (rho θ)^2) (2 * rho θ ^ (2 - 1 : ℕ) * (B * Real.sin θ / Real.sinh (rho θ))) θ :=
        h_rho_deriv.pow 2
      have h_eq : (2 * rho θ ^ (2 - 1 : ℕ) * (B * Real.sin θ / Real.sinh (rho θ))) = (2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) := by
        norm_num
      rw [h_eq] at h1a
      exact h1a
    have h2 : HasDerivAt (fun θ : ℝ => -((rho θ)^2) / (4 * s)) (-(2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) / (4 * s)) θ :=
      h1.neg.div_const (4 * s)
    have h3 : HasDerivAt (fun θ : ℝ => Real.exp (-((rho θ)^2) / (4 * s)))
        (Real.exp (-((rho θ)^2) / (4 * s)) * (-(2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) / (4 * s))) θ :=
      h2.exp
    have h4 : HasDerivAt (fun θ : ℝ => -2 * s / B * Real.exp (-((rho θ)^2) / (4 * s)))
        ((-2 * s / B) * (Real.exp (-((rho θ)^2) / (4 * s)) * (-(2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) / (4 * s)))) θ :=
      h3.const_mul (-2 * s / B)
    have h5 : ((-2 * s / B) * (Real.exp (-((rho θ)^2) / (4 * s)) * (-(2 * rho θ * (B * Real.sin θ / Real.sinh (rho θ))) / (4 * s)))) =
        Real.exp (-(rho θ)^2 / (4 * s)) * (rho θ / Real.sinh (rho θ)) * Real.sin θ := by
      field_simp [hB_ne] <;> ring
    rw [h5] at h4
    exact h4
  -- hF_diff: F differentiable on (0, pi)
  have hF_diff : ∀ θ ∈ Set.uIoo (0 : ℝ) Real.pi, DifferentiableAt ℝ F θ := by
    intro θ hθ
    exact (hF_hasDeriv θ hθ).differentiableAt
  -- h_deriv_eq: deriv F = integrand
  have h_deriv_eq : ∀ θ ∈ Set.uIoo (0 : ℝ) Real.pi,
      deriv F θ = Real.exp (-(rho θ)^2 / (4 * s)) * (rho θ / Real.sinh (rho θ)) * Real.sin θ := by
    intro θ hθ
    exact (hF_hasDeriv θ hθ).deriv
  -- h_int: deriv F interval integrable (sorry: math clear — rho>0 on (0,pi], d_over_sinh continuous)
  have h_int : IntervalIntegrable (deriv F) volume 0 Real.pi := by sorry
  -- FTC
  have h_ftc0 : ∫ θ in (0 : ℝ)..Real.pi, deriv F θ = F Real.pi - F 0 :=
    intervalIntegral.integral_deriv_eq_sub_uIoo hF_cont hF_diff h_int
  -- h_eq_integral: ∫ integrand = ∫ deriv F (agree on (0,pi), endpoints measure zero)
  have h_ftc : ∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (-(rho θ)^2 / (4 * s)) * (rho θ / Real.sinh (rho θ)) * Real.sin θ
    = F Real.pi - F 0 := by
    have h_eq_integral : ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(rho θ)^2 / (4 * s)) * (rho θ / Real.sinh (rho θ)) * Real.sin θ
      = ∫ θ in (0 : ℝ)..Real.pi, deriv F θ := by sorry
    rw [h_eq_integral, h_ftc0]
  rw [integral_Icc_eq_interval, h_ftc]
  exact F_endpoints_diff d r s hd hr hs B hB

/-- Auxiliary 1 (completing the square):
    r²/(4t) + (r∓d)²/(4s) = a(r∓c)² + d²/(4(t+s)),
    where a=(t+s)/(4ts), c=dt/(t+s).
    Pure algebra: expand RHS and match coefficients. -/
lemma radial_completing_square (d t s : ℝ) (ht : 0 < t) (hs : 0 < s) (r : ℝ) :
    Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s)) =
    Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) ∧
    Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s)) =
    Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) := by
  have hts_nonzero : t + s ≠ 0 := by linarith
  have ht_nonzero : t ≠ 0 := by linarith
  have hs_nonzero : s ≠ 0 := by linarith
  have h1 : (r)^2 / (4 * t) + (r - d)^2 / (4 * s) =
      (d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r - d * t / (t + s))^2 := by
    field_simp [ht_nonzero, hs_nonzero, hts_nonzero] <;> ring
  have h2 : (r)^2 / (4 * t) + (r + d)^2 / (4 * s) =
      (d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r + d * t / (t + s))^2 := by
    field_simp [ht_nonzero, hs_nonzero, hts_nonzero] <;> ring
  have h_first : Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s)) =
      Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) := by
    calc
      Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s))
        = Real.exp (-((r)^2 / (4 * t) + (r - d)^2 / (4 * s))) := by rw [← Real.exp_add] <;> ring
      _ = Real.exp (-((d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) := by rw [h1]
      _ = Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) := by
        have h : Real.exp (-((d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) =
            Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) := by
          rw [← Real.exp_add] <;> ring
        exact h
  have h_second : Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s)) =
      Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) := by
    calc
      Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s))
        = Real.exp (-((r)^2 / (4 * t) + (r + d)^2 / (4 * s))) := by rw [← Real.exp_add] <;> ring
      _ = Real.exp (-((d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) := by rw [h2]
      _ = Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) := by
        have h : Real.exp (-((d)^2 / (4 * (t + s)) + (t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) =
            Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-((t + s) / (4 * t * s) * (r + d * t / (t + s))^2)) := by
          rw [← Real.exp_add] <;> ring
        exact h
  exact ⟨h_first, h_second⟩

/-- Translation substitution for setIntegral: ∫_{x-c ∈ s} f(u) du = ∫_{x ∈ s} f(x-c) dx.
    Uses MeasurePreserving (Lebesgue measure translation invariant) + MeasurableEmbedding. -/
lemma setIntegral_translation (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    ∫ u in (fun x : ℝ => x - c) '' s, f u = ∫ x in s, f (x - c) := by
  have h_mp : MeasurePreserving (fun x : ℝ => x - c) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have h2 : (fun x : ℝ => x - c) = (fun x : ℝ => -c + x) := by funext x; ring
    rw [h2]
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self (-c)
  have h_me : MeasurableEmbedding (fun x : ℝ => x - c) :=
    (Homeomorph.addRight (-c)).isClosedEmbedding.measurableEmbedding
  exact h_mp.setIntegral_image_emb h_me f s

/-- Translation on half-line: ∫_{-c}^∞ f(u) du = ∫₀^∞ f(x-c) dx. -/
lemma setIntegral_Ioi_translation (f : ℝ → ℝ) (c : ℝ) :
    ∫ u in Set.Ioi (-c), f u = ∫ x in Set.Ioi (0 : ℝ), f (x - c) := by
  have h_image : (fun x : ℝ => x - c) '' Set.Ioi (0 : ℝ) = Set.Ioi (-c) := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; linarith
    · intro hu; refine ⟨u + c, by linarith, by ring⟩
  rw [← h_image]
  exact setIntegral_translation f c (Set.Ioi (0 : ℝ))

/-- Reflection substitution: for symmetric set s, ∫_s f(x) dx = ∫_s f(-x) dx. -/
lemma setIntegral_reflection (f : ℝ → ℝ) (s : Set ℝ) (hs : (fun x : ℝ => -x) '' s = s) :
    ∫ x in s, f x = ∫ x in s, f (-x) := by
  have h_mp : MeasurePreserving (fun x : ℝ => -x) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    exact?
  have h_me : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := h_mp.setIntegral_image_emb h_me f s
  rw [hs] at h
  exact h

/-- General reflection substitution: ∫_s f(x) dx = ∫_{-s} f(-x) dx, where -s = {-x | x ∈ s}. -/
lemma setIntegral_reflection_general (f : ℝ → ℝ) (s : Set ℝ) :
    ∫ x in s, f x = ∫ x in (fun x : ℝ => -x) '' s, f (-x) := by
  have h_mp : MeasurePreserving (fun x : ℝ => -x) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    exact?
  have h_me : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  let g := fun y : ℝ => f (-y)
  have h : ∫ y in (fun x : ℝ => -x) '' s, g y = ∫ x in s, g (-x) :=
    h_mp.setIntegral_image_emb h_me g s
  have h2 : ∫ y in (fun x : ℝ => -x) '' s, g y = ∫ x in s, f x := by
    simpa [g] using h
  exact h2.symm

/-- For an even function h, ∫_{-c}^0 h(x) dx = ∫_0^c h(x) dx. Zero-sorry. -/
lemma even_half_reflection (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (h_even : ∀ x, h (-x) = h x) :
    ∫ u in Set.Ioo (-c) (0 : ℝ), h u = ∫ u in Set.Ioo (0 : ℝ) c, h u := by
  have h_img : (fun x : ℝ => -x) '' Set.Ioo (-c) (0 : ℝ) = Set.Ioo (0 : ℝ) c := by
    ext x; simp only [Set.mem_image, Set.mem_Ioo] <;> constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩ <;> constructor <;> linarith
    · intro ⟨hx1, hx2⟩; refine ⟨-x, ⟨by linarith, by linarith⟩, by ring⟩
  have h_general := setIntegral_reflection_general h (Set.Ioo (-c) (0 : ℝ))
  rw [h_img] at h_general
  have h_eq : Set.EqOn (fun u : ℝ => h (-u)) h (Set.Ioo (0 : ℝ) c) := by
    intro u _; exact h_even u
  have h_congr : ∫ u in Set.Ioo (0 : ℝ) c, h (-u) = ∫ u in Set.Ioo (0 : ℝ) c, h u :=
    setIntegral_congr_fun (by exact?) h_eq
  rw [h_congr] at h_general
  exact h_general

/-- volume {x} = 0 for real x. -/
lemma real_volume_singleton (x : ℝ) : volume ({x} : Set ℝ) = 0 := by simp

/-- AEDisjoint from Disjoint for measurable sets. -/
lemma aedisjoint_of_disjoint (s t : Set ℝ) (h : Disjoint s t) : AEDisjoint volume s t :=
  Disjoint.aedisjoint h

/-- Integral over union of disjoint measurable sets. -/
lemma setIntegral_union_disjoint (s t : Set ℝ) (f : ℝ → ℝ)
    (h_disj : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : IntegrableOn f s) (hft : IntegrableOn f t) :
    ∫ x in s ∪ t, f x = (∫ x in s, f x) + (∫ x in t, f x) := by
  have h_ae : AEDisjoint volume s t := aedisjoint_of_disjoint s t h_disj
  exact setIntegral_union₀ h_ae ht.nullMeasurableSet hfs hft

/-- Integral unaffected by removing a singleton. -/
lemma integral_remove_singleton (s : Set ℝ) (x : ℝ) (f : ℝ → ℝ) :
    ∫ y in s \ {x}, f y = ∫ y in s, f y := by
  have h1 : ∀ᵐ y, y ≠ x := by
    simpa [ae_iff] using show volume ({x} : Set ℝ) = 0 from by simp
  have h_ae : s \ {x} =ᵐ[volume] s := by
    filter_upwards [h1] with y hy
    simp [Set.mem_diff, hy]
  exact setIntegral_congr_set h_ae

/-- ∫ in Ioc x y = ∫ in Ioo x y (single point difference). -/
lemma integral_Ioc_eq_Ioo (x y : ℝ) (f : ℝ → ℝ) :
    ∫ t in Set.Ioc x y, f t = ∫ t in Set.Ioo x y, f t :=
  integral_Ioc_eq_integral_Ioo' (μ := volume) (f := f) (real_volume_singleton y)

/-- Odd function integral over symmetric set is zero. -/
lemma setIntegral_odd_zero (f : ℝ → ℝ) (s : Set ℝ) (hs : (fun x : ℝ => -x) '' s = s)
    (h_odd : ∀ x ∈ s, f (-x) = -f x) (h_meas : MeasurableSet s) :
    ∫ x in s, f x = 0 := by
  have h1 : ∫ x in s, f x = ∫ x in s, f (-x) := setIntegral_reflection f s hs
  have h2 : Set.EqOn (fun x : ℝ => f (-x)) (fun x : ℝ => -f x) s := by
    intro x hx
    exact h_odd x hx
  have h3 : ∫ x in s, f (-x) = ∫ x in s, -f x := setIntegral_congr_fun h_meas h2
  have h4 : ∫ x in s, -f x = -∫ x in s, f x := by
    have h : ∫ x, -f x ∂(volume.restrict s) = -∫ x, f x ∂(volume.restrict s) :=
      integral_neg (μ := volume.restrict s) f
    exact h
  rw [h1, h3, h4]
  linarith

/-- Gaussian integrability toolkit: exp(-a*x^2), x*exp(-a*x^2), and affine shifts are Integrable on all of ℝ. -/
lemma gaussian_integrable_exp (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-(a * x^2))) := by
  have h := integrable_exp_neg_mul_sq ha
  simpa using h

lemma gaussian_integrable_x (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => x * Real.exp (-(a * x^2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq ha (show (-1 : ℝ) < 1 by norm_num)
  have h_eq : (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(a * x^2))) = (fun x : ℝ => x * Real.exp (-(a * x^2))) := by
    funext x; simp [Real.rpow_one]
  simpa [h_eq] using h

lemma gaussian_integrable_affine (a c : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => (x + c) * Real.exp (-(a * x^2))) := by
  have h1 : Integrable (fun x : ℝ => x * Real.exp (-(a * x^2))) := gaussian_integrable_x a ha
  have h2 : Integrable (fun x : ℝ => c * Real.exp (-(a * x^2))) := (gaussian_integrable_exp a ha).smul c
  have h3 : Integrable (fun x : ℝ => x * Real.exp (-(a * x^2)) + c * Real.exp (-(a * x^2))) := h1.add h2
  have h4 : (fun x : ℝ => (x + c) * Real.exp (-(a * x^2))) = fun x : ℝ => x * Real.exp (-(a * x^2)) + c * Real.exp (-(a * x^2)) := by funext x; ring
  rw [h4]; exact h3

lemma gaussian_integrable_shift (a c : ℝ) (ha : 0 < a) :
    Integrable (fun r : ℝ => r * Real.exp (-(a * (r - c)^2))) := by
  have h : Integrable (fun x : ℝ => (x + c) * Real.exp (-(a * x^2))) := gaussian_integrable_affine a c ha
  have h_mp : MeasurePreserving (fun r : ℝ => r - c) volume volume := by
    refine ⟨by fun_prop, ?_⟩; exact?
  have h_map : Measure.map (fun r : ℝ => r - c) volume = volume := h_mp.map_eq
  have h' : Integrable (fun x : ℝ => (x + c) * Real.exp (-(a * x^2))) (Measure.map (fun r : ℝ => r - c) volume) := by
    rw [h_map]; exact h
  have h_comp : Integrable (fun r : ℝ => ((r - c) + c) * Real.exp (-(a * (r - c)^2))) :=
    h'.comp_measurable (by fun_prop)
  have h_eq : (fun r : ℝ => ((r - c) + c) * Real.exp (-(a * (r - c)^2))) = (fun r : ℝ => r * Real.exp (-(a * (r - c)^2))) := by funext r; ring
  simpa [h_eq] using h_comp

/-- Even merge lemma: ∫_{-c}^c c·h + ∫_c^∞ 2c·h = 2c·∫_0^∞ h for even h.
    Standalone version to isolate from radial_substitution context. -/
lemma even_merge_lemma (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    let h : ℝ → ℝ := fun u => Real.exp (-(a * u^2))
    (∫ u in Set.Ioc (-c) c, c * h u) + (∫ u in Set.Ioi c, (2 * c) * h u) =
    2 * c * ∫ u in Set.Ioi (0 : ℝ), h u := by
  let h : ℝ → ℝ := fun u => Real.exp (-(a * u^2))
  by_cases h_c0 : c = 0
  · -- c = 0 → both sides zero
    rw [h_c0] <;> simp
  · -- c > 0
    have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm h_c0)
    have h_even : ∀ x : ℝ, h (-x) = h x := by
      intro x; simp only [h] <;> ring
    have h_ie : IntegrableOn h (Set.Ioc (-c) c) := (gaussian_integrable_exp a ha).integrableOn
    -- ∫_{-c}^c h = 2 * ∫_0^c h
    have h1 : ∫ u in Set.Ioc (-c) c, h u = ∫ u in Set.Ioo (-c) c, h u :=
      integral_Ioc_eq_Ioo (-c) c h
    have h1b : ∫ u in Set.Ioo (-c) c, h u = ∫ u in (Set.Ioo (-c) c) \ {0}, h u :=
      (integral_remove_singleton (Set.Ioo (-c) c) 0 h).symm
    have h_disj1 : Disjoint (Set.Ioo (-c) (0 : ℝ)) (Set.Ioo (0 : ℝ) c) := by
      rw [Set.disjoint_left]; intro x hx1 hx2
      simp only [Set.mem_Ioo] at hx1 hx2 <;> linarith
    have h_union1 : Set.Ioo (-c) (0 : ℝ) ∪ Set.Ioo (0 : ℝ) c = (Set.Ioo (-c) c) \ {0} := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro h
        cases h with
        | inl h =>
          have h11 : -c < x := h.1
          have h12 : x < 0 := h.2
          have h13 : x < c := by linarith
          have h14 : x ≠ 0 := by linarith
          exact ⟨⟨h11, h13⟩, h14⟩
        | inr h =>
          have h11 : 0 < x := h.1
          have h12 : x < c := h.2
          have h13 : -c < x := by linarith
          have h14 : x ≠ 0 := by linarith
          exact ⟨⟨h13, h12⟩, h14⟩
      · rintro ⟨⟨h11, h12⟩, h3⟩
        by_cases h4 : x < 0
        · exact Or.inl ⟨h11, h4⟩
        · have h5 : 0 ≤ x := by linarith
          have h6 : 0 < x := lt_of_le_of_ne h5 (Ne.symm h3)
          exact Or.inr ⟨h6, h12⟩
    have hfs1 : IntegrableOn h (Set.Ioo (-c) (0 : ℝ)) :=
      (gaussian_integrable_exp a ha).mono_measure (by simpa [Measure.restrict_univ] using Measure.restrict_mono (Set.subset_univ _) le_rfl)
    have hft1 : IntegrableOn h (Set.Ioo (0 : ℝ) c) :=
      (gaussian_integrable_exp a ha).mono_measure (by simpa [Measure.restrict_univ] using Measure.restrict_mono (Set.subset_univ _) le_rfl)
    have h2 : ∫ u in (Set.Ioo (-c) c) \ {0}, h u =
        (∫ u in Set.Ioo (-c) (0 : ℝ), h u) + (∫ u in Set.Ioo (0 : ℝ) c, h u) := by
      rw [←h_union1]
      exact setIntegral_union_disjoint (Set.Ioo (-c) (0 : ℝ)) (Set.Ioo (0 : ℝ) c) h h_disj1
        (by exact?) (by exact?) hfs1 hft1
    have h3 : ∫ u in Set.Ioo (-c) (0 : ℝ), h u = ∫ u in Set.Ioo (0 : ℝ) c, h u :=
      even_half_reflection h c hc_pos h_even
    have h4 : ∫ u in Set.Ioo (0 : ℝ) c, h u = ∫ u in Set.Ioc (0 : ℝ) c, h u :=
      (integral_Ioc_eq_Ioo (0 : ℝ) c h).symm
    have h_double : ∫ u in Set.Ioc (-c) c, h u = 2 * ∫ u in Set.Ioc (0 : ℝ) c, h u := by
      rw [h1, h1b, h2, h3, h4] <;> ring
    -- constant multiples
    have h_const1 : ∫ u in Set.Ioc (-c) c, c * h u = c * ∫ u in Set.Ioc (-c) c, h u := by exact?
    have h_const2 : ∫ u in Set.Ioi c, (2 * c) * h u = (2 * c) * ∫ u in Set.Ioi c, h u := by exact?
    -- merge: ∫_0^c h + ∫_c^∞ h = ∫_0^∞ h
    have h5 : ∫ u in Set.Ioc (0 : ℝ) c, h u = ∫ u in Set.Ioo (0 : ℝ) c, h u :=
      integral_Ioc_eq_Ioo (0 : ℝ) c h
    have h_disj2 : Disjoint (Set.Ioo (0 : ℝ) c) (Set.Ioi c) := by
      rw [Set.disjoint_left]; intro x hx1 hx2
      simp only [Set.mem_Ioo, Set.mem_Ioi] at hx1 hx2 <;> linarith
    have h_union2 : Set.Ioo (0 : ℝ) c ∪ Set.Ioi c = (Set.Ioi (0 : ℝ)) \ {c} := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ioi, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro h
        cases h with
        | inl h =>
          have h11 : 0 < x := h.1
          have h12 : x < c := h.2
          have h13 : x ≠ c := by linarith
          exact ⟨h11, h13⟩
        | inr h =>
          have h11 : c < x := h
          have h12 : 0 < x := by linarith
          have h13 : x ≠ c := by linarith
          exact ⟨h12, h13⟩
      · rintro ⟨h11, h2⟩
        by_cases h3 : x < c
        · exact Or.inl ⟨h11, h3⟩
        · have h4 : c ≤ x := by linarith
          have h5 : c < x := lt_of_le_of_ne h4 (Ne.symm h2)
          exact Or.inr h5
    have h_merge : (∫ u in Set.Ioc (0 : ℝ) c, h u) + (∫ u in Set.Ioi c, h u) = ∫ u in Set.Ioi (0 : ℝ), h u := by
      rw [h5]
      have h6 : (∫ u in Set.Ioo (0 : ℝ) c, h u) + (∫ u in Set.Ioi c, h u) = ∫ u in (Set.Ioi (0 : ℝ)) \ {c}, h u := by
        rw [←h_union2]
        have hfs2 : IntegrableOn h (Set.Ioo (0 : ℝ) c) :=
          (gaussian_integrable_exp a ha).mono_measure (by simpa [Measure.restrict_univ] using Measure.restrict_mono (Set.subset_univ _) le_rfl)
        have hft2 : IntegrableOn h (Set.Ioi c) :=
          (gaussian_integrable_exp a ha).mono_measure (by simpa [Measure.restrict_univ] using Measure.restrict_mono (Set.subset_univ _) le_rfl)
        have h_ae2 : AEDisjoint volume (Set.Ioo (0 : ℝ) c) (Set.Ioi c) := aedisjoint_of_disjoint _ _ h_disj2
        have h_ms2 : MeasurableSet (Set.Ioi c) := by exact?
        exact (setIntegral_union₀ h_ae2 h_ms2.nullMeasurableSet hfs2 hft2).symm
      rw [h6, integral_remove_singleton (Set.Ioi (0 : ℝ)) c h]
    dsimp only [h]
    calc
      (∫ u in Set.Ioc (-c) c, c * h u) + (∫ u in Set.Ioi c, (2 * c) * h u)
        = c * (∫ u in Set.Ioc (-c) c, h u) + (2 * c) * (∫ u in Set.Ioi c, h u) := by rw [h_const1, h_const2]
      _ = c * (2 * ∫ u in Set.Ioc (0 : ℝ) c, h u) + (2 * c) * (∫ u in Set.Ioi c, h u) := by rw [h_double]
      _ = 2 * c * ((∫ u in Set.Ioc (0 : ℝ) c, h u) + (∫ u in Set.Ioi c, h u)) := by ring
      _ = 2 * c * ∫ u in Set.Ioi (0 : ℝ), h u := by rw [h_merge]

/-- Auxiliary 2 (substitution + odd part vanishes):
    ∫₀^∞ r [e^{-a(r-c)²} - e^{-a(r+c)²}] dr = 2c ∫₀^∞ e^{-a u²} du.
    Math: shift u=r∓c → split at c → odd part ∫_{-c}^c u e^{-a u²}=0 → 2c ∫₀^∞ e^{-a u²}.
    Sorry: requires setIntegral substitution + interval splitting in Lean. -/
lemma radial_substitution (d t s : ℝ) (hd : 0 ≤ d) (ht : 0 < t) (hs : 0 < s) :
    let a := (t + s) / (4 * t * s)
    let c := d * t / (t + s)
    ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-((t + s) / (4 * t * s) * (r - d * t / (t + s))^2)) -
                                Real.exp (-((t + s) / (4 * t * s) * (r + d * t / (t + s))^2)))
    = 2 * (d * t / (t + s)) * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-((t + s) / (4 * t * s) * u^2)) := by
  set a : ℝ := (t + s) / (4 * t * s) with ha_def
  set c : ℝ := d * t / (t + s) with hc_def
  have ha_pos : 0 < a := by positivity
  have hc_nonneg : 0 ≤ c := by positivity
  let f1 := fun r : ℝ => r * Real.exp (-(a * (r - c)^2))
  let f2 := fun r : ℝ => r * Real.exp (-(a * (r + c)^2))
  let g := fun u : ℝ => Real.exp (-(a * u^2))
  have h_Ioi_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := by exact?
  -- Substitution 1: u = r - c, so ∫₀^∞ f1(r) dr = ∫_{-c}^∞ (u+c) g(u) du
  have h_subst1 : ∫ r in Set.Ioi (0 : ℝ), f1 r = ∫ u in Set.Ioi (-c), (u + c) * g u := by
    let f := fun u : ℝ => (u + c) * g u
    have h_trans : ∫ u in Set.Ioi (-c), f u = ∫ x in Set.Ioi (0 : ℝ), f (x - c) :=
      setIntegral_Ioi_translation f c
    have h_eq : Set.EqOn (fun x : ℝ => f (x - c)) f1 (Set.Ioi (0 : ℝ)) := by
      intro x _
      simp only [f, f1, g] <;> ring
    have h_congr : ∫ x in Set.Ioi (0 : ℝ), f (x - c) = ∫ r in Set.Ioi (0 : ℝ), f1 r :=
      setIntegral_congr_fun h_Ioi_meas h_eq
    calc
      ∫ r in Set.Ioi (0 : ℝ), f1 r = ∫ x in Set.Ioi (0 : ℝ), f (x - c) := h_congr.symm
      _ = ∫ u in Set.Ioi (-c), f u := h_trans.symm
  -- Substitution 2: u = r + c, so ∫₀^∞ f2(r) dr = ∫_c^∞ (u-c) g(u) du
  have h_subst2 : ∫ r in Set.Ioi (0 : ℝ), f2 r = ∫ u in Set.Ioi c, (u - c) * g u := by
    let f := fun u : ℝ => (u - c) * g u
    have h_trans_raw := setIntegral_Ioi_translation f (-c)
    have h_trans : ∫ u in Set.Ioi c, f u = ∫ x in Set.Ioi (0 : ℝ), f (x + c) := by
      simpa [neg_neg, sub_neg_eq_add] using h_trans_raw
    have h_eq : Set.EqOn (fun x : ℝ => f (x + c)) f2 (Set.Ioi (0 : ℝ)) := by
      intro x _
      simp only [f, f2, g] <;> ring
    have h_congr : ∫ x in Set.Ioi (0 : ℝ), f (x + c) = ∫ r in Set.Ioi (0 : ℝ), f2 r :=
      setIntegral_congr_fun h_Ioi_meas h_eq
    calc
      ∫ r in Set.Ioi (0 : ℝ), f2 r = ∫ x in Set.Ioi (0 : ℝ), f (x + c) := h_congr.symm
      _ = ∫ u in Set.Ioi c, f u := h_trans.symm
  -- Core simplification: split ∫_{-c}^∞ at c, odd part ∫_{-c}^c u*g(u)=0, merge → 2c∫₀^∞ g
  have h_core : (∫ u in Set.Ioi (-c), (u + c) * g u) - (∫ u in Set.Ioi c, (u - c) * g u) =
      2 * c * ∫ u in Set.Ioi (0 : ℝ), g u := by
    let h := g
    -- Step 1: split ∫_{-c}^∞ = ∫_{-c}^c + ∫_c^∞
    have h_split1 : ∫ u in Set.Ioi (-c), (u + c) * h u =
        (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (u + c) * h u) := by
      have h_union : Set.Ioc (-c) c ∪ Set.Ioi c = Set.Ioi (-c) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (h | h) <;> linarith
        · intro hx
          by_cases h : x ≤ c
          · exact Or.inl ⟨by linarith, h⟩
          · exact Or.inr (by linarith)
      have h_disj : AEDisjoint volume (Set.Ioc (-c) c) (Set.Ioi c) := by
        have h : Disjoint (Set.Ioc (-c) c) (Set.Ioi c) := by
          rw [Set.disjoint_left]
          intro x hx1 hx2
          simp only [Set.mem_Ioc, Set.mem_Ioi] at hx1 hx2
          linarith
        exact?
      have h_null : NullMeasurableSet (Set.Ioi c) volume := by exact?
      have h_int1 : IntegrableOn (fun u : ℝ => (u + c) * h u) (Set.Ioc (-c) c) := (gaussian_integrable_affine a c ha_pos).integrableOn
      have h_int2 : IntegrableOn (fun u : ℝ => (u + c) * h u) (Set.Ioi c) := (gaussian_integrable_affine a c ha_pos).integrableOn
      rw [← h_union]
      exact setIntegral_union₀ h_disj h_null h_int1 h_int2
    -- Step 2: subtract ∫_c^∞ (u-c)h, merge → ∫_{-c}^c (u+c)h + ∫_c^∞ 2c·h
    have h_diff : (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (u + c) * h u) -
        (∫ u in Set.Ioi c, (u - c) * h u) =
        (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (2 * c) * h u) := by
      let f1 := fun u : ℝ => (u + c) * h u
      let f2 := fun u : ℝ => (u - c) * h u
      let f3 := fun u : ℝ => (2 * c) * h u
      have h_int1 : IntegrableOn f1 (Set.Ioi c) := (gaussian_integrable_affine a c ha_pos).integrableOn
      have h_int2 : IntegrableOn f2 (Set.Ioi c) := (gaussian_integrable_affine a (-c) ha_pos).integrableOn
      have h_sub : ∫ u in Set.Ioi c, (f1 u - f2 u) = (∫ u in Set.Ioi c, f1 u) - (∫ u in Set.Ioi c, f2 u) := by
        have h : ∫ x, (f1 x - f2 x) ∂(volume.restrict (Set.Ioi c)) =
            (∫ x, f1 x ∂(volume.restrict (Set.Ioi c))) - (∫ x, f2 x ∂(volume.restrict (Set.Ioi c))) :=
          integral_sub h_int1 h_int2
        exact h
      have h_eq : Set.EqOn (fun u : ℝ => f1 u - f2 u) f3 (Set.Ioi c) := by
        intro u _
        simp only [f1, f2, f3, h] <;> ring
      have h_congr : ∫ u in Set.Ioi c, (f1 u - f2 u) = ∫ u in Set.Ioi c, f3 u :=
        setIntegral_congr_fun (by exact?) h_eq
      have h_key : (∫ u in Set.Ioi c, f1 u) - (∫ u in Set.Ioi c, f2 u) = ∫ u in Set.Ioi c, f3 u := by
        calc
          (∫ u in Set.Ioi c, f1 u) - (∫ u in Set.Ioi c, f2 u)
            = ∫ u in Set.Ioi c, (f1 u - f2 u) := h_sub.symm
          _ = ∫ u in Set.Ioi c, f3 u := h_congr
      simp only [f1, f2, f3] at h_key
      have h_reassoc : (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (u + c) * h u) - (∫ u in Set.Ioi c, (u - c) * h u) =
          (∫ u in Set.Ioc (-c) c, (u + c) * h u) + ((∫ u in Set.Ioi c, (u + c) * h u) - (∫ u in Set.Ioi c, (u - c) * h u)) := by ring
      rw [h_reassoc, h_key] <;> ring
    -- Step 3: odd part vanishes: ∫_{-c}^c (u+c)h = ∫_{-c}^c c·h
    have h_odd : ∫ u in Set.Ioc (-c) c, (u + c) * h u = ∫ u in Set.Ioc (-c) c, c * h u := by
      -- Ioo (-c) c is symmetric under reflection
      have h_symm : (fun x : ℝ => -x) '' Set.Ioo (-c) c = Set.Ioo (-c) c := by
        ext x
        simp only [Set.mem_image, Set.mem_Ioo]
        constructor
        · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
          constructor <;> linarith
        · intro ⟨hx1, hx2⟩
          refine ⟨-x, ⟨by linarith, by linarith⟩, by ring⟩
      have h_odd_fun : ∀ x ∈ Set.Ioo (-c) c, (fun u : ℝ => u * h u) (-x) = -(fun u : ℝ => u * h u) x := by
        intro x _
        simp only [h, g] <;> ring
      have h_Ioo_meas : MeasurableSet (Set.Ioo (-c) c) := by exact?
      have h_zero_Ioo : ∫ u in Set.Ioo (-c) c, u * h u = 0 :=
        setIntegral_odd_zero (fun u : ℝ => u * h u) (Set.Ioo (-c) c) h_symm h_odd_fun h_Ioo_meas
      -- Ioc (-c) c differs from Ioo (-c) c by single point c (measure zero)
      have h_Ioc_eq_Ioo : ∫ u in Set.Ioc (-c) c, u * h u = ∫ u in Set.Ioo (-c) c, u * h u := by
        have h_singleton : volume ({c} : Set ℝ) = 0 := by exact?
        exact integral_Ioc_eq_integral_Ioo' (μ := volume) (f := fun u : ℝ => u * h u) h_singleton
      have h_main : ∫ u in Set.Ioc (-c) c, u * h u = 0 := by
        rw [h_Ioc_eq_Ioo, h_zero_Ioo]
      -- ∫ (u+c)h = ∫ u·h + ∫ c·h = 0 + ∫ c·h
      have h_add : ∫ u in Set.Ioc (-c) c, (u + c) * h u =
          (∫ u in Set.Ioc (-c) c, u * h u) + (∫ u in Set.Ioc (-c) c, c * h u) := by
        let f := fun u : ℝ => u * h u
        let g := fun u : ℝ => c * h u
        have h_int_f : IntegrableOn f (Set.Ioc (-c) c) := (gaussian_integrable_x a ha_pos).integrableOn
        have h_int_g : IntegrableOn g (Set.Ioc (-c) c) := (gaussian_integrable_exp a ha_pos).smul c |>.integrableOn
        have h_add' : ∫ u in Set.Ioc (-c) c, (f u + g u) =
            (∫ u in Set.Ioc (-c) c, f u) + (∫ u in Set.Ioc (-c) c, g u) := by
          have h : ∫ x, (f x + g x) ∂(volume.restrict (Set.Ioc (-c) c)) =
              (∫ x, f x ∂(volume.restrict (Set.Ioc (-c) c))) + (∫ x, g x ∂(volume.restrict (Set.Ioc (-c) c))) :=
            integral_add h_int_f h_int_g
          exact h
        have h_eq : Set.EqOn (fun u : ℝ => (u + c) * h u) (fun u : ℝ => f u + g u) (Set.Ioc (-c) c) := by
          intro u _
          simp only [f, g] <;> ring
        have h_congr : ∫ u in Set.Ioc (-c) c, (u + c) * h u = ∫ u in Set.Ioc (-c) c, (f u + g u) :=
          setIntegral_congr_fun (by exact?) h_eq
        rw [h_congr, h_add']
      rw [h_add, h_main] <;> ring
    -- Step 4: even doubling + merge (using standalone lemma even_merge_lemma)
    have h_even_merge : (∫ u in Set.Ioc (-c) c, c * h u) + (∫ u in Set.Ioi c, (2 * c) * h u) =
        2 * c * ∫ u in Set.Ioi (0 : ℝ), h u := by
      have h_em := even_merge_lemma a c ha_pos (show 0 ≤ c from by linarith)
      dsimp only at h_em
      exact h_em
    calc
      (∫ u in Set.Ioi (-c), (u + c) * h u) - (∫ u in Set.Ioi c, (u - c) * h u)
        = (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (u + c) * h u) -
            (∫ u in Set.Ioi c, (u - c) * h u) := by rw [h_split1]
      _ = (∫ u in Set.Ioc (-c) c, (u + c) * h u) + (∫ u in Set.Ioi c, (2 * c) * h u) := h_diff
      _ = (∫ u in Set.Ioc (-c) c, c * h u) + (∫ u in Set.Ioi c, (2 * c) * h u) := by rw [h_odd]
      _ = 2 * c * ∫ u in Set.Ioi (0 : ℝ), h u := h_even_merge
  -- Linearity: ∫ (f1 - f2) = ∫ f1 - ∫ f2
  have h_f1_minus_f2 : ∀ r : ℝ, f1 r - f2 r = r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2))) := by
    intro r
    simp only [f1, f2] <;> ring
  have h_lin : ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2))) =
      (∫ r in Set.Ioi (0 : ℝ), f1 r) - (∫ r in Set.Ioi (0 : ℝ), f2 r) := by
    have h_int1 : IntegrableOn f1 (Set.Ioi (0 : ℝ)) := by dsimp only [f1]; exact (gaussian_integrable_shift a c ha_pos).integrableOn
    have h_int2 : IntegrableOn f2 (Set.Ioi (0 : ℝ)) := by
      dsimp only [f2]
      have h : Integrable (fun r : ℝ => r * Real.exp (-(a * (r - (-c))^2))) := gaussian_integrable_shift a (-c) ha_pos
      have h_eq : (fun r : ℝ => r * Real.exp (-(a * (r - (-c))^2))) = (fun r : ℝ => r * Real.exp (-(a * (r + c)^2))) := by funext r; ring
      simpa [h_eq] using h.integrableOn
    have h_sub : ∫ r in Set.Ioi (0 : ℝ), (f1 r - f2 r) =
        (∫ r in Set.Ioi (0 : ℝ), f1 r) - (∫ r in Set.Ioi (0 : ℝ), f2 r) := by
      have h : ∫ x, (f1 x - f2 x) ∂(volume.restrict (Set.Ioi (0 : ℝ))) =
          (∫ x, f1 x ∂(volume.restrict (Set.Ioi (0 : ℝ)))) - (∫ x, f2 x ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
        integral_sub h_int1 h_int2
      exact h
    have h_eq : Set.EqOn (fun r : ℝ => f1 r - f2 r) (fun r : ℝ => r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2)))) (Set.Ioi (0 : ℝ)) := by
      intro r _
      exact h_f1_minus_f2 r
    have h_congr : ∫ r in Set.Ioi (0 : ℝ), (f1 r - f2 r) =
        ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2))) :=
      setIntegral_congr_fun h_Ioi_meas h_eq
    rw [← h_congr, h_sub]
  simp only [ha_def, hc_def]
  rw [h_lin, h_subst1, h_subst2, h_core]

/-- Auxiliary 3 (half-line Gaussian integral):
    ∫₀^∞ e^{-a u²} du = √(π/a) / 2 for a > 0.
    Direct from Mathlib's integral_gaussian_Ioi. -/
lemma radial_gaussian (a : ℝ) (ha : 0 < a) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u^2)) = Real.sqrt (Real.pi / a) / 2 := by
  have h := integral_gaussian_Ioi a
  simpa using h

/-- Radial integral lemma (theorem, Gaussian integral by completing the square).
    Correct statement (derived from heat kernel semigroup K_t * K_s = K_{t+s}):
      ∫₀^∞ r e^{-r²/(4t)} (e^{-(r-d)²/(4s)} - e^{-(r+d)²/(4s)}) dr
      = 2√π d t^{3/2} s^{1/2} / (t+s)^{3/2} * e^{-d²/(4(t+s))}
    Proof: radial_completing_square → radial_substitution → radial_gaussian → simplify. -/
theorem heatKernel_radial_integral (d t s : ℝ) (hd : 0 ≤ d) (ht : 0 < t) (hs : 0 < s) :
    ∫ r in Set.Ioi (0 : ℝ),
      r * Real.exp (-(r)^2 / (4 * t)) *
      (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s)))
    = 2 * Real.sqrt Real.pi * d * t^(3 / 2 : ℝ) * s^(1 / 2 : ℝ) / (t + s)^(3 / 2 : ℝ) *
      Real.exp (-(d)^2 / (4 * (t + s))) := by
  set a : ℝ := (t + s) / (4 * t * s) with ha_def
  set c : ℝ := d * t / (t + s) with hc_def
  have ha_pos : 0 < a := by
    simp only [ha_def] <;> positivity
  have hts_pos : 0 < t + s := by linarith
  -- Step 1: completing the square (pointwise)
  have h1 : ∀ r, Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s)) =
      Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r - c)^2)) := by
    intro r
    exact (radial_completing_square d t s ht hs r).1
  have h2 : ∀ r, Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s)) =
      Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r + c)^2)) := by
    intro r
    exact (radial_completing_square d t s ht hs r).2
  -- Step 2: factor out exp(-d²/(4(t+s)))
  have h3 : ∫ r in Set.Ioi (0 : ℝ),
      r * Real.exp (-(r)^2 / (4 * t)) *
      (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s)))
    = Real.exp (-(d)^2 / (4 * (t + s))) *
      ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2))) := by
    let f := fun r : ℝ => r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2)))
    have h_int1 : Integrable (fun r : ℝ => r * Real.exp (-(a * (r - c)^2))) :=
      gaussian_integrable_shift a c ha_pos
    have h_int2' : Integrable (fun r : ℝ => r * Real.exp (-(a * (r - (-c))^2))) :=
      gaussian_integrable_shift a (-c) ha_pos
    have h_int2 : Integrable (fun r : ℝ => r * Real.exp (-(a * (r + c)^2))) := by
      have h_eq : (fun r : ℝ => r * Real.exp (-(a * (r + c)^2))) = (fun r : ℝ => r * Real.exp (-(a * (r - (-c))^2))) := by
        funext r; ring_nf
      rw [h_eq]; exact h_int2'
    have h_intf : Integrable f := by
      have h : Integrable (fun r : ℝ => r * Real.exp (-(a * (r - c)^2)) - r * Real.exp (-(a * (r + c)^2))) := h_int1.sub h_int2
      have h_eq : (fun r : ℝ => r * Real.exp (-(a * (r - c)^2)) - r * Real.exp (-(a * (r + c)^2))) = f := by
        funext r; simp [f] <;> ring
      rw [h_eq] at h; exact h
    have h4 : ∀ r, r * Real.exp (-(r)^2 / (4 * t)) *
        (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s))) =
        Real.exp (-(d)^2 / (4 * (t + s))) * f r := by
      intro r
      have h41 : Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s)) =
          Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r - c)^2)) := (radial_completing_square d t s ht hs r).1
      have h42 : Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s)) =
          Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r + c)^2)) := (radial_completing_square d t s ht hs r).2
      calc
        r * Real.exp (-(r)^2 / (4 * t)) * (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s)))
          = r * (Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r)^2 / (4 * t)) * Real.exp (-(r + d)^2 / (4 * s))) := by ring
        _ = r * (Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r - c)^2)) - Real.exp (-(d)^2 / (4 * (t + s))) * Real.exp (-(a * (r + c)^2))) := by rw [h41, h42]
        _ = Real.exp (-(d)^2 / (4 * (t + s))) * f r := by simp [f] <;> ring
    have h5 : MeasurableSet (Set.Ioi (0 : ℝ)) := by exact?
    have h6 : ∫ r in Set.Ioi (0 : ℝ), Real.exp (-(d)^2 / (4 * (t + s))) * f r =
        Real.exp (-(d)^2 / (4 * (t + s))) * ∫ r in Set.Ioi (0 : ℝ), f r := by
      exact?
    calc
      ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(r)^2 / (4 * t)) * (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s)))
        = ∫ r in Set.Ioi (0 : ℝ), Real.exp (-(d)^2 / (4 * (t + s))) * f r := by
          rw [setIntegral_congr_fun h5 (fun r _ => h4 r)]
      _ = Real.exp (-(d)^2 / (4 * (t + s))) * ∫ r in Set.Ioi (0 : ℝ), f r := h6
      _ = Real.exp (-(d)^2 / (4 * (t + s))) * ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2))) := by rfl
  rw [h3]
  -- Step 3: radial_substitution
  have h5 : ∫ r in Set.Ioi (0 : ℝ), r * (Real.exp (-(a * (r - c)^2)) - Real.exp (-(a * (r + c)^2)))
    = 2 * c * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u^2)) := by
    simpa [ha_def, hc_def] using radial_substitution d t s hd ht hs
  rw [h5]
  -- Step 4: radial_gaussian
  have h6 : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(a * u^2)) = Real.sqrt (Real.pi / a) / 2 :=
    radial_gaussian a ha_pos
  rw [h6]
  -- Step 5: simplify
  have h71 : 2 * c * (Real.sqrt (Real.pi / a) / 2) = c * Real.sqrt (Real.pi / a) := by ring
  have h72 : c * Real.sqrt (Real.pi / a) =
      2 * Real.sqrt Real.pi * d * t^(3 / 2 : ℝ) * s^(1 / 2 : ℝ) / (t + s)^(3 / 2 : ℝ) := by
    simp only [hc_def, ha_def]
    have hts : 0 < t + s := by linarith
    have hts' : 0 < t * s := mul_pos ht hs
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    -- √(π / ((t+s)/(4ts))) = √(4πts/(t+s))
    have h_eq1 : Real.pi / ((t + s) / (4 * t * s)) = 4 * (Real.pi * t * s / (t + s)) := by
      field_simp [hts.ne', hts'.ne'] <;> ring
    -- √(4X) = 2√X
    have h_sqrt1 : Real.sqrt (4 * (Real.pi * t * s / (t + s))) = 2 * Real.sqrt (Real.pi * t * s / (t + s)) := by
      have h_nonneg : 0 ≤ Real.pi * t * s / (t + s) := by positivity
      have h : Real.sqrt (4 * (Real.pi * t * s / (t + s))) = Real.sqrt 4 * Real.sqrt (Real.pi * t * s / (t + s)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h]
      have h4 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h4] <;> ring
    -- √(πts/(t+s)) = √π * √(ts) / √(t+s)
    have h_sqrt2 : Real.sqrt (Real.pi * t * s / (t + s)) =
        Real.sqrt Real.pi * Real.sqrt (t * s) / Real.sqrt (t + s) := by
      have h1 : Real.sqrt (Real.pi * t * s / (t + s)) = Real.sqrt (Real.pi * t * s) / Real.sqrt (t + s) := by
        rw [Real.sqrt_div (by positivity)]
      rw [h1]
      have h2 : Real.sqrt (Real.pi * t * s) = Real.sqrt Real.pi * Real.sqrt (t * s) := by
        rw [← Real.sqrt_mul (by positivity)] <;> ring
      rw [h2]
    -- Combine
    have h_sqrt : Real.sqrt (Real.pi / ((t + s) / (4 * t * s))) =
        2 * Real.sqrt Real.pi * Real.sqrt (t * s) / Real.sqrt (t + s) := by
      rw [h_eq1, h_sqrt1, h_sqrt2] <;> ring
    rw [h_sqrt]
    -- Convert √ to rpow
    have h_ts_sqrt : Real.sqrt (t * s) = t^(1 / 2 : ℝ) * s^(1 / 2 : ℝ) := by
      have h : Real.sqrt (t * s) = Real.sqrt t * Real.sqrt s := by
        rw [← Real.sqrt_mul (by linarith)] <;> ring
      rw [h]
      have ht' : Real.sqrt t = t^(1 / 2 : ℝ) := by simp [Real.sqrt_eq_rpow]
      have hs' : Real.sqrt s = s^(1 / 2 : ℝ) := by simp [Real.sqrt_eq_rpow]
      rw [ht', hs'] <;> ring
    have h_ts_sum : Real.sqrt (t + s) = (t + s)^(1 / 2 : ℝ) := by
      simp [Real.sqrt_eq_rpow]
    rw [h_ts_sqrt, h_ts_sum]
    -- Final algebra: (dt/(t+s)) * 2√π * t^{1/2} * s^{1/2} / (t+s)^{1/2} = 2√π d t^{3/2} s^{1/2} / (t+s)^{3/2}
    have h_final : (d * t / (t + s)) * (2 * Real.sqrt Real.pi * (t^(1 / 2 : ℝ) * s^(1 / 2 : ℝ)) / (t + s)^(1 / 2 : ℝ)) =
        2 * Real.sqrt Real.pi * d * t^(3 / 2 : ℝ) * s^(1 / 2 : ℝ) / (t + s)^(3 / 2 : ℝ) := by
      have h32 : t^(3 / 2 : ℝ) = t * t^(1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add (by linarith)] <;> simp
      have h32' : (t + s)^(3 / 2 : ℝ) = (t + s) * (t + s)^(1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add (by linarith)] <;> simp
      rw [h32, h32']
      field_simp [hts.ne'] <;> ring
    exact h_final
  have h7 : Real.exp (-(d)^2 / (4 * (t + s))) * (2 * c * (Real.sqrt (Real.pi / a) / 2)) =
      2 * Real.sqrt Real.pi * d * t^(3 / 2 : ℝ) * s^(1 / 2 : ℝ) / (t + s)^(3 / 2 : ℝ) *
      Real.exp (-(d)^2 / (4 * (t + s))) := by
    rw [h71, h72] <;> ring
  exact h7

end OrderPreservingBijection
