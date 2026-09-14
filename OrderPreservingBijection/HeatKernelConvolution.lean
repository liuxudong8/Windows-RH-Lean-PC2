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
  sorry

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
  -- h_int: deriv F interval integrable (standard: continuous on (0,pi), bounded near endpoints)
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
  sorry

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
  -- Step 2: factor out exp(-d²/(4(t+s))) and apply substitution
  sorry

end OrderPreservingBijection
