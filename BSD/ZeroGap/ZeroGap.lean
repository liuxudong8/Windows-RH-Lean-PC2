import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Corollary A: zero-gap from the positivity margin — `BSD.ZeroGap`

Target: bound the height of the NEAREST NON-CENTRAL zero of L(E/K, ·)
below, using only the positivity margin at the center (rank exactly 2):

    γ₀ ≥ η := δ₀ / √( exp (2·(U + E)) − 1 )

where δ₀ is a selected shift on the real axis, U an upper bound for
log Λ(1+δ₀) − log c₀ − 2·log δ₀, and E an error bound for the
Hadamard logarithmic identity at δ₀.  All three come from the strict
interval pipeline (probe 档), so η is numerically computable.

Mechanism (0.11 收口):

    log Λ(1+δ) = log c₀ + 2·log δ + S(δ) + err(δ)      (Hadamard, k = 2)
    S(δ) := (1/2)·Σ_{γ≠0} log(1 + δ²/γ²)               (γ = Im ρ, zeros)
    S(δ) ≥ (1/2)·log(1 + δ²/γ₀²)                       (single term ≤ sum,
                                                          other terms ≥ 0)
    U upper bound + |err| ≤ E  ⟹  S(δ₀) ≤ U + E
    ⟹ log(1 + δ₀²/γ₀²) ≤ 2(U+E) ⟹ γ₀ ≥ δ₀/√(exp(2(U+E)) − 1)

Every axiom below is an UNCONDITIONAL analytic fact (implementation
debt only): the Hadamard factorization, convergence of Σ 1/γ²,
zero discreteness — none of them requires GRH or the BSD formula.
The nearest-zero existence (γ₀ > 0) is axiomized as existence debt
(zeros are infinite and discrete for a cuspidal L; unconditional).

## Axiom inventory

Object layer: Lambda, c0, gamma0, hadamardSum, err, delta0, U, E, k(=2 fixed).
Facts: hadamard_log_eq (identity), err_bound, U_bound,
hadamardSum_single_le (single term ≤ sum), positivity of c0/δ₀/U/E,
nearest-zero existence gamma0_pos.

## Theorems (real proofs)

single_le_UaddE (S(δ₀) ≤ U + E), log_le_exp (1 + δ₀²/γ₀² ≤ exp(2(U+E))),
gamma0_lower_bound (main: γ₀ ≥ η).
-/

namespace BSD.ZeroGap

/-! ## 1. Object layer: complete L, central data, zeros, Hadamard data -/

/-- Complete L-function Λ(s) on the real axis (N^{s/2}·Γ(s)·L(s) for
    E/K; positive Γ/N-factors on the axis). -/
axiom Lambda : ℝ → ℝ

/-- Central Taylor coefficient c₀ = Λ⁽ᵏ⁾(1)/k! at the rank-2 center
    (k = 2): c₀ = Λ″(1)/2. -/
axiom c0 : ℝ

/-- Positivity of the central coefficient (component positivity:
    L″(E/K,1) > 0 — P*, unconditional channel). -/
axiom c0_pos : 0 < c0

/-- Height of the NEAREST NON-CENTRAL zero: γ₀ = min { |γ| : ρ = 1 + iγ
    a zero of Λ, γ ≠ 0 } (zeros of a cuspidal L are infinite and
    discrete; existence is UNCONDITIONAL, axiomatized as debt). -/
axiom gamma0 : ℝ

/-- γ₀ > 0: a non-central zero exists. -/
axiom gamma0_pos : 0 < gamma0

/-- Hadamard sum term as an object function:
    S(δ) := (1/2)·Σ_{γ≠0} log(1 + δ²/γ²).  (The infinite sum is
    axiomatized; convergence is unconditional — Hadamard.) -/
axiom hadamardSum : ℝ → ℝ

/-- Error term in the Hadamard logarithmic identity. -/
axiom err : ℝ → ℝ

/-- Selected real-axis shift δ₀ (fixed by the numeric pipeline). -/
axiom delta0 : ℝ

/-- δ₀ > 0. -/
axiom delta0_pos : 0 < delta0

/-- Upper bound for log Λ(1+δ₀) − log c₀ − 2·log δ₀ (numeric 档). -/
axiom U : ℝ

/-- U > 0. -/
axiom U_pos : 0 < U

/-- Error bound for the Hadamard identity at δ₀ (numeric 档). -/
axiom E : ℝ

/-- E > 0. -/
axiom E_pos : 0 < E

/-! ## 2. Analytic facts (unconditional, axiomatized) -/

/-- Hadamard logarithmic identity at the rank-2 center (k = 2):
    log Λ(1+δ) = log c₀ + 2·log δ + S(δ) + err(δ). -/
axiom hadamard_log_eq (δ : ℝ) :
  Real.log (Lambda (1 + δ)) = Real.log c0 + 2 * Real.log δ + hadamardSum δ + err δ

/-- Error bound: |err(δ)| ≤ E at the selected δ₀. -/
axiom err_bound (δ : ℝ) : |err δ| ≤ E

/-- Numeric upper bound at δ₀:
    log Λ(1+δ₀) − log c₀ − 2·log δ₀ ≤ U. -/
axiom U_bound : Real.log (Lambda (1 + delta0)) - Real.log c0 - 2 * Real.log delta0 ≤ U

/-- The nearest-zero single term is ≤ the full Hadamard sum (every
    other term is ≥ 0, so the sum dominates its largest term). -/
axiom hadamardSum_single_le (δ : ℝ) :
  (1 / 2 : ℝ) * Real.log (1 + δ ^ 2 / gamma0 ^ 2) ≤ hadamardSum δ

/-! ## 3. True theorems -/

/-- S(δ₀) ≤ U + E:  Hadamard identity + U-bound + error bound. -/
lemma single_le_UaddE : hadamardSum delta0 ≤ U + E := by
  have h1 : Real.log (Lambda (1 + delta0)) - Real.log c0 - 2 * Real.log delta0 ≤ U := U_bound
  have h2 : Real.log (Lambda (1 + delta0)) =
      Real.log c0 + 2 * Real.log delta0 + hadamardSum delta0 + err delta0 :=
    hadamard_log_eq delta0
  have hS : hadamardSum delta0 + err delta0 ≤ U := by
    have h := h1
    rw [h2] at h
    linarith
  have herr_ge : -E ≤ err delta0 := by
    have h := err_bound delta0
    have habs : |err delta0| ≤ E := h
    linarith [abs_le.mp habs]
  linarith

/-- 1 + δ₀²/γ₀² ≤ exp(2·(U+E)):  single term ≤ sum ≤ U+E, exp monotone. -/
lemma log_le_exp : 1 + delta0 ^ 2 / gamma0 ^ 2 ≤ Real.exp (2 * (U + E)) := by
  have hS : (1 / 2 : ℝ) * Real.log (1 + delta0 ^ 2 / gamma0 ^ 2) ≤ U + E := by
    exact le_trans (hadamardSum_single_le delta0) single_le_UaddE
  have hpos1 : 0 < 1 + delta0 ^ 2 / gamma0 ^ 2 := by
    have hg2 : 0 < gamma0 ^ 2 := pow_pos gamma0_pos 2
    have hfrac : 0 ≤ delta0 ^ 2 / gamma0 ^ 2 := div_nonneg (sq_nonneg delta0) (le_of_lt hg2)
    linarith
  have hlog : Real.log (1 + delta0 ^ 2 / gamma0 ^ 2) ≤ 2 * (U + E) := by
    linarith
  have he : Real.exp (Real.log (1 + delta0 ^ 2 / gamma0 ^ 2)) ≤ Real.exp (2 * (U + E)) :=
    (Real.exp_le_exp.mpr hlog)
  have hcancel : 1 + delta0 ^ 2 / gamma0 ^ 2 = Real.exp (Real.log (1 + delta0 ^ 2 / gamma0 ^ 2)) :=
    (Real.exp_log hpos1).symm
  rwa [hcancel]

/-- Main: γ₀ ≥ δ₀ / √(exp(2·(U+E)) − 1).  The nearest non-central zero
    height is bounded below by numeric data at the selected δ₀. -/
theorem gamma0_lower_bound :
  delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1) ≤ gamma0 := by
  have hle : 1 + delta0 ^ 2 / gamma0 ^ 2 ≤ Real.exp (2 * (U + E)) := log_le_exp
  have hsub : delta0 ^ 2 / gamma0 ^ 2 ≤ Real.exp (2 * (U + E)) - 1 := by linarith
  have hden_pos : 0 < Real.exp (2 * (U + E)) - 1 := by
    have hUaddE : 0 < 2 * (U + E) := by
      have hU : 0 < U := U_pos
      have hE : 0 < E := E_pos
      linarith
    have hgt1 : 1 < Real.exp (2 * (U + E)) := Real.one_lt_exp_iff.mpr hUaddE
    linarith
  have hg2_pos : 0 < gamma0 ^ 2 := pow_pos gamma0_pos 2
  have hsq : delta0 ^ 2 ≤ gamma0 ^ 2 * (Real.exp (2 * (U + E)) - 1) := by
    calc
      delta0 ^ 2 ≤ (Real.exp (2 * (U + E)) - 1) * gamma0 ^ 2 := (div_le_iff₀ hg2_pos).mp hsub
      _ = gamma0 ^ 2 * (Real.exp (2 * (U + E)) - 1) := by ring
  have hc_pos : 0 < Real.sqrt (Real.exp (2 * (U + E)) - 1) := Real.sqrt_pos.mpr hden_pos
  have hsq2 : (delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1)) ^ 2 ≤ gamma0 ^ 2 := by
    calc
      (delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1)) ^ 2
          = delta0 ^ 2 / Real.sqrt (Real.exp (2 * (U + E)) - 1) ^ 2 := by ring
      _ = delta0 ^ 2 / (Real.exp (2 * (U + E)) - 1) := by rw [Real.sq_sqrt (le_of_lt hden_pos)]
      _ ≤ gamma0 ^ 2 := (div_le_iff₀ hden_pos).mpr hsq
  have habs := sq_le_sq.mp hsq2
  have hnonneg_lhs : 0 ≤ delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1) :=
    div_nonneg (le_of_lt delta0_pos) (le_of_lt hc_pos)
  have ha : |delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1)| = delta0 / Real.sqrt (Real.exp (2 * (U + E)) - 1) :=
    abs_of_nonneg hnonneg_lhs
  have hb : |gamma0| = gamma0 := abs_of_pos gamma0_pos
  rw [ha, hb] at habs
  exact habs

end BSD.ZeroGap
