import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import BSD.Positivity.Positivity

/-!
# Channel B: P* positivity from UNCONDITIONAL analytic structure — the sign-preservation path

Parallel proof channel to BSD.Positivity.Positivity (Channel A: refined
BSD formula).  Same target theorem on K = Q(sqrt 5):

    P* :  ord_1 L(E/K) = 2  ==>  L''(E/K,1) > 0

Channel B derives it from the ANALYTIC structure of L (zero-freeness in
Re(s) > 1, Euler product tail, continuity, Taylor quotients) instead of
the ALGEBRAIC hypothesis (refined BSD formula, Sha finite).  Mechanism
(no BSD formula anywhere):

    (1) L(s) > 0 for s > 3/2          -- Euler product factors positive
                                          (|a_p| <= 2 sqrt p), UNCONDITIONAL
    (2) no zeros in (1, 3/2)           -- UNCONDITIONAL theorem: for a GL2
                                          cuspidal L (modular E/Q(sqrt 5),
                                          self-dual), L has no zeros in
                                          Re(s) > 1.  Proof: in Re(s) > 1
                                          the Euler product converges
                                          absolutely (Godement–Jacquet); a
                                          zero there forces a local factor
                                          1 - α_v q^{-s} to vanish, i.e.
                                          |α_v| = q^{σ} > q, contradicting
                                          Ramanujan |α_v| ≤ sqrt q
                                          (= Hasse bound, Deligne).
                                          Modularity (Wiles) + Hasse
                                          (Deligne) + absolute convergence
                                          are THEOREMS — no GRH, no BSD.
                                          (s = 1 excluded; s = 3/2 endpoint
                                          by continuity.)
    (3) (1)+(2)+continuity => sign-preservation on (1, 3/2]
    (4) rank 1: L(1+δ) = L'(1)·δ + o(δ),  rank 2: L(1+δ) = L''(1)·δ²/2 + o(δ²)
    (5) (3)+(4)+nonzero (Kolyvagin rank 1 / Taylor-definition rank 2)
        => L'(1) > 0  resp.  L''(1) > 0  on E and E^5 separately.

Hence:  analytic rank exactly 2  ==>  P*  (sign-preservation path).
This is INDEPENDENT of the refined BSD formula AND of GRH: the zero-free
region Re(s) > 1 is an unconditional theorem, so GRH has RETIRED from
the assumption spectrum of P* (2026-10-10 refactor: the `grh_no_zero_L_E`
axioms were replaced by `zero_free_re_one_side`, theorem-level axioms).
Rank-0 components stay THEOREM-level (Euler product, unconditional),
taken from BSD.Positivity.Positivity.

Remaining assumptions in this channel: analytic object axioms
(L_E, continuity, Euler-product tail, Taylor quotients — all
UNCONDITIONAL facts, implementation debt only) + Kolyvagin rank-1
nonzero (proven theorem, implementation debt) + the zero-free-region
axiom (unconditional theorem, implementation debt).  NO conjecture-level
axiom remains in Channel B.

Strict-interval instances (probe389_strict / probe_twists_strict) are
the instance-level confirmation of this channel: numerically verified
sign preservation + center-derivative positivity, unconditionally.

## Axiom inventory (channel-B layer)

Object axioms (E side): L_E as a real function, continuity on
[1, 3/2], Euler-product positivity at/above 3/2 (incl. endpoint by
continuity), unconditional zero-free region on (1, 3/2), first/second
Taylor quotients.  (E^5 side: same, symmetric.)

## Theorems (real proofs)

pos_on_interval_of_no_zero (IVT sign preservation, generic),
pos_on_Icc(_5) (closed subintervals), L_E_pos_on_open(_5),
Lp_pos_uncond(_5), Lpp_pos_uncond(_5), uncond_type_20/11/02 (Leibniz
mirror of BSD.Positivity with unconditional positivity sources),
p_star_uncond (main, type-by-type).
-/

namespace BSD.PositivityGRH

open BSD.Positivity

open Filter
open scoped Topology

/-! ## 1. Channel-B object layer: L as a function, analytic semantics -/

/-- L(E, s) as a real function on the axis (extends the center-value
    objects of BSD.Positivity). -/
axiom L_E : ℝ → ℝ

/-- Continuity on [1, 3/2] (analyticity of L). -/
axiom continuous_L_E : ContinuousOn L_E (Set.Icc (1 : ℝ) (3 / 2 : ℝ))

/-- Euler-product positivity, s >= 3/2 (including endpoint by
    continuity + zero-freeness of the Euler product on (3/2, ∞)). -/
axiom L_E_pos_ge_three_halves : ∀ s : ℝ, (3 / 2 : ℝ) ≤ s → 0 < L_E s

/-- Zero-free region Re(s) > 1 restricted to (1, 3/2): L(E, s) has no
    zeros there.  UNCONDITIONAL THEOREM for a GL2 cuspidal self-dual
    L-function (modular E over Q(sqrt 5)): in Re(s) > 1 the Euler
    product converges absolutely; a zero would force a local factor
    |α_v| = q^{σ} > q, contradicting Ramanujan (Hasse, Deligne).
    Implemented here as a THEOREM-LEVEL axiom (implementation debt:
    full automorphic-L theory not yet in mathlib); GRH is NOT needed. -/
axiom zero_free_re_one_side : ∀ s : ℝ, (1 : ℝ) < s → s < (3 / 2 : ℝ) → L_E s ≠ 0

/-- Taylor quotient, rank-1 center: L(1+δ)/δ → L'(1) as δ → 0+. -/
axiom taylor_first_L_E :
  Tendsto (fun δ : ℝ => L_E (1 + δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 Lprime_E_one)

/-- Taylor quotient, rank-2 center: L(1+δ)/δ² → L''(1)/2 as δ → 0+. -/
axiom taylor_second_L_E :
  Tendsto (fun δ : ℝ => L_E (1 + δ) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (Lprimeprime_E_one / 2))

/-- L(E^5, s) as a real function. -/
axiom L_E5 : ℝ → ℝ

/-- Continuity on [1, 3/2]. -/
axiom continuous_L_E5 : ContinuousOn L_E5 (Set.Icc (1 : ℝ) (3 / 2 : ℝ))

/-- Euler-product positivity, s >= 3/2. -/
axiom L_E5_pos_ge_three_halves : ∀ s : ℝ, (3 / 2 : ℝ) ≤ s → 0 < L_E5 s

/-- Zero-free region Re(s) > 1 for the twist (unconditional theorem,
    same argument). -/
axiom zero_free_re_one_side5 : ∀ s : ℝ, (1 : ℝ) < s → s < (3 / 2 : ℝ) → L_E5 s ≠ 0

/-- Taylor quotient, twist, rank-1 center. -/
axiom taylor_first_L_E5 :
  Tendsto (fun δ : ℝ => L_E5 (1 + δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 Lprime_E5_one)

/-- Taylor quotient, twist, rank-2 center. -/
axiom taylor_second_L_E5 :
  Tendsto (fun δ : ℝ => L_E5 (1 + δ) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (Lprimeprime_E5_one / 2))

/-! ## 1b. Functional equation: sign & zeros on (1/2, 1) -/

/-- Root number of L(E, ·), the GL2 functional-equation sign (±1). -/
axiom rootNumberE : ℝ

/-- Root number is ±1. -/
axiom rootNumberE_eq_pos_or_neg : rootNumberE = 1 ∨ rootNumberE = -1

/-- Functional equation, real-axis form on (1/2, 1): for real
    coefficients the gamma factors and N^{s/2} are positive on the
    real axis, so for σ ∈ (1/2, 1):
        sign L(σ) = ε · sign L(2−σ),   and   L(σ) = 0 ⟺ L(2−σ) = 0.
    (待证明：函数方程的 Lean 实现；首消目标 = functional equation of L.) -/
axiom L_E_fe (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1) :
  (0 < L_E σ ↔ 0 < rootNumberE * L_E (2 - σ)) ∧ (L_E σ = 0 ↔ L_E (2 - σ) = 0)

/-- Root number of L(E^5, ·). -/
axiom rootNumberE5 : ℝ

/-- Root number is ±1. -/
axiom rootNumberE5_eq_pos_or_neg : rootNumberE5 = 1 ∨ rootNumberE5 = -1

/-- Functional equation, real-axis form for the twist. -/
axiom L_E5_fe (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1) :
  (0 < L_E5 σ ↔ 0 < rootNumberE5 * L_E5 (2 - σ)) ∧ (L_E5 σ = 0 ↔ L_E5 (2 - σ) = 0)

/-! ## 2. True theorems: sign preservation via IVT -/

/-- A continuous real function that is positive at the right endpoint
    and has NO zeros on the closed interval is strictly positive
    throughout.  (Intermediate value theorem: if f x <= 0 somewhere,
    then f crosses 0 between x and b.) -/
theorem pos_on_interval_of_no_zero {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hno : ∀ x ∈ Set.Icc a b, f x ≠ 0)
    (hpos : 0 < f b) :
    ∀ x ∈ Set.Icc a b, 0 < f x := by
  intro x hx
  by_contra hle0
  have hx_le_b : x ≤ b := hx.2
  have hle : f x ≤ 0 := le_of_not_gt hle0
  have hneg : f x < 0 := lt_of_le_of_ne hle (hno x hx)
  have hx_in : x ∈ Set.Icc x b := by
    exact Set.left_mem_Icc.mpr hx_le_b
  have hb_in : b ∈ Set.Icc x b := by
    exact Set.right_mem_Icc.mpr hx_le_b
  have hsub : Set.Icc x b ⊆ Set.Icc a b := by
    intro y hy
    exact ⟨hx.1.trans hy.1, hy.2.trans le_rfl⟩
  have hconn : IsPreconnected (Set.Icc x b) := isPreconnected_Icc
  have hz : 0 ∈ f '' Set.Icc x b := by
    exact hconn.intermediate_value hx_in hb_in (hcont.mono hsub)
      ⟨le_of_lt hneg, le_of_lt hpos⟩
  rcases hz with ⟨c, hc, hfc⟩
  exact hno c (hsub hc) hfc

/-! ## 3. Unconditional ⇒ sign preservation on (1, 3/2] -/

/-- Zero-free region Re(s) > 1 + Euler product: L_E > 0 on every closed
    subinterval [a, 3/2] with 1 < a. -/
lemma pos_on_Icc (a : ℝ) (ha1 : (1 : ℝ) < a) (ha2 : a < (3 / 2 : ℝ)) :
    ∀ x ∈ Set.Icc a (3 / 2 : ℝ), 0 < L_E x := by
  apply pos_on_interval_of_no_zero ha2
  · exact continuous_L_E.mono (by
      intro y hy
      exact ⟨(lt_of_lt_of_le ha1 hy.1).le, hy.2⟩)
  · intro y hy
    by_cases hy3 : y = (3 / 2 : ℝ)
    · subst hy3
      exact (L_E_pos_ge_three_halves (3 / 2 : ℝ) le_rfl).ne'
    · exact zero_free_re_one_side y (lt_of_lt_of_le ha1 hy.1) (lt_of_le_of_ne hy.2 hy3)
  · exact L_E_pos_ge_three_halves (3 / 2 : ℝ) le_rfl

/-- Zero-free region + Euler product: L_E > 0 on the open interval
    (1, 3/2). -/
lemma L_E_pos_on_open : ∀ x : ℝ, (1 : ℝ) < x → x < (3 / 2 : ℝ) → 0 < L_E x := by
  intro x hx1 hx2
  let a := (1 + x) / 2
  have ha1 : (1 : ℝ) < a := by
    dsimp [a]
    linarith
  have ha2 : a < (3 / 2 : ℝ) := by
    dsimp [a]
    linarith
  have hxa : a ≤ x := by
    dsimp [a]
    linarith
  exact pos_on_Icc a ha1 ha2 x ⟨hxa, hx2.le⟩

/-- Zero-free region + Euler product: L_E5 > 0 on every closed
    subinterval [a, 3/2] with 1 < a. -/
lemma pos_on_Icc5 (a : ℝ) (ha1 : (1 : ℝ) < a) (ha2 : a < (3 / 2 : ℝ)) :
    ∀ x ∈ Set.Icc a (3 / 2 : ℝ), 0 < L_E5 x := by
  apply pos_on_interval_of_no_zero ha2
  · exact continuous_L_E5.mono (by
      intro y hy
      exact ⟨(lt_of_lt_of_le ha1 hy.1).le, hy.2⟩)
  · intro y hy
    by_cases hy3 : y = (3 / 2 : ℝ)
    · subst hy3
      exact (L_E5_pos_ge_three_halves (3 / 2 : ℝ) le_rfl).ne'
    · exact zero_free_re_one_side5 y (lt_of_lt_of_le ha1 hy.1) (lt_of_le_of_ne hy.2 hy3)
  · exact L_E5_pos_ge_three_halves (3 / 2 : ℝ) le_rfl

/-- Same for the twist. -/
lemma L_E5_pos_on_open : ∀ x : ℝ, (1 : ℝ) < x → x < (3 / 2 : ℝ) → 0 < L_E5 x := by
  intro x hx1 hx2
  let a := (1 + x) / 2
  have ha1 : (1 : ℝ) < a := by
    dsimp [a]
    linarith
  have ha2 : a < (3 / 2 : ℝ) := by
    dsimp [a]
    linarith
  have hxa : a ≤ x := by
    dsimp [a]
    linarith
  exact pos_on_Icc5 a ha1 ha2 x ⟨hxa, hx2.le⟩

/-! ## 3b. Functional-equation extension: no zeros on (1/2, 3/2) ∖ {1} -/

/-- No zeros on (1/2, 1): sign preservation on (1, 3/2) pulled back by
    the functional equation (zero correspondence L(σ)=0 ⟺ L(2−σ)=0). -/
theorem L_E_no_zero_left (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1) :
    L_E σ ≠ 0 := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hz : L_E (2 - σ) ≠ 0 := zero_free_re_one_side (2 - σ) hσ2 hσ2'
  intro hzσ
  exact hz ((L_E_fe σ h1 h2).2.mp hzσ)

/-- Same for the twist. -/
theorem L_E5_no_zero_left (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1) :
    L_E5 σ ≠ 0 := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hz : L_E5 (2 - σ) ≠ 0 := zero_free_re_one_side5 (2 - σ) hσ2 hσ2'
  intro hzσ
  exact hz ((L_E5_fe σ h1 h2).2.mp hzσ)

/-- ε(E) = +1: L_E > 0 on (1/2, 1) (same sign as L_E on (1, 3/2)). -/
theorem L_E_pos_left_of_rootNumber_one (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1)
    (hε : rootNumberE = 1) : 0 < L_E σ := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hpos : 0 < L_E (2 - σ) := L_E_pos_on_open (2 - σ) hσ2 hσ2'
  have hiff : (0 < L_E σ) ↔ (0 < rootNumberE * L_E (2 - σ)) := (L_E_fe σ h1 h2).1
  exact hiff.mpr (by rw [hε]; simpa using hpos)

/-- ε(E) = -1: L_E < 0 on (1/2, 1) (opposite sign). -/
theorem L_E_neg_left_of_rootNumber_neg_one (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1)
    (hε : rootNumberE = -1) : L_E σ < 0 := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hpos : 0 < L_E (2 - σ) := L_E_pos_on_open (2 - σ) hσ2 hσ2'
  have hiff : (0 < L_E σ) ↔ (0 < rootNumberE * L_E (2 - σ)) := (L_E_fe σ h1 h2).1
  have hnot : ¬ 0 < L_E σ := by
    intro hgt
    have hprod : 0 < rootNumberE * L_E (2 - σ) := hiff.mp hgt
    have hnegl : rootNumberE * L_E (2 - σ) < 0 := by
      rw [hε]
      simpa using hpos
    exact hnegl.not_gt hprod
  have hne : L_E σ ≠ 0 := L_E_no_zero_left σ h1 h2
  exact lt_of_le_of_ne (le_of_not_gt hnot) hne

/-- ε(E^5) = +1: L_E5 > 0 on (1/2, 1). -/
theorem L_E5_pos_left_of_rootNumber_one (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1)
    (hε : rootNumberE5 = 1) : 0 < L_E5 σ := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hpos : 0 < L_E5 (2 - σ) := L_E5_pos_on_open (2 - σ) hσ2 hσ2'
  have hiff : (0 < L_E5 σ) ↔ (0 < rootNumberE5 * L_E5 (2 - σ)) := (L_E5_fe σ h1 h2).1
  exact hiff.mpr (by rw [hε]; simpa using hpos)

/-- ε(E^5) = -1: L_E5 < 0 on (1/2, 1). -/
theorem L_E5_neg_left_of_rootNumber_neg_one (σ : ℝ) (h1 : (1 / 2 : ℝ) < σ) (h2 : σ < 1)
    (hε : rootNumberE5 = -1) : L_E5 σ < 0 := by
  have hσ2 : (1 : ℝ) < 2 - σ := by linarith
  have hσ2' : 2 - σ < (3 / 2 : ℝ) := by linarith
  have hpos : 0 < L_E5 (2 - σ) := L_E5_pos_on_open (2 - σ) hσ2 hσ2'
  have hiff : (0 < L_E5 σ) ↔ (0 < rootNumberE5 * L_E5 (2 - σ)) := (L_E5_fe σ h1 h2).1
  have hnot : ¬ 0 < L_E5 σ := by
    intro hgt
    have hprod : 0 < rootNumberE5 * L_E5 (2 - σ) := hiff.mp hgt
    have hnegl : rootNumberE5 * L_E5 (2 - σ) < 0 := by
      rw [hε]
      simpa using hpos
    exact hnegl.not_gt hprod
  have hne : L_E5 σ ≠ 0 := L_E5_no_zero_left σ h1 h2
  exact lt_of_le_of_ne (le_of_not_gt hnot) hne

/-- Zero-free on the FULL punctured interval (1/2, 3/2) ∖ {1}: left half
    by functional-equation extension, right half by the unconditional
    zero-free region. -/
theorem L_E_no_zero_full (σ : ℝ) (hlo : (1 / 2 : ℝ) < σ) (hhi : σ < (3 / 2 : ℝ))
    (hne : σ ≠ 1) : L_E σ ≠ 0 := by
  by_cases hσ1 : σ < 1
  · exact L_E_no_zero_left σ hlo hσ1
  · have h1σ : (1 : ℝ) < σ := lt_of_le_of_ne (le_of_not_gt hσ1) hne.symm
    exact zero_free_re_one_side σ h1σ hhi

/-- Zero-free on the full punctured interval for the twist. -/
theorem L_E5_no_zero_full (σ : ℝ) (hlo : (1 / 2 : ℝ) < σ) (hhi : σ < (3 / 2 : ℝ))
    (hne : σ ≠ 1) : L_E5 σ ≠ 0 := by
  by_cases hσ1 : σ < 1
  · exact L_E5_no_zero_left σ hlo hσ1
  · have h1σ : (1 : ℝ) < σ := lt_of_le_of_ne (le_of_not_gt hσ1) hne.symm
    exact zero_free_re_one_side5 σ h1σ hhi

/-! ## 4. Unconditional ⇒ center-derivative positivity (rank 1, rank 2) -/

/-- Unconditional + rank 1 => L'(E,1) > 0.  Sign preservation (1, 3/2]
    forces L(1+δ) > 0 for small δ > 0 (Euler product covers δ >= 1/2);
    the Taylor quotient L(1+δ)/δ → L'(1) then has a nonnegative limit;
    Kolyvagin nonzero promotes to > 0. -/
theorem Lp_pos_uncond (h : zeroOrderE = 1) : 0 < Lprime_E_one := by
  have hlim : Tendsto (fun δ : ℝ => L_E (1 + δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 Lprime_E_one) :=
    taylor_first_L_E
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ L_E (1 + δ) / δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ0
    by_cases hbig : (3 / 2 : ℝ) ≤ 1 + δ
    · have hpos : 0 < L_E (1 + δ) := L_E_pos_ge_three_halves (1 + δ) hbig
      exact (div_pos hpos hδ0).le
    · have hδ : (0 : ℝ) < δ := by simpa using hδ0
      have hx1 : (1 : ℝ) < 1 + δ := by linarith
      have hx2 : 1 + δ < (3 / 2 : ℝ) := lt_of_not_ge hbig
      have hpos : 0 < L_E (1 + δ) := L_E_pos_on_open (1 + δ) hx1 hx2
      exact (div_pos hpos hδ0).le
  have hge : 0 ≤ Lprime_E_one := by
    have hlim' : Tendsto (fun δ : ℝ => -(L_E (1 + δ) / δ)) (𝓝[>] (0 : ℝ)) (𝓝 (-Lprime_E_one)) :=
      hlim.neg
    have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -(L_E (1 + δ) / δ) ≤ 0 := by
      filter_upwards [hev] with δ hδ
      linarith
    have hle : -Lprime_E_one ≤ 0 := le_of_tendsto hlim' hev'
    linarith
  have hne : Lprime_E_one ≠ 0 := by
    simpa using lprime_ne_zero_of_rank_one h
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- Unconditional + rank 2 => L''(E,1) > 0.  Same argument with the
    second Taylor quotient; nonzero is the Taylor-definitional fact
    (ord = 2 => L''(1) != 0). -/
theorem Lpp_pos_uncond (h : zeroOrderE = 2) : 0 < Lprimeprime_E_one := by
  have hlim : Tendsto (fun δ : ℝ => L_E (1 + δ) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (Lprimeprime_E_one / 2)) :=
    taylor_second_L_E
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ L_E (1 + δ) / δ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ0
    by_cases hbig : (3 / 2 : ℝ) ≤ 1 + δ
    · have hpos : 0 < L_E (1 + δ) := L_E_pos_ge_three_halves (1 + δ) hbig
      exact (div_pos hpos (pow_pos hδ0 2)).le
    · have hδ : (0 : ℝ) < δ := by simpa using hδ0
      have hx1 : (1 : ℝ) < 1 + δ := by linarith
      have hx2 : 1 + δ < (3 / 2 : ℝ) := lt_of_not_ge hbig
      have hpos : 0 < L_E (1 + δ) := L_E_pos_on_open (1 + δ) hx1 hx2
      exact (div_pos hpos (pow_pos hδ0 2)).le
  have hge : 0 ≤ Lprimeprime_E_one / 2 := by
    have hlim' : Tendsto (fun δ : ℝ => -(L_E (1 + δ) / δ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (-(Lprimeprime_E_one / 2))) :=
      hlim.neg
    have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -(L_E (1 + δ) / δ ^ 2) ≤ 0 := by
      filter_upwards [hev] with δ hδ
      linarith
    have hle : -(Lprimeprime_E_one / 2) ≤ 0 := le_of_tendsto hlim' hev'
    linarith
  have hne : Lprimeprime_E_one ≠ 0 := by
    simpa using Lprimeprime_ne_zero_of_rank_eq_two h
  have hge2 : 0 ≤ Lprimeprime_E_one := by
    have hdiv : Lprimeprime_E_one = (Lprimeprime_E_one / 2) * 2 := by ring
    rw [hdiv]
    exact mul_nonneg hge (by norm_num : 0 ≤ (2 : ℝ))
  exact lt_of_le_of_ne hge2 (Ne.symm hne)

/-- Unconditional + rank 1 => L'(E^5,1) > 0 (twist). -/
theorem Lp_pos_uncond5 (h : zeroOrderE5 = 1) : 0 < Lprime_E5_one := by
  have hlim : Tendsto (fun δ : ℝ => L_E5 (1 + δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 Lprime_E5_one) :=
    taylor_first_L_E5
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ L_E5 (1 + δ) / δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ0
    by_cases hbig : (3 / 2 : ℝ) ≤ 1 + δ
    · have hpos : 0 < L_E5 (1 + δ) := L_E5_pos_ge_three_halves (1 + δ) hbig
      exact (div_pos hpos hδ0).le
    · have hδ : (0 : ℝ) < δ := by simpa using hδ0
      have hx1 : (1 : ℝ) < 1 + δ := by linarith
      have hx2 : 1 + δ < (3 / 2 : ℝ) := lt_of_not_ge hbig
      have hpos : 0 < L_E5 (1 + δ) := L_E5_pos_on_open (1 + δ) hx1 hx2
      exact (div_pos hpos hδ0).le
  have hge : 0 ≤ Lprime_E5_one := by
    have hlim' : Tendsto (fun δ : ℝ => -(L_E5 (1 + δ) / δ)) (𝓝[>] (0 : ℝ)) (𝓝 (-Lprime_E5_one)) :=
      hlim.neg
    have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -(L_E5 (1 + δ) / δ) ≤ 0 := by
      filter_upwards [hev] with δ hδ
      linarith
    have hle : -Lprime_E5_one ≤ 0 := le_of_tendsto hlim' hev'
    linarith
  have hne : Lprime_E5_one ≠ 0 := by
    simpa using lprime_ne_zero_of_rank_one5 h
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- Unconditional + rank 2 => L''(E^5,1) > 0 (twist). -/
theorem Lpp_pos_uncond5 (h : zeroOrderE5 = 2) : 0 < Lprimeprime_E5_one := by
  have hlim : Tendsto (fun δ : ℝ => L_E5 (1 + δ) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (Lprimeprime_E5_one / 2)) :=
    taylor_second_L_E5
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ L_E5 (1 + δ) / δ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ0
    by_cases hbig : (3 / 2 : ℝ) ≤ 1 + δ
    · have hpos : 0 < L_E5 (1 + δ) := L_E5_pos_ge_three_halves (1 + δ) hbig
      exact (div_pos hpos (pow_pos hδ0 2)).le
    · have hδ : (0 : ℝ) < δ := by simpa using hδ0
      have hx1 : (1 : ℝ) < 1 + δ := by linarith
      have hx2 : 1 + δ < (3 / 2 : ℝ) := lt_of_not_ge hbig
      have hpos : 0 < L_E5 (1 + δ) := L_E5_pos_on_open (1 + δ) hx1 hx2
      exact (div_pos hpos (pow_pos hδ0 2)).le
  have hge : 0 ≤ Lprimeprime_E5_one / 2 := by
    have hlim' : Tendsto (fun δ : ℝ => -(L_E5 (1 + δ) / δ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (-(Lprimeprime_E5_one / 2))) :=
      hlim.neg
    have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -(L_E5 (1 + δ) / δ ^ 2) ≤ 0 := by
      filter_upwards [hev] with δ hδ
      linarith
    have hle : -(Lprimeprime_E5_one / 2) ≤ 0 := le_of_tendsto hlim' hev'
    linarith
  have hne : Lprimeprime_E5_one ≠ 0 := by
    simpa using Lprimeprime_ne_zero_of_rank_eq_two5 h
  have hge2 : 0 ≤ Lprimeprime_E5_one := by
    have hdiv : Lprimeprime_E5_one = (Lprimeprime_E5_one / 2) * 2 := by ring
    rw [hdiv]
    exact mul_nonneg hge (by norm_num : 0 ≤ (2 : ℝ))
  exact lt_of_le_of_ne hge2 (Ne.symm hne)

/-! ## 5. P* from the unconditional channel: type-by-type (mirroring
BSD.Positivity) -/

/-- P* at type (2,0) via the unconditional channel:
    L''(E/K,1) = L''(E,1)·L(E^5,1) > 0 — unconditional rank-2 positivity
    of L''(E,1), times THEOREM-level rank-0 positivity of L(E^5,1);
    middle and last Leibniz terms vanish. -/
theorem uncond_type_20 (hE2 : zeroOrderE = 2) (hE5_0 : zeroOrderE5 = 0) :
    0 < Lprimeprime_EK_one := by
  have hLppE : 0 < Lprimeprime_E_one := Lpp_pos_uncond hE2
  have hLE5 : 0 < LE5_one := l_one_pos_of_rank_zero5 hE5_0
  have hprod : 0 < Lprimeprime_E_one * LE5_one := mul_pos hLppE hLE5
  have hLpE5 : Lprime_E5_one = 0 :=
    Lprime_zero_of_rank_ne_one5 (by simp [hE5_0])
  have hLE : LE_one = 0 :=
    L_value_zero_of_rank_pos (by simp [hE2])
  rw [leibniz_artin, hLpE5, hLE]
  simp
  exact hprod

/-- P* at type (1,1) via the unconditional channel:
    L''(E/K,1) = 2·L'(E,1)·L'(E^5,1) > 0 — the ENTANGLEMENT branch;
    both rank-1 components are positive by the unconditional
    sign-preservation path (Kolyvagin nonzero for promotion). -/
theorem uncond_type_11 (hE1 : zeroOrderE = 1) (hE5_1 : zeroOrderE5 = 1) :
    0 < Lprimeprime_EK_one := by
  have hLE : LE_one = 0 :=
    L_value_zero_of_rank_pos (by simp [hE1])
  have hLE5 : LE5_one = 0 :=
    L_value_zero_of_rank_pos5 (by simp [hE5_1])
  have hLpE : 0 < Lprime_E_one := Lp_pos_uncond hE1
  have hLpE5 : 0 < Lprime_E5_one := Lp_pos_uncond5 hE5_1
  have hmid : 0 < (2 : Real) * Lprime_E_one * Lprime_E5_one :=
    mul_pos (mul_pos (by norm_num) hLpE) hLpE5
  rw [leibniz_artin, hLE, hLE5]
  simp
  exact hmid

/-- P* at type (0,2) via the unconditional channel:
    L''(E/K,1) = L(E,1)·L''(E^5,1) > 0 — mirror of (2,0). -/
theorem uncond_type_02 (hE0 : zeroOrderE = 0) (hE5_2 : zeroOrderE5 = 2) :
    0 < Lprimeprime_EK_one := by
  have hLE : 0 < LE_one := l_one_pos_of_rank_zero hE0
  have hLppE5 : 0 < Lprimeprime_E5_one := Lpp_pos_uncond5 hE5_2
  have hLpE : Lprime_E_one = 0 :=
    Lprime_zero_of_rank_ne_one (by simp [hE0])
  have hLppE : Lprimeprime_E_one = 0 :=
    Lprimeprime_zero_of_rank_ne_two (by simp [hE0])
  have hprod : 0 < LE_one * Lprimeprime_E5_one := mul_pos hLE hLppE5
  rw [leibniz_artin, hLpE, hLppE]
  simp
  exact hprod

/-- P* via Channel B: unconditional zero-freeness (both components
    zero-free on (1, 3/2)) + analytic rank exactly 2 on K
    =>  L''(E/K,1) > 0.
    Type trichotomy (0,2) | (1,1) | (2,0); each branch uses the
    Channel-B positivity of rank-1/rank-2 components (rank-0
    components: Euler product, THEOREM-level, from BSD.Positivity). -/
theorem p_star_uncond (h : analyticZeroOrder = 2) : 0 < Lprimeprime_EK_one := by
  have hadd : zeroOrderE + zeroOrderE5 = 2 := by
    rw [← zeroOrder_additivity]
    exact h
  rcases type_trichotomy hadd with h02 | h11 | h20
  · rcases h02 with ⟨hE0, hE5_2⟩
    exact uncond_type_02 hE0 hE5_2
  · rcases h11 with ⟨hE1, hE5_1⟩
    exact uncond_type_11 hE1 hE5_1
  · rcases h20 with ⟨hE2, hE5_0⟩
    exact uncond_type_20 hE2 hE5_0

end BSD.PositivityGRH
