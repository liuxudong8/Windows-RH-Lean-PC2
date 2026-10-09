import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum

/-!
# P*: positivity of L''(E/K,1) at analytic rank exactly 2

Third-stage Lean skeleton (K = Q(sqrt 5), Artin decomposition
L(E/K) = L(E)·L(E^5)).  The theorem laid down here is the DEFENSIBLE
version of the user's original question "is L'' bounded below for
every rank >= 2 curve on K?" — that phrasing is FALSE (rank 3 and
rank >= 4 configurations give L''(E/K,1) = 0), so the skeleton proves:

    P* :  ord_1 L(E/K) = 2  ==>  L''(E/K,1) > 0.

## Recon result (Positivity/positivity_recon_summary.md, 2026-10-08)

(1,1)-type existence decided numerically + Cremona allbsd:
- 389a1 (N = 389, rank 2, eps = +1): E^5 has rank 0
  (L(E^5,1) = 8.909 != 0)  =>  type (2,0) on K;
  L''(E/K,1) = 1.518633000576854 * 8.909 ~ 13.53 > 0 (trivial product).
- (1,1) is REALIZED: 6/6 rank-1 curves with N ≡ ±1 (mod 5) have E^5 of
  rank 1 (79a1, 89a1, 91a1, 99a1, 101a1, 106b1); the entanglement product
  L'(E,1)·L'(E^5,1) > 0 in all six (empirical law, 6 data points).
- Root number eps(E^5) = eps(E)*chi_5(N) only pins PARITY; it pins the
  (1,1) candidates to rank-1 curves with N ≡ ±1 (mod 5) — a NONEMPTY
  family.  (1,1) cannot be excluded by parity.

## Logical status of P* (the boundary answer)

Leibniz on the Artin decomposition:

    L''(E/K,1) = L''(E,1)·L(E^5,1) + 2·L'(E,1)·L'(E^5,1) + L(E,1)·L''(E^5,1)

Three types (ord_1 L(E), ord_1 L(E^5)):
    (2,0):  L''(E,1)·L(E^5,1)   — rank-2 positivity × rank-0 L(1) > 0
    (1,1):  2·L'(E,1)·L'(E^5,1) — ENTANGLEMENT, two rank-1 positivities
    (0,2):  L(E,1)·L''(E^5,1)   — mirror of (2,0)

The only non-trivial content is the (1,1) entanglement, and it is
EXACTLY rank-1 BSD positivity (L'(1) = Omega·R·Sha/T^2 > 0).  Hence:

    P*  <=>  componentwise BSD positivity
      (rank-0 component: THEOREM (Kolyvagin–Logachev, Gross–Zagier-era
        BSD rank 0);  rank-1/rank-2 components: refined-BSD formula
        axioms + positivity THEOREMS — see "The rank-2 leg" below)

P* is therefore a RESTATEMENT of BSD positivity, not an independent
provable theorem.  This skeleton makes that precise: the axioms below
ARE the componentwise BSD positivity; the theorems derive P* from them
type by type; the data layer records the two realized types.

## Axiom inventory

Object layer (45 axioms) — "any elliptic curve E over Q with 5-twist
E^5, K = Q(sqrt 5), ord_1 L(E/K) = ord_1 L(E) + ord_1 L(E^5)":

| axiom | meaning | upgrade path |
|---|---|---|
| LE_one ... LppEK_one (8) | center values & derivatives | L-function layer |
| zeroOrderE / zeroOrderE5 / analyticZeroOrder | zero orders | same |
| zeroOrder_additivity | Artin decomposition | Artin / functoriality |
| leibniz_artin | L''(E/K) = Leibniz product | Taylor + product rule |
| L_value_zero_of_rank_pos(_5) | ord >= 1 => L(1) = 0 | analyticity + Taylor |
| Lprime_zero_of_rank_ne_one(_5) | ord != 1 => L'(1) = 0 | same |
| Lprimeprime_zero_of_rank_ne_two(_5) | ord != 2 => L''(1) = 0 | same |
| Lprimeprime_ne_zero_of_rank_eq_two(_5) | ord = 2 => L''(1) != 0 | DEFINITIONAL (Taylor converse; no Kolyvagin needed) |
| l_one_pos_of_rank_zero(_5) | rank 0 => L(1) > 0 | THEOREM (BSD rank 0) |
| lprime_ne_zero_of_rank_one(_5) | rank 1 => L'(1) != 0 | THEOREM (Kolyvagin–Gross–Zagier) |
| OmegaE, RegulatorE, ShaE, TorsionSizeE (+ positivity) | BSD data, factors all known positive | THEOREM / trivial |
| bsd_formula_rank_one | L'(1) = Omega·R·Sha/|T|^2 | CONJECTURE (Sha finiteness) — the ONLY rank-1 sign obstacle |
| lprime_pos_of_rank_one (theorem) | rank 1 => L'(1) > 0 | derived: formula + factor positivity |
| OmegaE5, RegulatorE5, ShaE5, TorsionSizeE5 (+ positivity) | twist-side BSD data | THEOREM / trivial |
| bsd_formula_rank_one5 | L'(E^5,1) = Omega·R·Sha/|T|^2 | CONJECTURE (Sha finiteness), symmetric |
| lprime_pos_of_rank_one5 (theorem) | twist-side rank 1 => L'(1) > 0 | derived: formula + factor positivity |
| Regulator2E(_5) (+ positivity) | rank-2 2x2 height-matrix determinant | THEOREM (positive-definite Gram det) |
| bsd_formula_rank_two(_5) | L''(1) = 2·Omega·R2·Sha/|T|^2 | CONJECTURE (Sha finiteness) — the ONLY rank-2 sign obstacle |
| lprimeprime_pos_of_rank_two(_5) (theorem) | rank 2 => L''(1) > 0 | derived: formula + factor positivity |
| LppEK_zero_of_rank_ge_three | ord >= 3 => L''(E/K,1) = 0 | Taylor (P* domain cutoff) |

Data layer (17 axioms) — realized types from the recon + strict
interval verification of the (1,1) entanglement (6/6):
389a1 -> (2,0); 106b1 -> (1,1) + entanglement positivity.

## Theorems (real proofs)

type_trichotomy, p_star_type_20, p_star_type_11, p_star_type_02,
p_star (main), rank_ge_three_implies_Lpp_zero, pos_implies_ne_zero,
lprime_pos_of_rank_one, lprime_pos_of_rank_one5 (derived from the
formulas, no longer axioms),
lprimeprime_pos_of_rank_two, lprimeprime_pos_of_rank_two5 (rank-2
2x2-regulator formulas, no longer axioms),
entanglement_positive_iff_same_sign,
probe389_type_is_2_0, probe106_type_is_1_1, one_one_type_realized.

## The entanglement boundary (the answer to "can the axiom be
   downgraded to a partial theorem?")

(1,1)-branch positivity is the product L'(E)·L'(E^5) > 0.  What can be
downgraded, and what cannot:

1. NONZERO is a theorem (Kolyvagin–Gross–Zagier): rank 1 forces
   L'(1) != 0 — `lprime_ne_zero_of_rank_one(_5)`.  This is the exact
   content of the "Kolyvagin upper-bound constraint": it gives
   nonvanishing, never a sign.
2. SIGN is not an independent conjecture: in the refined BSD formula
   L'(1) = Omega·R·Sha/|T|^2 every factor on the right is already
   positive by theorem/triviality (Omega, Regulator, Sha > 0, |T|^2 > 0).
   Hence "L'(1) > 0" reduces ENTIRELY to the formula itself
   (equivalently: Sha finite) — `bsd_formula_rank_one(_5)` are the only
   rank-1 positivity obstacles, and `lprime_pos_of_rank_one(_5)` are
   theorems from them.
3. The entanglement product carries NO extra information:
   `entanglement_positive_iff_same_sign` — the product is positive iff
   the two components have the same sign; the common sign must come
   from the two component positivities.  No "special situation"
   (E^5 rank 1 + Kolyvagin bound) shortcuts the common-sign step.
   Empirical status: the recon measured 6/6 positive products
   (79a1, 89a1, 91a1, 99a1, 101a1, 106b1) — a data law, not a theorem.

## The rank-2 leg (this round: same decomposition pushed to rank 2)

The (2,0) / (0,2) branches of P* use the rank-2 component positivity.
Identical downgrade structure: the rank-2 refined BSD leading
coefficient is L''(1)/2 = Omega·R2·Sha/|T|^2, i.e.

    L''(E,1) = 2·Omega·R2·Sha/|T|^2

where R2 is the 2x2 Neron–Tate height-matrix DETERMINANT.  Its
positivity is theorem-level (positive-definite Gram determinant of two
linearly independent generators), so — exactly as in rank 1 — the
only rank-2 positivity obstacle is the formula itself (Sha
finiteness): `bsd_formula_rank_two(_5)` are the single remaining
conjectures, and `lprimeprime_pos_of_rank_two(_5)` are theorems from
them.  With this round, ALL componentwise BSD positivity used by P* is
downgraded: rank-0 = theorem, rank-1 = formula axiom + theorem
positivity, rank-2 = formula axiom + theorem positivity.  The entire
conjectural content of P* now sits in exactly four axioms:
`bsd_formula_rank_one`, `bsd_formula_rank_one5`,
`bsd_formula_rank_two`, `bsd_formula_rank_two5` — all four are the
same statement, refined BSD (Sha finiteness), at the four component
ranks of the two curves.
-/

namespace BSD.Positivity

/-! ## 1. Object layer: L-values, derivatives, zero orders (axioms) -/

/-- Center value L(E,1) of E/Q. -/
axiom LE_one : Real

/-- Center value L(E^5,1) of the 5-twist. -/
axiom LE5_one : Real

/-- Center value L(E/K,1). -/
axiom LEK_one : Real

/-- First derivative at the center, L'(E,1). -/
axiom Lprime_E_one : Real

/-- First derivative at the center, L'(E^5,1). -/
axiom Lprime_E5_one : Real

/-- Second derivative at the center, L''(E,1). -/
axiom Lprimeprime_E_one : Real

/-- Second derivative at the center, L''(E^5,1). -/
axiom Lprimeprime_E5_one : Real

/-- Second derivative at the center, L''(E/K,1) — the P* object. -/
axiom Lprimeprime_EK_one : Real

/-- ord_1 L(E, s): order of vanishing at s = 1. -/
axiom zeroOrderE : Nat

/-- ord_1 L(E^5, s). -/
axiom zeroOrderE5 : Nat

/-- ord_1 L(E/K, s) — the analytic rank of E over K. -/
axiom analyticZeroOrder : Nat

/-- Artin decomposition over K = Q(sqrt 5):
    ord_1 L(E/K) = ord_1 L(E) + ord_1 L(E^5). -/
axiom zeroOrder_additivity : analyticZeroOrder = zeroOrderE + zeroOrderE5

/-- Leibniz rule on the Artin decomposition:
    L''(E/K,1) = L''(E,1)·L(E^5,1) + 2·L'(E,1)·L'(E^5,1) + L(E,1)·L''(E^5,1).
    (L(E/K) = L(E)·L(E^5) on the analytic side; second derivative of a
    product.) -/
axiom leibniz_artin :
  Lprimeprime_EK_one =
    Lprimeprime_E_one * LE5_one + (2 : Real) * Lprime_E_one * Lprime_E5_one +
      LE_one * Lprimeprime_E5_one

/-- Taylor structure: ord >= 1 forces the center value to vanish. -/
axiom L_value_zero_of_rank_pos : 1 <= zeroOrderE -> LE_one = 0

/-- Taylor structure on the twist: ord >= 1 forces L(E^5,1) = 0. -/
axiom L_value_zero_of_rank_pos5 : 1 <= zeroOrderE5 -> LE5_one = 0

/-- Taylor structure: ord != 1 forces the first derivative to vanish
    (a nonzero L'(1) is exactly what rank 1 means). -/
axiom Lprime_zero_of_rank_ne_one : zeroOrderE != 1 -> Lprime_E_one = 0

/-- Taylor structure on the twist, first derivative. -/
axiom Lprime_zero_of_rank_ne_one5 : zeroOrderE5 != 1 -> Lprime_E5_one = 0

/-- Taylor structure: ord != 2 forces the second derivative to vanish. -/
axiom Lprimeprime_zero_of_rank_ne_two : zeroOrderE != 2 -> Lprimeprime_E_one = 0

/-- Taylor structure on the twist, second derivative. -/
axiom Lprimeprime_zero_of_rank_ne_two5 : zeroOrderE5 != 2 -> Lprimeprime_E5_one = 0

/-- Taylor structure, CONVERSE at rank 2 (definitional analytic fact):
    ord = 2 means the (s-1)^2 Taylor coefficient is nonzero, i.e.
    L''(1) != 0 — NO Kolyvagin input needed (unlike rank 1, where
    L'(1) != 0 is the deep Kolyvagin–Gross–Zagier theorem).  This
    closes the analytic-side NONZERO leg of the two-way closure at the
    definition level: if L''(1) > 0 is ever established, it is rank 2
    itself doing the work — the regulator cannot collapse (R2 > 0,
    geometric rigidity), and the second derivative cannot vanish
    (Taylor structure). -/
axiom Lprimeprime_ne_zero_of_rank_eq_two : zeroOrderE = 2 -> Lprimeprime_E_one != 0

/-- Taylor structure, converse at rank 2, twist side (definitional). -/
axiom Lprimeprime_ne_zero_of_rank_eq_two5 : zeroOrderE5 = 2 -> Lprimeprime_E5_one != 0

/-- BSD positivity, rank 0 (THEOREM-level: Kolyvagin–Logachev & BSD
    rank-0 regime; the center value of a rank-0 curve is strictly
    positive, since the leading coefficient is Omega·Sha/|T|^2 > 0). -/
axiom l_one_pos_of_rank_zero : zeroOrderE = 0 -> 0 < LE_one

/-- BSD positivity, rank 0, twist side. -/
axiom l_one_pos_of_rank_zero5 : zeroOrderE5 = 0 -> 0 < LE5_one

/-- Kolyvagin–Gross–Zagier: analytic rank exactly 1 forces the center
    derivative to be NONZERO (THEOREM-level: for rank 1 the weak BSD
    rank part is proved — ord_1 L(E) = 1 implies L'(1) != 0, Sha finite).
    This is the "Kolyvagin upper-bound constraint" the entanglement
    boundary analysis isolates: it controls NONZERO, never the sign. -/
axiom lprime_ne_zero_of_rank_one : zeroOrderE = 1 -> Lprime_E_one != 0

/-- Kolyvagin–Gross–Zagier, twist side. -/
axiom lprime_ne_zero_of_rank_one5 : zeroOrderE5 = 1 -> Lprime_E5_one != 0

/-- Real period of E (positive, THEOREM-level). -/
axiom OmegaE : Real

/-- Neron–Tate regulator of E at rank 1 (positive for a generator of
    infinite order, THEOREM-level — height is positive definite). -/
axiom RegulatorE : Real

/-- Order of the Tate–Shafarevich group of E (a positive rational, if
    finite; finiteness is the conjecture — see bsd_formula_rank_one). -/
axiom ShaE : Real

/-- Size of the torsion subgroup |E(Q)_tors| (positive integer). -/
axiom TorsionSizeE : Nat

/-- Real period positivity (THEOREM-level). -/
axiom OmegaE_pos : 0 < OmegaE

/-- Regulator positivity (THEOREM-level: height positive-definiteness). -/
axiom RegulatorE_pos : 0 < RegulatorE

/-- Sha is a positive rational number (trivial if finite). -/
axiom ShaE_pos : 0 < ShaE

/-- Torsion size is positive (trivial). -/
axiom TorsionSizeE_pos : 0 < TorsionSizeE

/-- Rank-1 refined BSD formula (CONJECTURE-level, the SINGLE remaining
    positivity obstacle):  L'(E,1) = Omega·R·Sha/|T|^2.
    The sign of L'(1) is therefore NOT an independent sign conjecture:
    every factor of the right-hand side is already known to be positive
    by THEOREM (Omega, Regulator, Sha > 0 as a positive rational,
    |T|^2 > 0).  Hence "L'(1) > 0" reduces to the formula itself
    (equivalently: Sha finite + exact BSD value) — this is the precise
    boundary of the entanglement positivity. -/
axiom bsd_formula_rank_one :
  zeroOrderE = 1 ->
    Lprime_E_one = OmegaE * RegulatorE * ShaE / (TorsionSizeE : Real) ^ 2

/-- A positive real number is nonzero (trivial). -/
theorem pos_implies_ne_zero {x : Real} (h : 0 < x) : x ≠ 0 :=
  ne_of_gt h

/-- BSD positivity, rank 1 — now a THEOREM, derived from the refined
    formula + factor positivity (no longer an axiom).  The conjecture
    content has been moved entirely into `bsd_formula_rank_one`
    (Sha finiteness); positivity of Omega/Regulator/Sha/|T|^2 is
    theorem-level, so the sign of L'(E,1) carries no independent
    obstacle beyond the formula. -/
theorem lprime_pos_of_rank_one (h : zeroOrderE = 1) : 0 < Lprime_E_one := by
  have hf : Lprime_E_one = OmegaE * RegulatorE * ShaE / (TorsionSizeE : Real) ^ 2 :=
    bsd_formula_rank_one h
  rw [hf]
  have hOR : 0 < OmegaE * RegulatorE := mul_pos OmegaE_pos RegulatorE_pos
  have hORS : 0 < OmegaE * RegulatorE * ShaE := mul_pos hOR ShaE_pos
  have hT2 : 0 < (TorsionSizeE : Real) ^ 2 := pow_pos (by exact_mod_cast TorsionSizeE_pos) 2
  exact div_pos hORS hT2

/-- Entanglement positivity is EXACTLY same-sign-ness: L'(E)·L'(E^5) > 0
    iff both derivatives are positive or both negative.  Neither sign is
    forced by the Kolyvagin nonzero theorem; the common sign must come
    from `lprime_pos_of_rank_one(_5)` (rank-1 refined BSD) — this is the
    boundary statement in theorem form: the entanglement product carries
    no positivity information beyond the two component signs. -/
theorem entanglement_positive_iff_same_sign {a b : Real} :
    0 < a * b <-> ((0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) := by
  constructor
  · intro hab
    by_cases ha : 0 < a
    · left
      constructor
      · exact ha
      · by_contra hb_le
        have hb0 : b <= 0 := le_of_not_gt hb_le
        nlinarith
    · right
      constructor
      · have ha0 : a ≠ 0 := by
          intro hz
          subst hz
          nlinarith
        exact lt_of_le_of_ne (le_of_not_gt ha) ha0
      · by_contra hb_ge
        have hb0 : 0 <= b := le_of_not_gt hb_ge
        nlinarith
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_pos ha hb
    · have hpos : 0 < (-a) * (-b) := mul_pos (by linarith) (by linarith)
      nlinarith

/-- Real period of E^5 (positive, THEOREM-level). -/
axiom OmegaE5 : Real

/-- Neron–Tate regulator of E^5 at rank 1 (positive, THEOREM-level). -/
axiom RegulatorE5 : Real

/-- Order of the Tate–Shafarevich group of E^5 (positive rational). -/
axiom ShaE5 : Real

/-- Size of the torsion subgroup |E^5(Q)_tors| (positive integer). -/
axiom TorsionSizeE5 : Nat

/-- Real period positivity of E^5 (THEOREM-level). -/
axiom OmegaE5_pos : 0 < OmegaE5

/-- Rank-1 regulator positivity of E^5 (THEOREM-level). -/
axiom RegulatorE5_pos : 0 < RegulatorE5

/-- Sha of E^5 is a positive rational (trivial if finite). -/
axiom ShaE5_pos : 0 < ShaE5

/-- Torsion size of E^5 is positive (trivial). -/
axiom TorsionSizeE5_pos : 0 < TorsionSizeE5

/-- Rank-1 refined BSD formula for E^5 (CONJECTURE-level, the SINGLE
    remaining positivity obstacle on the twist side): the symmetric
    decomposition of `bsd_formula_rank_one`. -/
axiom bsd_formula_rank_one5 :
  zeroOrderE5 = 1 ->
    Lprime_E5_one = OmegaE5 * RegulatorE5 * ShaE5 / (TorsionSizeE5 : Real) ^ 2

/-- BSD positivity, rank 1, twist side — now a THEOREM (formula axiom
    + factor positivity), completing the symmetric downgrade. -/
theorem lprime_pos_of_rank_one5 (h : zeroOrderE5 = 1) : 0 < Lprime_E5_one := by
  have hf : Lprime_E5_one = OmegaE5 * RegulatorE5 * ShaE5 / (TorsionSizeE5 : Real) ^ 2 :=
    bsd_formula_rank_one5 h
  rw [hf]
  have hOR : 0 < OmegaE5 * RegulatorE5 := mul_pos OmegaE5_pos RegulatorE5_pos
  have hORS : 0 < OmegaE5 * RegulatorE5 * ShaE5 := mul_pos hOR ShaE5_pos
  have hT2 : 0 < (TorsionSizeE5 : Real) ^ 2 := pow_pos (by exact_mod_cast TorsionSizeE5_pos) 2
  exact div_pos hORS hT2

/-- Rank-2 regulator of E: the 2x2 Neron–Tate height-matrix determinant
    (positive, THEOREM-level — the height pairing is positive definite,
    so the Gram determinant of two linearly independent generators is
    strictly positive). -/
axiom Regulator2E : Real

/-- Rank-2 regulator positivity (THEOREM-level: positive-definite 2x2
    Gram determinant). -/
axiom Regulator2E_pos : 0 < Regulator2E

/-- Rank-2 refined BSD formula (CONJECTURE-level, the SINGLE remaining
    positivity obstacle at rank 2):  L''(E,1) = 2·Omega·R2·Sha/|T|^2
    (leading coefficient L''(1)/2 = Omega·R2·Sha/|T|^2; the 2 is the
    1/2! = 1/2 from the Taylor expansion, folded to the left).
    Exactly as in rank 1, every factor of the RHS is known positive by
    THEOREM — including the rank-2 regulator, since the 2x2 height
    matrix is positive definite.  So "L''(1) > 0" reduces to the
    formula itself (Sha finite): the rank-2 sign carries no
    independent obstacle. -/
axiom bsd_formula_rank_two :
  zeroOrderE = 2 ->
    Lprimeprime_E_one = (2 : Real) * OmegaE * Regulator2E * ShaE / (TorsionSizeE : Real) ^ 2

/-- Rank-2 regulator of E^5 (2x2 determinant, positive, THEOREM-level). -/
axiom Regulator2E5 : Real

/-- Rank-2 regulator positivity of E^5 (THEOREM-level). -/
axiom Regulator2E5_pos : 0 < Regulator2E5

/-- Rank-2 refined BSD formula for E^5 (CONJECTURE-level, symmetric). -/
axiom bsd_formula_rank_two5 :
  zeroOrderE5 = 2 ->
    Lprimeprime_E5_one = (2 : Real) * OmegaE5 * Regulator2E5 * ShaE5 / (TorsionSizeE5 : Real) ^ 2

/-- BSD positivity, rank 2 — now a THEOREM, derived from the rank-2
    refined formula + factor positivity (no longer an axiom).  The
    conjecture content has moved entirely into `bsd_formula_rank_two`
    (Sha finiteness); the rank-2 regulator enters only through its
    positivity, which is theorem-level (positive-definite 2x2 Gram
    determinant).  This completes the rank-2 leg of the downgrade:
    P*'s (2,0) branch positivity now comes from a theorem, exactly as
    the (1,1) branch did. -/
theorem lprimeprime_pos_of_rank_two (h : zeroOrderE = 2) : 0 < Lprimeprime_E_one := by
  have hf : Lprimeprime_E_one = (2 : Real) * OmegaE * Regulator2E * ShaE / (TorsionSizeE : Real) ^ 2 :=
    bsd_formula_rank_two h
  rw [hf]
  have h2 : 0 < (2 : Real) := by norm_num
  have h2O : 0 < (2 : Real) * OmegaE := mul_pos h2 OmegaE_pos
  have h2OR : 0 < (2 : Real) * OmegaE * Regulator2E := mul_pos h2O Regulator2E_pos
  have h2ORS : 0 < (2 : Real) * OmegaE * Regulator2E * ShaE := mul_pos h2OR ShaE_pos
  have hT2 : 0 < (TorsionSizeE : Real) ^ 2 := pow_pos (by exact_mod_cast TorsionSizeE_pos) 2
  exact div_pos h2ORS hT2

/-- BSD positivity, rank 2, twist side — now a THEOREM, symmetric. -/
theorem lprimeprime_pos_of_rank_two5 (h : zeroOrderE5 = 2) : 0 < Lprimeprime_E5_one := by
  have hf : Lprimeprime_E5_one = (2 : Real) * OmegaE5 * Regulator2E5 * ShaE5 / (TorsionSizeE5 : Real) ^ 2 :=
    bsd_formula_rank_two5 h
  rw [hf]
  have h2 : 0 < (2 : Real) := by norm_num
  have h2O : 0 < (2 : Real) * OmegaE5 := mul_pos h2 OmegaE5_pos
  have h2OR : 0 < (2 : Real) * OmegaE5 * Regulator2E5 := mul_pos h2O Regulator2E5_pos
  have h2ORS : 0 < (2 : Real) * OmegaE5 * Regulator2E5 * ShaE5 := mul_pos h2OR ShaE5_pos
  have hT2 : 0 < (TorsionSizeE5 : Real) ^ 2 := pow_pos (by exact_mod_cast TorsionSizeE5_pos) 2
  exact div_pos h2ORS hT2

/-- Taylor cutoff: ord_1 L(E/K) >= 3 forces L''(E/K,1) = 0 — this is
    why P* must restrict its hypothesis to rank EXACTLY 2 (the original
    "positive lower bound for all rank >= 2" phrasing is false at
    rank 3 and above; the P* domain closes at rank 2). -/
axiom LppEK_zero_of_rank_ge_three : 3 <= analyticZeroOrder -> Lprimeprime_EK_one = 0

/-! ## 2. Theorem layer: P* from componentwise BSD positivity -/

/-- Type trichotomy: analytic rank 2 over K splits as
    (0,2) | (1,1) | (2,0) by additivity. -/
lemma type_trichotomy (h : zeroOrderE + zeroOrderE5 = 2) :
    (zeroOrderE = 0 /\ zeroOrderE5 = 2) \/ (zeroOrderE = 1 /\ zeroOrderE5 = 1) \/
      (zeroOrderE = 2 /\ zeroOrderE5 = 0) := by
  by_cases h0 : zeroOrderE = 0
  · left
    constructor
    · exact h0
    · omega
  by_cases h1 : zeroOrderE = 1
  · right
    left
    constructor
    · exact h1
    · omega
  by_cases h2 : zeroOrderE = 2
  · right
    right
    constructor
    · exact h2
    · omega
  · exfalso
    omega

/-- P* at type (2,0): L''(E/K,1) = L''(E,1)·L(E^5,1) > 0 —
    rank-2 BSD positivity on E, times the THEOREM-level rank-0
    positivity of L(E^5,1).  The middle and last Leibniz terms vanish
    (rank 0 kills L'(E^5,1); rank 2 kills L(E,1)). -/
theorem p_star_type_20 (hE2 : zeroOrderE = 2) (hE5_0 : zeroOrderE5 = 0) :
    0 < Lprimeprime_EK_one := by
  have hLppE : 0 < Lprimeprime_E_one := lprimeprime_pos_of_rank_two hE2
  have hLE5 : 0 < LE5_one := l_one_pos_of_rank_zero5 hE5_0
  have hprod : 0 < Lprimeprime_E_one * LE5_one := mul_pos hLppE hLE5
  have hLpE5 : Lprime_E5_one = 0 :=
    Lprime_zero_of_rank_ne_one5 (by simp [hE5_0])
  have hLE : LE_one = 0 :=
    L_value_zero_of_rank_pos (by simp [hE2])
  rw [leibniz_artin, hLpE5, hLE]
  simp
  exact hprod

/-- P* at type (1,1): L''(E/K,1) = 2·L'(E,1)·L'(E^5,1) > 0 —
    the ENTANGLEMENT branch.  The first and last Leibniz terms vanish
    (rank 1 kills L(E,1) and L(E^5,1)); the middle term is positive
    exactly by the two rank-1 BSD positivities — the content of P* is
    the rank-1 BSD positivity, restated. -/
theorem p_star_type_11 (hE1 : zeroOrderE = 1) (hE5_1 : zeroOrderE5 = 1) :
    0 < Lprimeprime_EK_one := by
  have hLE : LE_one = 0 :=
    L_value_zero_of_rank_pos (by simp [hE1])
  have hLE5 : LE5_one = 0 :=
    L_value_zero_of_rank_pos5 (by simp [hE5_1])
  have hLpE : 0 < Lprime_E_one := lprime_pos_of_rank_one hE1
  have hLpE5 : 0 < Lprime_E5_one := lprime_pos_of_rank_one5 hE5_1
  have hmid : 0 < (2 : Real) * Lprime_E_one * Lprime_E5_one :=
    mul_pos (mul_pos (by norm_num) hLpE) hLpE5
  rw [leibniz_artin, hLE, hLE5]
  simp
  exact hmid

/-- P* at type (0,2): L''(E/K,1) = L(E,1)·L''(E^5,1) > 0 —
    mirror of (2,0): THEOREM-level rank-0 positivity of L(E,1), times
    rank-2 BSD positivity of the twist. -/
theorem p_star_type_02 (hE0 : zeroOrderE = 0) (hE5_2 : zeroOrderE5 = 2) :
    0 < Lprimeprime_EK_one := by
  have hLE : 0 < LE_one := l_one_pos_of_rank_zero hE0
  have hLppE5 : 0 < Lprimeprime_E5_one := lprimeprime_pos_of_rank_two5 hE5_2
  have hLpE : Lprime_E_one = 0 :=
    Lprime_zero_of_rank_ne_one (by simp [hE0])
  have hLppE : Lprimeprime_E_one = 0 :=
    Lprimeprime_zero_of_rank_ne_two (by simp [hE0])
  have hprod : 0 < LE_one * Lprimeprime_E5_one := mul_pos hLE hLppE5
  rw [leibniz_artin, hLpE, hLppE]
  simp
  exact hprod

/-- P* (main theorem): on K = Q(sqrt 5), analytic rank exactly 2 forces
    the second derivative at the center to be strictly positive.
    The proof is a type-by-type case split; every branch reduces to
    componentwise BSD positivity.  Upgrading P* to a theorem therefore
    requires upgrading rank-1/rank-2 BSD positivity (rank-0 is already
    theorem-level). -/
theorem p_star (h : zeroOrderE + zeroOrderE5 = 2) :
    0 < Lprimeprime_EK_one := by
  rcases type_trichotomy h with h02 | h11 | h20
  · rcases h02 with ⟨hE0, hE5_2⟩
    exact p_star_type_02 hE0 hE5_2
  · rcases h11 with ⟨hE1, hE5_1⟩
    exact p_star_type_11 hE1 hE5_1
  · rcases h20 with ⟨hE2, hE5_0⟩
    exact p_star_type_20 hE2 hE5_0

/-- Boundary theorem: at rank >= 3 the second derivative is identically
    zero, so the "positive lower bound" reading of the original question
    is false beyond rank 2 — the P* domain is exactly rank 2. -/
theorem rank_ge_three_implies_Lpp_zero (h : 3 <= analyticZeroOrder) :
    Lprimeprime_EK_one = 0 := LppEK_zero_of_rank_ge_three h

/-! ## 3. Data layer: realized types (389a1 -> (2,0); 106b1 -> (1,1)) -/

/-- ord_1 L(389a1, s). -/
axiom zeroOrder389E : Nat

/-- ord_1 L(389a1^5, s). -/
axiom zeroOrder389E5 : Nat

/-- 389a1/Q has analytic rank 2 — Cremona ecdata allbsd authoritative
    line: `389 a 1 [0,1,1,-2,0] 2 1 1 4.98042512171011
    0.759316500288427 0.152460177943144 1` (rank column = 2;
    0.759316500288427 = L''(1)/2). -/
axiom zeroOrder389E_eq_two : zeroOrder389E = 2

/-- 389a1's 5-twist has rank 0: L(E^5,1) = 8.909 != 0 (numeric probe,
    Q = 3000 convergent pipeline; eps(E^5) = eps(E)*chi_5(389) = +1,
    even rank allowed, measured 0). -/
axiom zeroOrder389E5_eq_zero : zeroOrder389E5 = 0

/-- Realized type of 389a1 on K: (2,0) — the trivial-positivity branch
    of P* (no entanglement needed). -/
theorem probe389_type_is_2_0 : zeroOrder389E = 2 /\ zeroOrder389E5 = 0 :=
  ⟨zeroOrder389E_eq_two, zeroOrder389E5_eq_zero⟩

/-- L''(389a1,1) — the analytic second derivative of L(389a1, s) at
    s = 1 (value of the (2,0) branch's E-component). -/
axiom Lprimeprime389E_one : Real

/-- Strict interval verification: L''(389a1,1)/2 > 0, MACHINE-CHECKABLE
    and UNCONDITIONAL — no BSD formula, no Sha finiteness, no Kolyvagin
    input is needed for the sign of this particular value.
    probe389_strict.py (mpmath interval arithmetic, mp.dps = 90,
    Q = 3000, Lavrik identity exact for any Q):
      L''(389a1,1)/2  in  [0.7583683262976454, 0.7602647044343964]
    error ledger: iv round-off half-width 7.0e-4; diff truncation
    h^2*M4/12 = 9.5e-4 (h = 1e-4, M4 <= 1.14e6 from iv 4th-difference
    x4 safety); cross-h residual 3.4e-5; total delta 1.9e-3 (x2
    safety) — 400x below the 0.758 lower bound.
    Q-stability: Q = 2000 vs 3000 agree to 2.2e-16 (identity exact,
    no truncation error); Sage reference 0.759316500288427 matched to
    1.5e-8.
    This is the concrete instance of the two-way closure claim:
    "L''(1) > 0 because rank = 2, not because the regulator
    collapsed" — the analytic-side sign is established strictly for
    389a1, independent of the BSD formula (the formula's R2/Sha content
    remains the separate conjecture, untouched by this lemma).
    Re-runnable: `python probe389_strict.py > probe389_strict_out.txt`. -/
axiom probe389_strict_pos : 0 < Lprimeprime389E_one

/-- ord_1 L(106b1, s) — a rank-1 curve with conductor N = 106 ≡ 1 (mod 5)
    (eps(E^5) = eps(E)*chi_5(106) = (−1)(+1) = −1: odd rank allowed). -/
axiom zeroOrder106E : Nat

/-- ord_1 L(106b1^5, s). -/
axiom zeroOrder106E5 : Nat

/-- 106b1/Q has analytic rank 1 (Cremona allbsd rank column). -/
axiom zeroOrder106E_eq_one : zeroOrder106E = 1

/-- 106b1's 5-twist has rank 1: L(E^5,1) < 1e-6 (zero) and
    L'(E^5,1) = 4.2345 != 0 (numeric probe, Q = 3000). -/
axiom zeroOrder106E5_eq_one : zeroOrder106E5 = 1

/-- Realized type of 106b1 on K: (1,1) — the ENTANGLEMENT branch of
    P* is nonempty. -/
theorem probe106_type_is_1_1 : zeroOrder106E = 1 /\ zeroOrder106E5 = 1 :=
  ⟨zeroOrder106E_eq_one, zeroOrder106E5_eq_one⟩

/-- (1,1) is nonempty as a type: realized by 106b1 (and, per the recon,
    by 79a1, 89a1, 91a1, 99a1, 101a1 — all six rank-1 curves with
    N ≡ ±1 mod 5 tested have E^5 of rank 1).  Parity cannot exclude
    (1,1); the family it pins down is realized. -/
theorem one_one_type_realized :
    exists a b : Nat, a = 1 /\ b = 1 /\ a = zeroOrder106E /\ b = zeroOrder106E5 := by
  refine ⟨1, 1, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rw [zeroOrder106E_eq_one]
  · rw [zeroOrder106E5_eq_one]

/-- First derivative of L(106b1, s) at the center. -/
axiom Lprime106E_one : Real

/-- First derivative of L(106b1^5, s) at the center. -/
axiom Lprime106E5_one : Real

/-- Strict interval verification of the 106b1 entanglement:
    L'(E,1)·L'(E^5,1) > 0, MACHINE-CHECKABLE and UNCONDITIONAL.
    probe_twists_strict.py (mpmath iv, mp.dps = 90, Q = 3000, Lavrik
    identity exact; central difference h = 1e-4, truncation bound
    h^2*M3/6 with M3 via iv 3rd-difference x4):
      L'(106b1,1)  in [0.66531598507918444, 0.66531610113523820]
      L'(106b1^5,1) in [4.23243023378982919, 4.23243117528115942]
      product      in [2.81590349027280284, 2.81590460786129482]
    error ledger per side: iv half-width ~1e-8, truncation ~2.9e-7,
    cross-h residual (h = 1e-4 vs 1e-5) ~7e-8, x2 safety — margin
    ~1e7 over the 2.8 lower bound.  Old float pipeline agrees to
    0.05% (its h = 0.02 central difference is the dominant error).
    Theorems above make precise what this data point can and cannot
    do: `entanglement_positive_iff_same_sign` shows it is equivalent
    to same-sign-ness of the two component derivatives; the common
    sign is established HERE by strict interval arithmetic, without
    invoking the BSD formula (the formula's content remains a separate
    conjecture).  Re-runnable: python probe_twists_strict.py. -/
axiom entanglement_pos_106 : 0 < Lprime106E_one * Lprime106E5_one

/-- First derivative of L(79a1, s) at the center. -/
axiom Lprime79E_one : Real

/-- First derivative of L(79a1^5, s) at the center. -/
axiom Lprime79E5_one : Real

/-- Strict interval verification (79a1): product in
    [2.37398827988610339, 2.37398909782306866], lo > 0. -/
axiom entanglement_pos_79a1 : 0 < Lprime79E_one * Lprime79E5_one

/-- First derivative of L(89a1, s) at the center. -/
axiom Lprime89E_one : Real

/-- First derivative of L(89a1^5, s) at the center. -/
axiom Lprime89E5_one : Real

/-- Strict interval verification (89a1): product in
    [2.74855253228599805, 2.74855350821509647], lo > 0. -/
axiom entanglement_pos_89a1 : 0 < Lprime89E_one * Lprime89E5_one

/-- First derivative of L(91a1, s) at the center. -/
axiom Lprime91E_one : Real

/-- First derivative of L(91a1^5, s) at the center. -/
axiom Lprime91E5_one : Real

/-- Strict interval verification (91a1): product in
    [3.05101590912779219, 3.05101703276215197], lo > 0. -/
axiom entanglement_pos_91a1 : 0 < Lprime91E_one * Lprime91E5_one

/-- First derivative of L(99a1, s) at the center. -/
axiom Lprime99E_one : Real

/-- First derivative of L(99a1^5, s) at the center. -/
axiom Lprime99E5_one : Real

/-- Strict interval verification (99a1): product in
    [2.60777345684348205, 2.60777443631160377], lo > 0. -/
axiom entanglement_pos_99a1 : 0 < Lprime99E_one * Lprime99E5_one

/-- First derivative of L(101a1, s) at the center. -/
axiom Lprime101E_one : Real

/-- First derivative of L(101a1^5, s) at the center. -/
axiom Lprime101E5_one : Real

/-- Strict interval verification (101a1): product in
    [2.83147604482945692, 2.83147705700724694], lo > 0. -/
axiom entanglement_pos_101a1 : 0 < Lprime101E_one * Lprime101E5_one

/-! ## 4. Document-chain tie-in (comment only)

P* is the positivity face of "why not 2" on K = Q(sqrt 5):

    Stage 1/2 (37a1/K, rank 1):  rank 2 excluded three ways by parity
       (BSD.Main.analytic_rank_K_eq_one_of_LK_prime_ne_zero, docstring
       merged "(iii) rank-2 three-way exclusion").
    Point 1 (389a1, eps = +1, rank 2): parity sieve dies,
       (0,2)/(2,0) revive; Kolyvagin bound = (0,0) gap.
    Point 2 (5077a1, eps = −1, rank 3): sieve partly revives,
       (2,1) — the only ord-2 carrier — dies free: the exclusion is
       EPSILON-driven, the numerical cost is RANK-driven.
    P* (this module): if rank EXACTLY 2 survives, then L''(E/K,1) > 0
       — and the only nontrivial branch (1,1) is nonempty (6/6 recon)
       and is exactly rank-1 BSD positivity.  Hence P* <=> componentwise
       BSD positivity: a restatement, not a new theorem.

Boundary statement (the user's original question, corrected):
    "all rank >= 2 curves on K have L'' bounded below" is FALSE —
    rank >= 3 gives L'' = 0 (rank_ge_three_implies_Lpp_zero) and
    5077a1/K is the concrete rank-3 witness.  The defensible theorem is
    P* (rank exactly 2), and P* is BSD positivity in disguise.
-/

end BSD.Positivity
