import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import BSD.LSeries5

/-!
# Stage 2: rank-2 exclusion for E = 37a1 / Q(sqrt 5)

Second-stage Lean skeleton: the root-number parity argument excluding
analytic rank 2 over K = Q(sqrt 5).  Stage 1 established analytic
rank = 1 (BSD.Main.analytic_rank_K_eq_one); Stage 2 adds the answer
to "why not rank 2".

## Math statement (2026-10-07, corrected)

E = 37a1 (epsilon(E) = -1, rank 1) and E^5 = its 5-twist
(epsilon(E^5) = +1).  Over K = Q(sqrt 5):

  ord_1 L(E/K) = ord_1 L(E) + ord_1 L(E^5)     (Artin decomposition)
  epsilon(E)   = -1  ==>  ord_1 L(E)   odd
  epsilon(E^5) = +1  ==>  ord_1 L(E^5) even

Hence ord_1 L(E/K) is odd, so analytic rank 2 is impossible.
This is FREE: no numerical input is needed.

Type-screening version: rank 2 would split by additivity as
(0,2), (1,1) or (2,0).  Each type is excluded by parity alone:
  (0,2): needs ord_1 L(E) = 0,  but epsilon(E) = -1 forces oddness
  (1,1): needs ord_1 L(E^5) = 1, but epsilon(E^5) = +1 forces evenness
  (2,0): needs ord_1 L(E) = 2,  but epsilon(E) = -1 forces oddness

Correction note: an earlier draft (2026-10-07 discussion) claimed
(0,2) is the only remaining candidate.  That was WRONG: epsilon(E) = -1
forces ord_1 L(E) odd, so (0,2) (which needs ord_1 L(E) = 0) is also
excluded by parity.  All three types die; rank 2 is impossible with
zero numerical input.  The numerical path (L(E^5,1) != 0) is kept below
as an independent double-check only.

## Axiom inventory (Stage-2 independent layer, 13 axioms)

| axiom | meaning | upgrade path |
|---|---|---|
| rootNumberE | epsilon(E) | automorphic L theory (mathlib missing) |
| rootNumberE5 | epsilon(E^5) | same |
| rootNumberK | epsilon(E/K) | same |
| rootNumberE_eq_neg_one | epsilon(E) = -1 | local root numbers (C5 audit) |
| rootNumberE5_eq_one | epsilon(E^5) = +1 | chi_5 primitive, gcd(37,5) = 1 |
| rootNumberK_eq_neg_one | epsilon(E/K) = -1 | product rule epsilon(E)*epsilon(E^5) |
| zeroOrderE | ord_1 L(E) | L-function layer |
| zeroOrderE5 | ord_1 L(E^5) | L-function layer |
| analyticZeroOrder | ord_1 L(E/K) | L-function layer |
| parity_neg_one | eps = -1 ==> order odd | functional equation |
| parity_pos_one | eps = +1 ==> order even | functional equation |
| zeroOrder_additivity | Artin decomposition | Artin / L-functoriality |
| zeroOrderE5_eq_zero_of_L_E5_one_ne_zero | nonzero value ==> order 0 | analyticity + Taylor |

## Theorems (real, closed proofs)

oddE, evenE5, oddK (parity instantiations), parityK_propagated
(additivity + E/E5 parity, WITHOUT the epsilon(K) axiom),
rootNumberK_from_product (multiplicativity checked numerically),
analyticRankK_ne_two (direct parity), analyticRankK_ne_two'
(type screening), rank_two_decomposition, no_type02/11/20,
zeroOrderE5_eq_zero (numerical), no_type02_numeric (double-check).
-/

namespace BSD.Stage2

/-! ## 1. Object layer: root numbers and zero orders (axioms) -/

/-- Global root number of E = 37a1/Q.  mathlib has no root-number
    theory; upgrade path: automorphic L functions / modular forms. -/
axiom rootNumberE : Int

/-- Global root number of the quadratic twist E^5/Q. -/
axiom rootNumberE5 : Int

/-- Global root number of E/K, K = Q(sqrt 5) (base change). -/
axiom rootNumberK : Int

/-- epsilon(E) = -1: L(E,s) has odd functional-equation sign. -/
axiom rootNumberE_eq_neg_one : rootNumberE = -1

/-- epsilon(E^5) = +1: chi_5 primitive (D_K = 5 = conductor), chi_5 even
    (chi_5(-1) = 1), gcd(N_E, 5) = gcd(37,5) = 1, so no local correction
    terms: epsilon(E^5) = epsilon(E) * chi_5(N_E) = (-1)*(-1) = +1.
    Numerically cross-checked with local signs / LMFDB. -/
axiom rootNumberE5_eq_one : rootNumberE5 = 1

/-- epsilon(E/K) = -1: product rule epsilon(E/K) = epsilon(E)*epsilon(E^5)
    = (-1)*(+1).  Numerical consistency is a theorem below
    (rootNumberK_from_product); the rule itself stays an axiom. -/
axiom rootNumberK_eq_neg_one : rootNumberK = -1

/-- ord_1 L(E, s): order of vanishing at the center s = 1. -/
axiom zeroOrderE : Nat

/-- ord_1 L(E^5, s). -/
axiom zeroOrderE5 : Nat

/-- ord_1 L(E/K, s), the analytic side of the analytic rank of E/K. -/
axiom analyticZeroOrder : Nat

/-- Functional-equation parity: a global root number -1 forces odd order.
    Upgrade path: functional equation of the completed L-function. -/
axiom parity_neg_one : forall {eps : Int} {r : Nat}, eps = -1 -> exists k : Nat, r = 2 * k + 1

/-- Functional-equation parity: a global root number +1 forces even order
    (zero allowed). -/
axiom parity_pos_one : forall {eps : Int} {r : Nat}, eps = 1 -> exists k : Nat, r = 2 * k

/-- Artin decomposition: ord_1 L(E/K) = ord_1 L(E) + ord_1 L(E^5)
    (base change of E to K = Q(sqrt 5), L(E/K) = L(E)*L(E^5)). -/
axiom zeroOrder_additivity : analyticZeroOrder = zeroOrderE + zeroOrderE5

/-- Bridge: a nonzero center value forces order 0 (analyticity + Taylor
    expansion around s = 1).  Instantiates with the closed theorem
    LSeries5.L_E5_one_ne_zero.  Kept only as a numerical double-check:
    the parity argument already excludes rank 2. -/
axiom zeroOrderE5_eq_zero_of_L_E5_one_ne_zero :
  LSeries5.L_E5 1 ≠ 0 -> zeroOrderE5 = 0

/-! ## 2. Theorem layer: parity lemmas (real proofs) -/

/-- ord_1 L(E) is odd (from epsilon(E) = -1). -/
theorem oddE : exists k : Nat, zeroOrderE = 2 * k + 1 :=
  parity_neg_one rootNumberE_eq_neg_one

/-- ord_1 L(E^5) is even (from epsilon(E^5) = +1). -/
theorem evenE5 : exists k : Nat, zeroOrderE5 = 2 * k :=
  parity_pos_one rootNumberE5_eq_one

/-- ord_1 L(E/K) is odd, directly from epsilon(E/K) = -1. -/
theorem oddK : exists k : Nat, analyticZeroOrder = 2 * k + 1 :=
  parity_neg_one rootNumberK_eq_neg_one

/-- Parity propagates through additivity WITHOUT the epsilon(K) axiom:
    odd (E) + even (E^5) = odd (E/K).  This makes rootNumberK_eq_neg_one
    redundant for the rank-2 exclusion (structural proof). -/
theorem parityK_propagated : exists k : Nat, analyticZeroOrder = 2 * k + 1 := by
  rcases oddE with ⟨a, ha⟩
  rcases evenE5 with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [zeroOrder_additivity, ha, hb]
  omega

/-- Multiplicativity of root numbers, checked numerically:
    epsilon(E/K) = epsilon(E)*epsilon(E^5) = (-1)*(+1) = -1. -/
theorem rootNumberK_from_product : rootNumberK = rootNumberE * rootNumberE5 := by
  rw [rootNumberK_eq_neg_one, rootNumberE_eq_neg_one, rootNumberE5_eq_one]
  norm_num

/-! ## 3. Rank-2 exclusion (main theorems) -/

/-- Main theorem (direct parity): analytic rank of E/K is NOT 2.
    (BSD interpretation: analyticRankK = analyticZeroOrder.) -/
theorem analyticRankK_ne_two : analyticZeroOrder ≠ 2 := by
  rcases oddK with ⟨k, hk⟩
  intro h
  omega

/-- Type decomposition: rank 2 splits as (0,2) | (1,1) | (2,0)
    by additivity (all nonnegative solutions of a + b = 2). -/
lemma rank_two_decomposition (h : analyticZeroOrder = 2) :
    (zeroOrderE = 0 /\ zeroOrderE5 = 2) \/ (zeroOrderE = 1 /\ zeroOrderE5 = 1) \/
      (zeroOrderE = 2 /\ zeroOrderE5 = 0) := by
  have hs : zeroOrderE + zeroOrderE5 = 2 := zeroOrder_additivity.symm.trans h
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

/-- Type (0,2) is excluded: needs ord_1 L(E) = 0, but epsilon(E) = -1
    forces oddness.  (Correction of the earlier draft: this type dies
    by parity alone, no numerics needed.) -/
lemma no_type02 : Not (zeroOrderE = 0 /\ zeroOrderE5 = 2) := by
  rcases oddE with ⟨k, hk⟩
  rintro ⟨h0, _⟩
  omega

/-- Type (1,1) is excluded: needs ord_1 L(E^5) = 1, but epsilon(E^5) = +1
    forces evenness. -/
lemma no_type11 : Not (zeroOrderE = 1 /\ zeroOrderE5 = 1) := by
  rcases evenE5 with ⟨k, hk⟩
  rintro ⟨_, h1⟩
  omega

/-- Type (2,0) is excluded: needs ord_1 L(E) = 2, but epsilon(E) = -1
    forces oddness. -/
lemma no_type20 : Not (zeroOrderE = 2 /\ zeroOrderE5 = 0) := by
  rcases oddE with ⟨k, hk⟩
  rintro ⟨h2, _⟩
  omega

/-- Main theorem (screening version): rank 2 has no type to live in. -/
theorem analyticRankK_ne_two' : analyticZeroOrder ≠ 2 := by
  intro h
  rcases rank_two_decomposition h with h02 | h11 | h20
  · exact no_type02 h02
  · exact no_type11 h11
  · exact no_type20 h20

/-! ## 4. Numerical double-check (independent of parity) -/

/-- ord_1 L(E^5) = 0: closed theorem L_E5_one_ne_zero (LSeries5)
    through the bridge axiom.  Independent confirmation of the (0,2)
    exclusion, kept as a backup only. -/
theorem zeroOrderE5_eq_zero : zeroOrderE5 = 0 :=
  zeroOrderE5_eq_zero_of_L_E5_one_ne_zero LSeries5.L_E5_one_ne_zero

/-- Type (0,2) excluded numerically as well (0 = 2 contradiction). -/
theorem no_type02_numeric : Not (zeroOrderE = 0 /\ zeroOrderE5 = 2) := by
  rw [zeroOrderE5_eq_zero]
  omega

/-! ## 5. Tie-in with Stage 1 (comment only)

BSD.Main.analytic_rank_K_eq_one : analyticRank Curve37a1 KFive = 1
(closure: analytic_rank_K_eq_one_of_LK_prime_ne_zero + basics).
Stage 2 adds: analytic rank != 2, excluded three ways by parity
(E side and E^5 side in every type); the numerical L(E^5,1) != 0
path is an independent backup.  Together with Stage 1, the analytic
rank of E/Q(sqrt 5) is exactly 1 and rank 2 is impossible.
-/

end BSD.Stage2
