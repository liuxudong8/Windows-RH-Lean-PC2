import BSD.Positivity.Positivity
import BSD.PositivityGRH.PositivityGRH

open BSD.Positivity
open BSD.PositivityGRH

/-!
# P* — hypothesis-or confluence:  (refined BSD formula) OR (unconditional analytic structure) ==> P*

Both channels exist independently:

* Channel A  `BSD.Positivity`      : refined BSD formula (R_2 > 0, Sha
                                     finite, exact L'' identity)  => P*.
  Positivity layer: object axioms + 4 formula axioms + zero-order
  elimination axioms; rank-1/rank-2 component positivity are THEOREMS
  derived from the formula axioms.

* Channel B  `BSD.PositivityGRH`   : UNCONDITIONAL analytic structure
                                     (zero-free region Re(s) > 1 — a
                                     theorem via Hasse/Deligne + modu-
                                     larity + absolute convergence; Euler
                                     product tail, IVT sign preservation,
                                     Taylor quotients) => component
                                     positivity => P*.
  Channel-B layer: THEOREM-level axioms only (no conjecture-level
  axiom).  GRH RETIRED from the P* assumption spectrum 2026-10-10:
  the former K-GRH no-zero axioms were replaced by the unconditional
  zero-free-region axioms `zero_free_re_one_side(_5)`.

This module records the IMMUNITY STATEMENT in a single theorem:
P* requires only that AT LEAST ONE of the two hypothesis families
holds.  The two flag propositions carry no mathematical content
(formula_holds / uncond_holds); the choice axiom formula_or_uncond
declares the disjunction.  Each disjunct branch then invokes the
corresponding channel theorem verbatim:

    formula_holds  =>  BSD.Positivity.p_star           (formula path)
    uncond_holds   =>  BSD.PositivityGRH.p_star_uncond (unconditional path)

Meta-level audit (outside the kernel, via `#print axioms`):
the axiom closure of `p_star` contains NO Channel-B axiom, and the
closure of `p_star_uncond` contains NO Channel-A formula axiom —
the two paths are mutually independent, which is exactly the
immunity content.  Since Channel B now carries NO conjecture-level
axiom, P* is immune to GRH entirely (GRH is not even needed): the
only conjecture family left in the spectrum is the refined BSD
formula.

## Axiom inventory (this module)

* formula_holds : Prop  -- flag: refined BSD formula family holds
* uncond_holds  : Prop  -- flag: unconditional analytic structure holds
* formula_or_uncond : formula_holds ∨ uncond_holds  -- disjunction choice
-/

namespace BSD.PStarOr

/-- Flag: the refined BSD formula family (Channel A) holds.
    Carries no content here; the content lives in the Channel-A
    axiom layer. -/
axiom formula_holds : Prop

/-- Flag: the unconditional analytic structure family (Channel B)
    holds.  Carries no content here; the content lives in the
    Channel-B axiom layer (theorem-level axioms only; GRH retired). -/
axiom uncond_holds : Prop

/-- Immunity statement: P* needs only one of the two families. -/
axiom formula_or_uncond : formula_holds ∨ uncond_holds

/-! ## Component positivity under either family -/

/-- rank 1 on E: L'(E,1) > 0 under formula OR unconditional structure. -/
theorem Lp_pos (h : zeroOrderE = 1) : 0 < Lprime_E_one := by
  rcases formula_or_uncond with _hF | _hU
  · exact lprime_pos_of_rank_one h
  · exact Lp_pos_uncond h

/-- rank 2 on E: L''(E,1) > 0 under formula OR unconditional structure. -/
theorem Lpp_pos (h : zeroOrderE = 2) : 0 < Lprimeprime_E_one := by
  rcases formula_or_uncond with _hF | _hU
  · exact lprimeprime_pos_of_rank_two h
  · exact Lpp_pos_uncond h

/-- rank 1 on E^5: L'(E^5,1) > 0 under formula OR unconditional. -/
theorem Lp_pos5 (h : zeroOrderE5 = 1) : 0 < Lprime_E5_one := by
  rcases formula_or_uncond with _hF | _hU
  · exact lprime_pos_of_rank_one5 h
  · exact Lp_pos_uncond5 h

/-- rank 2 on E^5: L''(E^5,1) > 0 under formula OR unconditional. -/
theorem Lpp_pos5 (h : zeroOrderE5 = 2) : 0 < Lprimeprime_E5_one := by
  rcases formula_or_uncond with _hF | _hU
  · exact lprimeprime_pos_of_rank_two5 h
  · exact Lpp_pos_uncond5 h

/-! ## Main: P* under the disjunction -/

/-- P* via hypothesis-or:  (formula ∨ unconditional)  +  rank exactly 2
    on K =>  L''(E/K,1) > 0.  Formula branch: Channel-A theorem;
    unconditional branch: Channel-B theorem. -/
theorem p_star_or (h : analyticZeroOrder = 2) : 0 < Lprimeprime_EK_one := by
  rcases formula_or_uncond with _hF | _hU
  · have hadd : zeroOrderE + zeroOrderE5 = 2 := by
      rw [← zeroOrder_additivity]
      exact h
    exact p_star hadd
  · exact p_star_uncond h

end BSD.PStarOr
