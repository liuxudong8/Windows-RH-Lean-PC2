import BSD.Probe5077.Probe5077

/-!
# Axiom-closure check for BSD.Probe5077
Run: lake build BSD.Probe5077 (or the full lake build BSD).
Every declaration used by the theorems below must be visible in the
#print axioms output: Probe5077-specific axioms only (no leakage of
Stage2 / Main / Probe389 axioms into the probe closure).
-/

-- core probe theorems (should reduce to the probe axioms)
#check BSD.Probe5077.analyticRankE5077_eq_three
#check BSD.Probe5077.oddE5077
#check BSD.Probe5077.evenE50775
#check BSD.Probe5077.rank_three_decomposition5077
#check BSD.Probe5077.no_type03_5077
#check BSD.Probe5077.no_type21_5077
#check BSD.Probe5077.type12_parity_compatible
#check BSD.Probe5077.type30_parity_compatible
#check BSD.Probe5077.rankThree_survivors_after_parity
#check BSD.Probe5077.parity_sieve_partially_revives
#check BSD.Probe5077.rank3_parity_compatible
#check BSD.Probe5077.rank2_absent_from_survivors

#print axioms BSD.Probe5077.rankThree_survivors_after_parity
#print axioms BSD.Probe5077.parity_sieve_partially_revives
#print axioms BSD.Probe5077.rank2_absent_from_survivors
