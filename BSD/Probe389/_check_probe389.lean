import BSD.Probe389.Probe389

/-!
# Axiom-closure check for BSD.Probe389
Run: lake env lean -R _check_probe389.lean  (or: lake build BSD.Probe389)
Every declaration used by the theorems below must be visible in the
#print axioms output: Probe389-specific axioms only (no leakage of
Stage2 or Main axioms into the probe closure).
-/

-- core probe theorems (should reduce to the probe axioms)
#check BSD.Probe389.analyticRankE389_eq_two
#check BSD.Probe389.evenE389
#check BSD.Probe389.evenE3895
#check BSD.Probe389.evenK389
#check BSD.Probe389.parityK389_propagated
#check BSD.Probe389.rootNumberK389_from_product
#check BSD.Probe389.no_type11_probe
#check BSD.Probe389.type20_parity_compatible
#check BSD.Probe389.type02_parity_compatible
#check BSD.Probe389.rank_two_decomposition389
#check BSD.Probe389.rankTwo_survivors_after_parity
#check BSD.Probe389.parity_sieve_fails_for_epsilon_plus_one
#check BSD.Probe389.rank2_parity_compatible

#print axioms BSD.Probe389.parityK389_propagated
#print axioms BSD.Probe389.rankTwo_survivors_after_parity
#print axioms BSD.Probe389.parity_sieve_fails_for_epsilon_plus_one
#print axioms BSD.Probe389.rootNumberK389_from_product
