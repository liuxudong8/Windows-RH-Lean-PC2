import BSD.Positivity.Positivity

/-!
# Axiom-closure check for BSD.Positivity
Run: lake build BSD.Positivity (or the full lake build BSD).
Every declaration used by the theorems below must be visible in the
#print axioms output: Positivity-layer axioms only (no leakage of
Stage2 / Main / Probe389 / Probe5077 axioms into the P* closure).
-/

-- core P* theorems
#check BSD.Positivity.type_trichotomy
#check BSD.Positivity.p_star_type_20
#check BSD.Positivity.p_star_type_11
#check BSD.Positivity.p_star_type_02
#check BSD.Positivity.p_star
#check BSD.Positivity.rank_ge_three_implies_Lpp_zero
#check BSD.Positivity.pos_implies_ne_zero
#check BSD.Positivity.lprime_pos_of_rank_one
#check BSD.Positivity.lprime_pos_of_rank_one5
#check BSD.Positivity.lprimeprime_pos_of_rank_two
#check BSD.Positivity.lprimeprime_pos_of_rank_two5
#check BSD.Positivity.entanglement_positive_iff_same_sign
#check BSD.Positivity.probe389_type_is_2_0
#check BSD.Positivity.probe389_strict_pos
#check BSD.Positivity.probe106_type_is_1_1
#check BSD.Positivity.one_one_type_realized
#check BSD.Positivity.entanglement_pos_79a1
#check BSD.Positivity.entanglement_pos_89a1
#check BSD.Positivity.entanglement_pos_91a1
#check BSD.Positivity.entanglement_pos_99a1
#check BSD.Positivity.entanglement_pos_101a1
#check BSD.Positivity.entanglement_pos_106
#print axioms BSD.Positivity.probe389_strict_pos

#print axioms BSD.Positivity.p_star
#print axioms BSD.Positivity.p_star_type_11
#print axioms BSD.Positivity.lprime_pos_of_rank_one
#print axioms BSD.Positivity.lprime_pos_of_rank_one5
#print axioms BSD.Positivity.lprimeprime_pos_of_rank_two
#print axioms BSD.Positivity.lprimeprime_pos_of_rank_two5
#print axioms BSD.Positivity.rank_ge_three_implies_Lpp_zero
#print axioms BSD.Positivity.entanglement_positive_iff_same_sign
#print axioms BSD.Positivity.one_one_type_realized
