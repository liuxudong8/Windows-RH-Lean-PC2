import BSD.EulerSystem

/-! 闭包核验：B 阶段组合真证（无 axiom 泄漏）+ 锚点清单。 -/

#check BSD.EulerSystem.lambda_zero_of_kato
#check BSD.EulerSystem.lambda_zero_iff_corank_eq_rank
#check BSD.EulerSystem.lambda2_389a1_eq_zero

#print axioms BSD.EulerSystem.lambda_zero_of_kato
#print axioms BSD.EulerSystem.lambda_zero_iff_corank_eq_rank

-- 目标链检索：λ_2(389a1) = 0 锚点（axiom）
#check BSD.EulerSystem.rank_389a1
#check BSD.EulerSystem.kolyvagin_rank2_blind_389a1
