import BSD.ShaFreeLayer
import BSD.ShaPComponent

/-! 闭包核验：免费层真证（无 axiom）+ 实例层依赖清单。 -/

#check BSD.ShaFreeLayer.card_eq_mul_of_short_exact_add
#check BSD.ShaFreeLayer.AlternatingPairing
#check BSD.ShaFreeLayer.Nondegenerate
#check BSD.ShaFreeLayer.injective_of_nondegenerate
#check BSD.ShaFreeLayer.sha2_389_card_eq_one

#print axioms BSD.ShaFreeLayer.card_eq_mul_of_short_exact_add
#print axioms BSD.ShaFreeLayer.injective_of_nondegenerate
#print axioms BSD.ShaFreeLayer.sha2_389_card_eq_one

-- 跨模块组合：A.1 + |Ш[2]|=1（实例层）
#check BSD.ShaPComponent.pPrimaryComponent_eq_bot_of_torsionBy_eq_bot
