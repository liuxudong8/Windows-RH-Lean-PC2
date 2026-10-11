import BSD.ExclusionReduction

/-!
# Closure check: BSD.ExclusionReduction (2026-10-11)

核对归约定理各关键定理的 axiom 闭包：
- exclusion_layer_reduction 的假设面 = Stage2 声明层 + 解析对象 axiom
  + 新桥 zeroOrderE_eq_one_of_lprime_ne_zero；不含 GRH、bsd_formula_rank_*、Sha。
- analytic_rank_K_eq_one_via_exclusion_reduction 另加 analytic_rank_K_eq_zero_order。
- §1 通用 Leibniz 归约应为零 axiom（纯微积分真定理）。
-/

#print axioms BSD.ExclusionReduction.exclusion_layer_reduction
#print axioms BSD.ExclusionReduction.analytic_rank_K_eq_one_via_exclusion_reduction
#print axioms BSD.ExclusionReduction.exclusion_layer_nonzero
#print axioms BSD.ExclusionReduction.zeroOrderE_eq_one
#print axioms BSD.ExclusionReduction.leibniz_10_ne_zero
#print axioms BSD.ExclusionReduction.product_deriv_decomposition
