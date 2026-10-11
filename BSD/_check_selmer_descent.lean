import BSD.SelmerDescent

/-!
# 闭包审计：BSD.SelmerDescent

Sel 层 descent 挂账。期望闭包：
- 全部结论只依赖本模块对象层 axiom（Selmer 有限性 Prop + 正合列 +
  descent 序列 + Kolyvagin Selmer 形式），**不含 bsd_formula_rank_\*、
  不含 GRH**——与 SymmetryReduction 的 Kolyvagin/descent 同层（数学定理级）。
-/

#print axioms BSD.SelmerDescent.sha_finite_EK_of_selmer_descent
#print axioms BSD.SelmerDescent.sha_finite_EK_11_via_selmer
