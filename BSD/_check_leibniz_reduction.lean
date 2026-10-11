import BSD.LeibnizReduction

/-!
# Closure check: BSD.LeibnizReduction (2026-10-11)

核对二阶 Leibniz 归约各关键定理的 axiom 闭包：
- §1 泛型三型（product_second_deriv / leibniz_20_second / leibniz_11_second_ne_zero）：
  应为纯逻辑公理（零挂账）。
- leibniz_artin_theorem：L_fun_structure + 逻辑（不含 Positivity.leibniz_artin）。
- p_star_via_leibniz / leibniz_20_second_object：L_fun_structure +
  Positivity 分量正性/Taylor 族 + 逻辑；不含 leibniz_artin、
  不含 bsd_formula_rank_*、不含 GRH。
-/

#print axioms BSD.LeibnizReduction.product_second_deriv
#print axioms BSD.LeibnizReduction.leibniz_20_second
#print axioms BSD.LeibnizReduction.leibniz_11_second_ne_zero
#print axioms BSD.LeibnizReduction.leibniz_artin_theorem
#print axioms BSD.LeibnizReduction.leibniz_20_second_object
#print axioms BSD.LeibnizReduction.p_star_type_11_via_leibniz
#print axioms BSD.LeibnizReduction.p_star_via_leibniz
