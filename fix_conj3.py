with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 innerProductM_conj_sym
old_m = """theorem innerProductM_conj_sym (f g : L2Function ManifoldM) :
    innerProductM f g = star (innerProductM g f) := by
  simp only [innerProductM]
  have h_main : star (manifoldIntegral (fun z : ManifoldM => g z * star (f z))) =
      manifoldIntegral (fun z : ManifoldM => star (g z * star (f z))) := by
    exact?
  rw [← h_main]
  congr with z
  have h1 : star (g z * star (f z)) = f z * star (g z) := by
    rw [star_mul, star_star] <;> ring
  exact h1"""

new_m = """theorem innerProductM_conj_sym (f g : L2Function ManifoldM) :
    innerProductM f g = star (innerProductM g f) := by
  simp only [innerProductM, manifoldIntegral, hyperbolicIntegral3]
  have h_main : star (integral hyperbolicMeasure3 (fun z : ManifoldM => g z * star (f z))) =
      integral hyperbolicMeasure3 (fun z : ManifoldM => star (g z * star (f z))) := by
    simpa [star_eq_conj] using integral_conj (f := (fun z : ManifoldM => g z * star (f z))) (μ := hyperbolicMeasure3)
  rw [← h_main]
  congr with z
  have h1 : star (g z * star (f z)) = f z * star (g z) := by
    rw [star_mul, star_star] <;> ring
  exact h1"""

content = content.replace(old_m, new_m)

# 修复 innerProductX_conj_sym
old_x = """theorem innerProductX_conj_sym (f g : L2Function ManifoldX) :
    innerProductX f g = star (innerProductX g f) := by
  simp only [innerProductX]
  have h_main : star (manifoldIntegralX (fun z : ManifoldX => g z * star (f z))) =
      manifoldIntegralX (fun z : ManifoldX => star (g z * star (f z))) := by
    exact?
  rw [← h_main]
  congr with z
  have h1 : star (g z * star (f z)) = f z * star (g z) := by
    rw [star_mul, star_star] <;> ring
  exact h1"""

new_x = """theorem innerProductX_conj_sym (f g : L2Function ManifoldX) :
    innerProductX f g = star (innerProductX g f) := by
  simp only [innerProductX, manifoldIntegralX, hyperbolicIntegral2]
  have h_main : star (integral hyperbolicMeasure2 (fun z : ManifoldX => g z * star (f z))) =
      integral hyperbolicMeasure2 (fun z : ManifoldX => star (g z * star (f z))) := by
    simpa [star_eq_conj] using integral_conj (f := (fun z : ManifoldX => g z * star (f z))) (μ := hyperbolicMeasure2)
  rw [← h_main]
  congr with z
  have h1 : star (g z * star (f z)) = f z * star (g z) := by
    rw [star_mul, star_star] <;> ring
  exact h1"""

content = content.replace(old_x, new_x)

with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
