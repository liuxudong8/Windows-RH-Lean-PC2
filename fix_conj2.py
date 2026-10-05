with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 innerProductM_conj_sym
old_m = """theorem innerProductM_conj_sym (f g : L2Function ManifoldM) :
    innerProductM f g = star (innerProductM g f) := by
  simp only [innerProductM]
  have h : (fun z : ManifoldM => f z * star (g z)) = fun z => star (g z * star (f z)) := by
    funext z
    have h1 : star (g z * star (f z)) = star (g z) * star (star (f z)) := by rw [star_mul]
    rw [h1]
    have h2 : star (star (f z)) = f z := by simp
    rw [h2] <;> ring
  rw [h]
  rw [integral_conj]
  <;> rfl"""

new_m = """theorem innerProductM_conj_sym (f g : L2Function ManifoldM) :
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

content = content.replace(old_m, new_m)

# 修复 innerProductX_conj_sym
old_x = """theorem innerProductX_conj_sym (f g : L2Function ManifoldX) :
    innerProductX f g = star (innerProductX g f) := by
  simp only [innerProductX]
  have h : (fun z : ManifoldX => f z * star (g z)) = fun z => star (g z * star (f z)) := by
    funext z
    have h1 : star (g z * star (f z)) = star (g z) * star (star (f z)) := by rw [star_mul]
    rw [h1]
    have h2 : star (star (f z)) = f z := by simp
    rw [h2] <;> ring
  rw [h]
  rw [integral_conj]
  <;> rfl"""

new_x = """theorem innerProductX_conj_sym (f g : L2Function ManifoldX) :
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

content = content.replace(old_x, new_x)

with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
