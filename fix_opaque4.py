f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 热核（opaque）：K_t(z, w) = 热方程的基本解。
    在三维双曲流形上有显式表达式（见 heatKernel_explicit_formula）。
    热核是对称的、正定的、满足半群性质。 -/
opaque heatKernel : ℝ → ManifoldM → ManifoldM → ℂ"""

new = """/-- 三维双曲热核（定义）：K_t(z, w) = 热方程的基本解。
    对 t>0，显式公式为：
      K_t(z,w) = (4πt)^(-3/2) · e^{-t} · e^{-d²/(4t)} · (d / sinh d)
    其中 d = hyperbolicDistance(z,w)。
    对 t≤0，定义为 0（热核仅在 t>0 时有意义）。
    因子 d/sinh(d) 来自三维双曲空间的体积元。 -/
noncomputable def heatKernel (t : ℝ) (z w : ManifoldM) : ℂ :=
    if 0 < t then
      let d := hyperbolicDistance z w
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(d)^2 / (4 * t)) *
        (d / ((Real.exp d - Real.exp (-d)) / 2)) : ℝ) : ℂ)
    else 0"""

content = content.replace(old, new, 1)

# 降级 heatKernel_explicit_formula 为定理
old2 = """axiom heatKernel_explicit_formula (t : ℝ) (z w : ManifoldM) : 0 < t →
    heatKernel t z w =
      Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
      Real.exp (-(hyperbolicDistance z w)^2 / (4 * t)) *
      (hyperbolicDistance z w / ((Real.exp (hyperbolicDistance z w) - Real.exp (-(hyperbolicDistance z w))) / 2))"""

new2 = """/-- 热核显式公式（定理，由定义直接推出）。 -/
theorem heatKernel_explicit_formula (t : ℝ) (z w : ManifoldM) (ht : 0 < t) :
    heatKernel t z w =
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(hyperbolicDistance z w)^2 / (4 * t)) *
        (hyperbolicDistance z w / ((Real.exp (hyperbolicDistance z w) - Real.exp (-(hyperbolicDistance z w))) / 2)) : ℝ) : ℂ) := by
  rw [heatKernel]; rw [if_pos ht]; rfl"""

content = content.replace(old2, new2, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: heatKernel -> def, heatKernel_explicit_formula -> theorem')
