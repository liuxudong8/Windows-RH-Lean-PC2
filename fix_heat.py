f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# heatKernel -> def（用显式公式）
old_heat = '''/-- 热核（opaque）：K_t(z, w) = 热方程 ∂_t u = Δ u 的基本解。
    在三维双曲流形 M = Γ\\H³ 上，热核有显式表达式：
      K_t(z, w) = (4πt)^(-3/2) e^{-t} e^{-d(z,w)²/(4t)} · (d(z,w)/sinh(d(z,w)))
    热核是对称的 K_t(z,w)=K_t(w,z)、正定的、满足半群性质。
    Arthur 迹公式的几何侧可以用热核表示：
      Tr(f(Δ)) = ∫_M Σ_{γ∈Γ} f(dist(z,γz)) K_t(z,γz) dz
    当前用 opaque 抽象，参数 (t, z, w)。 -/
opaque heatKernel : ℝ → ManifoldM → ManifoldM → ℂ'''

new_heat = '''/-- 热核（def，三维双曲热核显式公式）：
    K_t(z, w) = (4πt)^(-3/2) e^{-t} e^{-d(z,w)²/(4t)} · (d(z,w)/sinh(d(z,w)))
    对 t>0，此公式给出光滑、正定、对称的热核。
    对 t≤0，定义为 0（热核只在 t>0 时有意义）。 -/
noncomputable def heatKernel (t : ℝ) (z w : ManifoldM) : ℂ :=
  if 0 < t then
    let d := hyperbolicDistance z w
    (Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
     Real.exp (-(d)^2 / (4 * t)) *
     (d / ((Real.exp d - Real.exp (-d)) / 2)) : ℝ)
  else
    0'''

content = content.replace(old_heat, new_heat, 1)

# 删除 heatKernel_explicit_formula 公理
old_explicit = '''/-- 三维双曲热核的显式公式（公理）：
    K_t(z, w) = (4πt)^(-3/2) e^{-t} e^{-d(z,w)²/(4t)} · (d(z,w)/sinh(d(z,w)))
    其中 d(z,w) = hyperbolicDistance z w，sinh(d) = (e^d - e^{-d})/2。

    数学依据：三维双曲空间 H³ 上的热方程
      ∂_t u = ∂_r² u + 2 coth(r) ∂_r u - u
    其解为上述显式公式。
    因子 d/sinh(d) 来自三维双曲空间的体积元 r² sinh²(r) dr。
    对 t>0，此公式给出光滑、正定、对称的热核。 -/
axiom heatKernel_explicit_formula (t : ℝ) (z w : ManifoldM) : 0 < t →
    heatKernel t z w =
      Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
      Real.exp (-(hyperbolicDistance z w)^2 / (4 * t)) *
      (hyperbolicDistance z w / ((Real.exp (hyperbolicDistance z w) - Real.exp (-(hyperbolicDistance z w))) / 2))

'''
content = content.replace(old_explicit, '', 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: heatKernel -> def')
