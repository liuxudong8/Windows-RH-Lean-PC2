f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除 heatKernel 定义（第154-165行附近）
old_heat_def = '''/-- 热核（def，三维双曲热核显式公式）：
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
    0



'''
content = content.replace(old_heat_def, '', 1)

# 2. 在 hyperbolicDistance 之后插入 heatKernel 定义
old_hyp = '''opaque hyperbolicDistance : ManifoldM → ManifoldM → ℝ

/-- Γ 作用下双曲距离不变性（公理）：'''

new_hyp = '''opaque hyperbolicDistance : ManifoldM → ManifoldM → ℝ

/-- 热核（def，三维双曲热核显式公式）：
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
    0

/-- Γ 作用下双曲距离不变性（公理）：'''

content = content.replace(old_hyp, new_hyp, 1)

# 3. fLaplacianKernel 需要 noncomputable
content = content.replace(
    'def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=',
    'noncomputable def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=',
    1
)

# 4. heatOperator 需要 noncomputable
content = content.replace(
    'def heatOperator (t : ℝ) : L2Function ManifoldM → L2Function ManifoldM :=',
    'noncomputable def heatOperator (t : ℝ) : L2Function ManifoldM → L2Function ManifoldM :=',
    1
)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: moved heatKernel, fixed noncomputable')
