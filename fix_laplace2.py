f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除当前位置的 laplaceTransform 定义（在 realIntegral 之后）
old_lap_def = '''/-- Laplace 变换（def，用 realIntegral 实现）：
    L[f](t) = ∫₀^∞ f(x) e^{-tx} dx。 -/
def laplaceTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
    realIntegral (fun x => f x * Real.exp (-t * x))


'''
content = content.replace(old_lap_def, '', 1)

# 2. 把 realIntegral 移到 laplaceTransform 公理之前（第200行附近）
# 先删除 realIntegral 的定义
old_real = '''/-- 实数轴上的积分（opaque）：∫₀^∞ h(t) dt。
    用于热核的 Laplace 变换加权积分：K_f = ∫₀^∞ L[f](t) K_t dt。
    当前用 opaque 抽象，具体实现需要测度论基础设施。 -/
opaque realIntegral : (ℝ → ℂ) → ℂ

'''
content = content.replace(old_real, '', 1)

# 3. 在 Section 6.1 开头插入 realIntegral + laplaceTransform 定义
old_sec = '''/- 6.1 分析基础设施：Laplace 变换、Γ 作用、热核显式公式 -/

/-- Laplace 变换的指数函数计算（公理）：'''

new_sec = '''/- 6.1 分析基础设施：Laplace 变换、Γ 作用、热核显式公式 -/

/-- 实数轴上的积分（opaque）：∫₀^∞ h(t) dt。
    用于热核的 Laplace 变换加权积分：K_f = ∫₀^∞ L[f](t) K_t dt。
    当前用 opaque 抽象，具体实现需要测度论基础设施。 -/
opaque realIntegral : (ℝ → ℂ) → ℂ

/-- Laplace 变换（def，用 realIntegral 实现）：
    L[f](t) = ∫₀^∞ f(x) e^{-tx} dx。 -/
noncomputable def laplaceTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
    realIntegral (fun x => f x * Real.exp (-t * x))

/-- Laplace 变换的指数函数计算（公理）：'''

content = content.replace(old_sec, new_sec, 1)

# 4. fLaplacianKernel 需要 noncomputable
content = content.replace(
    'def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=',
    'noncomputable def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=',
    1
)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: reordered realIntegral and laplaceTransform')
