f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除当前的 laplaceTransform 定义
old_lap = '''    定义为 L[f](t) = ∫₀^∞ f(x) e^{-tx} dx（用 realIntegral 实现）。 -/
def laplaceTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
    realIntegral (fun x => f x * Real.exp (-t * x))

'''
content = content.replace(old_lap, '', 1)

# 2. 在 realIntegral 之后插入 laplaceTransform 定义
old_real = '''opaque realIntegral : (ℝ → ℂ) → ℂ


/-- f(Δ) 的积分核（定义）：'''

new_real = '''opaque realIntegral : (ℝ → ℂ) → ℂ

/-- Laplace 变换（def，用 realIntegral 实现）：
    L[f](t) = ∫₀^∞ f(x) e^{-tx} dx。 -/
def laplaceTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
    realIntegral (fun x => f x * Real.exp (-t * x))


/-- f(Δ) 的积分核（定义）：'''

content = content.replace(old_real, new_real, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: moved laplaceTransform after realIntegral')
