f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 分布的支撑（opaque）：
    对 TestFunction 上的线性泛函 D（分布），其支撑 supp(D) 是 ℝ 的子集，
    表示 D"非零"或"有奇点"的点集。
    完整定义需要分布论（test function 空间、对偶、支撑概念），
    当前用 opaque 抽象。这是逆向显式公式分布支撑比较的核心概念。 -/
opaque distributionSupport : (TestFunction → ℂ) → Set ℝ"""

new = """/-- 分布的支撑（定义）：
    对 TestFunction 上的线性泛函 D（分布），其支撑 supp(D) 是 ℝ 的子集：
    x ∈ supp(D) 当且仅当 x 的每个邻域内都存在测试函数 f 使得 D(f) ≠ 0。
    等价地，supp(D) 是使得 D 在其补集上为零的最小闭集。
    这是分布论的标准定义。 -/
def distributionSupport (D : TestFunction → ℂ) : Set ℝ :=
    {x : ℝ | ∀ (R : ℝ), 0 < R → ∃ (f : TestFunction),
      (∀ (y : ℝ), |y - x| ≥ R → f.eval y = 0) ∧ D f ≠ 0}"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: distributionSupport -> def')
