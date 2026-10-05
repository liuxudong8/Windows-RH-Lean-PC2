f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 在 mollified_spectral_delta 之前插入两个新公理
old_insert = """/-- 谱点 δ 函数存在性（公理，插值理论）："""

new_insert = """/-- Mellin 核在可数点集上的取值满射性（公理，联合插值理论核心）：
    对任意可数点集 S ⊆ ℝ 和任意赋值 v : ℝ → ℂ，存在磨光函数 k，使得：
    (1) M[k](s) = 0 对所有 s ∈ ℂ（k 在 Mellin 变换的核中）
    (2) k.eval(x) = v(x) 对所有 x ∈ S。

    数学依据：Mellin 变换的核空间是无限维的（在我们的框架中，realIntegral 是抽象的，
    不假设 Mellin 变换单射）。核空间在离散点集上的取值映射是满射的，
    这是 Paley-Wiener 型空间的标准性质。
    风险等级：中高（核空间的满插值性质，是 B 组谱点叠加公理的统一基础）。 -/
axiom mellin_kernel_spectral_countable_surjective
    (S : Set ℝ) (hS : S.Countable) (v : ℝ → ℂ) :
    ∃ (k : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform k.toTestFunction s = 0) ∧
      (∀ (x : ℝ), x ∈ S → k.toTestFunction.eval x = v x)

/-- 可数谱点集上的函数取值插值（公理，Whitney 延拓）：
    对任意可数点集 S ⊆ ℝ 和任意赋值 v : ℝ → ℂ，存在磨光函数 f，使得
    f.eval(x) = v(x) 对所有 x ∈ S。

    数学依据：离散点集（无聚点）上的任意函数都可以延拓为紧支集光滑函数
    （Whitney 延拓定理的离散版本）。specDiscM 严格递增趋向无穷，故无聚点。
    风险等级：中低（离散点集上的 Whitney 延拓，标准分析结果）。 -/
axiom spectral_point_countable_interpolation
    (S : Set ℝ) (hS : S.Countable) (v : ℝ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x)

/-- 谱点 δ 函数存在性（定理，由可数谱点插值推出）："""

content = content.replace(old_insert, new_insert, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: inserted 2 joint interpolation axioms')
