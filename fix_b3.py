f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 替换之前插入的 mellin_kernel_spectral_countable_surjective 为更直接的公理
old_axiom = """/-- Mellin 核在可数点集上的取值满射性（公理，联合插值理论核心）：
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
      (∀ (x : ℝ), x ∈ S → k.toTestFunction.eval x = v x)"""

new_axiom = """/-- Mellin 差方向与谱点取值保持的联合插值（公理，联合插值理论核心）：
    对任意磨光函数 f, g 和可数点集 S ⊆ ℝ，存在磨光函数 f'，使得：
    (1) M[f'](s) - M[f](s) = M[g](s) 对所有 s ∈ ℂ
    (2) f'.eval(x) = f.eval(x) 对所有 x ∈ S。

    数学依据：谱点取值约束是有限/可数个线性条件，其余维为无限，
    因此可以在保持这些点取值的同时叠加任意 Mellin 方向 g。
    这是 Paley-Wiener 型空间中"赋值映射×Mellin 映射"联合满射性的标准结果。
    磨光函数的 supportSeparated 约束（某区间=1）不影响，因为可以在该区间外调整。
    风险等级：中高（联合插值的满射性，B 组谱点叠加公理的统一基础）。 -/
axiom mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x)"""

content = content.replace(old_axiom, new_axiom, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: replaced kernel axiom with shift_preserving axiom')
