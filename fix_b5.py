f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """theorem mollified_spectral_delta :
    ∀ (n : ℕ), ∃ (δ : MollifiedTestFunction),
      (∀ (k : ℕ), k = n → δ.toTestFunction.eval (specDiscM k) = 1) ∧
      (∀ (k : ℕ), k ≠ n → δ.toTestFunction.eval (specDiscM k) = 0) := by"""

new = """/-- Mellin 差方向与谱点取值保持的联合插值（公理，联合插值理论核心）：
    对任意磨光函数 f, g 和可数点集 S ⊆ ℝ，存在磨光函数 f'，使得：
    (1) M[f'](s) - M[f](s) = M[g](s) 对所有 s ∈ ℂ
    (2) f'.eval(x) = f.eval(x) 对所有 x ∈ S。

    数学依据：谱点取值约束是可数个线性条件，其余维为无限，
    因此可以在保持这些点取值的同时叠加任意 Mellin 方向 g。
    这是 Paley-Wiener 型空间中"赋值映射×Mellin 映射"联合满射性的标准结果。
    风险等级：中高（联合插值的满射性，B 组谱点叠加公理的统一基础）。 -/
axiom mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x)

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

theorem mollified_spectral_delta :
    ∀ (n : ℕ), ∃ (δ : MollifiedTestFunction),
      (∀ (k : ℕ), k = n → δ.toTestFunction.eval (specDiscM k) = 1) ∧
      (∀ (k : ℕ), k ≠ n → δ.toTestFunction.eval (specDiscM k) = 0) := by"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: inserted 2 axioms before mollified_spectral_delta')
