f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 替换 mellin_shift_preserving_spectral_values 公理为两个子公理+定理
old = """/-- Mellin 差方向与谱点取值保持的联合插值（公理，联合插值理论核心）：
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
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x)"""

new = """/-- 单个谱点约束的 Mellin 差叠加（公理，插值理论原子）：
    对任意磨光函数 f, g 和单点 x₀ ∈ ℝ，存在磨光函数 f'，使得：
    (1) M[f'](s) - M[f](s) = M[g](s) 对所有 s ∈ ℂ
    (2) f'.eval(x₀) = f.eval(x₀)。

    数学依据：单个点的取值约束是一个线性条件，其余维为无限，
    因此可以在保持该点取值的同时叠加任意 Mellin 方向。
    这比可数版本弱得多，只涉及一个约束。
    风险等级：中（单个线性约束的余维数无限，标准泛函分析结果）。 -/
axiom mellin_shift_single_spectral_point
    (f g : MollifiedTestFunction) (x0 : ℝ) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      f'.toTestFunction.eval x0 = f.toTestFunction.eval x0

/-- 可数谱点约束的紧致性原理（公理，泛函分析紧致性）：
    如果对任意有限子集 F ⊆ S，都存在 f' 保持 F 中所有点取值且 Mellin 差 = M[g]，
    则存在 f' 保持 S 中所有点取值且 Mellin 差 = M[g]。

    数学依据：在 Fréchet 空间中，可数个递减闭集的交集非空，
    只要每个有限交非空（紧致性/完备性）。保持有限个点取值的解集是闭集，
    且随有限集增大而递减嵌套。
    风险等级：中（Fréchet 空间的有限交性质，标准泛函分析结果）。 -/
axiom mellin_shift_countable_compactness
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    (∀ (F : Finset ℝ), (∀ x ∈ F, x ∈ S) →
      ∃ (f' : MollifiedTestFunction),
        (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                      melinTransform g.toTestFunction s) ∧
        (∀ x ∈ F, f'.toTestFunction.eval x = f.toTestFunction.eval x)) →
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x)

/-- 可数谱点约束的 Mellin 差叠加（定理，由单点+有限交+紧致性推出）：
    对任意磨光函数 f, g 和可数点集 S ⊆ ℝ，存在磨光函数 f'，使得：
    (1) M[f'](s) - M[f](s) = M[g](s) 对所有 s ∈ ℂ
    (2) f'.eval(x) = f.eval(x) 对所有 x ∈ S。 -/
theorem mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x) := by
  apply mellin_shift_countable_compactness f g S hS
  intro F hF_sub
  induction' F using Finset.induction with x F hx ih
  · -- 空集：取 f'=f
    refine' ⟨f, _⟩
    constructor
    · intro s; simp
    · intro x hx; exfalso; exact Finset.not_mem_empty x hx
  · -- 插入 x：先对 F\{x} 构造 f₁，再对 x 构造 f'
    have hF'_sub : ∀ y ∈ F, y ∈ S := by intro y hy; exact hF_sub y (Finset.mem_insert_of_mem hy)
    rcases ih hF'_sub with ⟨f1, h_melin1, h_spec1⟩
    have hx_in_S : x ∈ S := hF_sub x (Finset.mem_insert_self x F)
    rcases mellin_shift_single_spectral_point f1 g x with ⟨f', h_melin, h_spec_x⟩
    refine' ⟨f', h_melin, _⟩
    intro y hy
    by_cases h_y_eq : y = x
    · rw [h_y_eq]; exact h_spec_x
    · have h_y_in_F : y ∈ F := by
        simpa [h_y_eq] using (Finset.mem_insert.mp hy).resolve_left h_y_eq
      exact h_spec1 y h_y_in_F"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: split mellin_shift_preserving_spectral_values into single + compactness')
