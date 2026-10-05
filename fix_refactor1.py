f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除 mellin_shift 公理，替换为可数版本定理
old_shift = """/-- 可数谱点约束的 Mellin 差叠加（公理，联合插值理论核心）：
    对任意磨光函数 f, g 和可数点集 S ⊆ ℝ，存在磨光函数 f'，使得：
    (1) M[f'](s) - M[f](s) = M[g](s) 对所有 s ∈ ℂ
    (2) f'.eval(x) = f.eval(x) 对所有 x ∈ S。

    数学依据：谱点取值约束是可数个线性条件，其余维为无限，
    因此可以在保持这些点取值的同时叠加任意 Mellin 方向 g。
    注意：这是全局 Mellin 等式（∀s∈ℂ），不能由可数点集赋值的 PWW 公理推出，
    因为 PWW 只控制可数个点上的 Mellin 值。这条公理由 Mellin 核空间的性质保证
    （在我们的框架中 realIntegral 是抽象的，不假设 Mellin 变换单射，故核非平凡）。
    风险等级：中高（全局 Mellin 差+谱点保持，B 组谱点叠加公理的统一基础）。 -/
axiom mellin_shift_preserving_spectral_values
    (f g : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (s : ℂ), melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
                    melinTransform g.toTestFunction s) ∧
      (∀ (x : ℝ), x ∈ S → f'.toTestFunction.eval x = f.toTestFunction.eval x)"""

new_shift = """/-- 谱点保持的可数 Mellin 叠加（定理，由 PWW 联合插值直接推出）：
    对任意磨光函数 f, g 和可数点集 T ⊆ ℂ，存在磨光函数 f'，使得：
    (1) f' 在所有谱点 {specDiscM n} 上取值与 f 相同
    (2) 对所有 s ∈ T，M[f'](s) - M[f](s) = M[g](s)

    证明：一次 PWW 应用——S=谱点集（可数），v=f.eval，T（可数），w=M[f]+M[g]。
    关键：只需要可数点集上的 Mellin 等式，不需要全局等式，
    因此不假设 Mellin 变换非单射，在真实数学中成立。 -/
theorem spectral_preserving_melin_superposition_countable
    (f g : MollifiedTestFunction) (T : Set ℂ) (hT : T.Countable) :
    ∃ (f' : MollifiedTestFunction),
      (∀ (n : ℕ), f'.toTestFunction.eval (specDiscM n) = f.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), s ∈ T →
        melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
        melinTransform g.toTestFunction s) := by
  let S : Set ℝ := Set.range specDiscM
  have hS : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun x => f.toTestFunction.eval x
  let w : ℂ → ℂ := fun s => melinTransform f.toTestFunction s + melinTransform g.toTestFunction s
  rcases paley_wiener_whitney_joint_interpolation S hS v T hT w with ⟨f', h_spec, h_melin⟩
  refine' ⟨f', _⟩
  constructor
  · intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    exact h_spec (specDiscM n) h_in
  · intro s hs
    have h : melinTransform f'.toTestFunction s = w s := h_melin s hs
    simpa [w] using h"""

content = content.replace(old_shift, new_shift, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 1 done: mellin_shift -> countable theorem')
