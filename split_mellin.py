path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old = """/-- 点插值纤维上的 Mellin 满射性（公理，Paley-Wiener 定理）： -/
axiom mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s)"""

new = """/-- Mellin 变换的可数集满射性（公理，纯 Paley-Wiener 定理）：
    对任意可数点集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在紧支集 TestFunction f
    使得 Mellin 变换 M[f] 在 T 上等于 w。
    这是 Paley-Wiener 定理的直接推论：紧支集函数的 Mellin 变换是整函数，
    且在可数点集上可任意指定取值（函数空间无限维）。
    不涉及点插值约束，是纯分析断言。 -/
axiom mellin_transform_countable_surjectivity
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (h : TestFunction), ∀ (s : ℂ), s ∈ T → melinTransform h s = w s

/-- 点插值纤维的 Mellin 丰富性（公理，磨光函数空间结构性质）：
    对任意磨光函数 f0、可分离可数点集 S、任意 TestFunction h，
    存在磨光函数 f 保持 f0 在 S 上的取值，且 M[f] = M[f0] + M[h]。
    数学含义：点插值约束不减少 Mellin 变换的自由度——
    可以在保持有限/可数个点取值的同时，叠加上任意 TestFunction 的 Mellin 变换。
    这是因为 {g | g|_S=0} 子空间无限维，其 Mellin 变换的像与全空间的像相同。 -/
axiom mollified_point_fiber_mellin_rich
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (h : TestFunction) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (melinTransform f.toTestFunction = melinTransform f0.toTestFunction + melinTransform h)

/-- 点插值纤维上的 Mellin 满射性（定理，由两条更基本公理推出）：
    给定 f0 和可数点集 S（保持 f0 在 S 上的取值），以及可数点集 T 和任意赋值 w，
    存在磨光函数 f 使得 f|_S = f0|_S 且 M[f]|_T = w。
    证明：由 mellin_transform_countable_surjectivity 取 h 使 M[h]|_T = w - M[f0]|_T，
    再由 mollified_point_fiber_mellin_rich 叠加 M[h] 得到 f。 -/
theorem mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  let u : ℂ → ℂ := fun s => w s - melinTransform f0.toTestFunction s
  rcases mellin_transform_countable_surjectivity T hT u with ⟨h, hh⟩
  rcases mollified_point_fiber_mellin_rich f0 S hS h_sep h with ⟨f, h_pts, h_melin_eq⟩
  refine ⟨f, h_pts, ?_⟩
  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    rw [h_melin_eq]
  rw [h1]
  have h2 : melinTransform h s = u s := hh s hs
  rw [h2]
  simp only [u] <;> abel"""

content = content.replace(old, new)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Split mellin_surjectivity into 2 axioms + theorem')
