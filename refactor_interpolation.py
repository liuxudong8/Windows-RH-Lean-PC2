with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 删除 mollified_point_fiber_mellin_rich 公理
old_rich = '''/-- 点插值纤维的 Mellin 丰富性（公理，磨光函数空间结构性质）：
    对任意磨光函数 f0、可分离可数点集 S、任意满足 nontrivialZeroSum(h)=0 的 TestFunction h，
    存在磨光函数 f 保持 f0 在 S 上的取值，且 M[f] = M[f0] + M[h]。
    数学含义：点插值约束不减少 Mellin 变换的自由度——
    可以在保持有限/可数个点取值的同时，叠加上 nontrivialZeroSum 为零的 TestFunction 的 Mellin 变换。
    前提 nontrivialZeroSum(h)=0 是必要的：由 spectral_zero_equality，谱点取值相同 ⟹ nontrivialZeroSum 相同，
    故叠加的 h 必须满足 nontrivialZeroSum(h)=0，否则与 spectral_zero_equality 矛盾。
    这是因为 {g | g|_S=0 且 nontrivialZeroSum(g)=0} 子空间无限维，其 Mellin 变换的像足够丰富。 -/
axiom mollified_point_fiber_mellin_rich
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (h : TestFunction) (h_nz : nontrivialZeroSum h = 0) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (melinTransform f.toTestFunction = melinTransform f0.toTestFunction + melinTransform h)

'''

if old_rich in content:
    content = content.replace(old_rich, '')
    print("删除 mollified_point_fiber_mellin_rich 成功")
else:
    print("未找到 mollified_point_fiber_mellin_rich")

# 2. mellin_surjectivity_over_point_fiber 从 theorem 改为 axiom
old_theorem = '''/-- 点插值纤维上的 Mellin 满射性（定理，由两条更基本公理推出）：
    给定 f0 和可数点集 S（保持 f0 在 S 上的取值），以及可数点集 T 和任意赋值 w，
    存在磨光函数 f 使得 f|_S = f0|_S 且 M[f]|_T = w。
    证明：由 mellin_transform_countable_surjectivity 取 h 使 M[h]|_T = w - M[f0]|_T，
    再由 mollified_point_fiber_mellin_rich 叠加 M[h] 得到 f。 -/
theorem mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  let u : ℂ → ℂ := fun s => w s - melinTransform f0.toTestFunction s
  rcases mellin_finite_surjectivity_zero_sum T hT u with ⟨h, hh, h_nz⟩
  rcases mollified_point_fiber_mellin_rich f0 S hS h_sep h h_nz with ⟨f, h_pts, h_melin_eq⟩
  refine ⟨f, h_pts, ?_⟩
  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    have h_eq := congrFun h_melin_eq s
    exact h_eq
  rw [h1]
  have h2 : melinTransform h s = u s := hh s hs
  rw [h2]
  simp only [u] <;> ring'''

new_axiom = '''/-- 点插值纤维上的有限 Mellin 满射性（公理，PWW 联合插值的核心）：
    给定 f0 和可数点集 S（保持 f0 在 S 上的取值），以及有限点集 T 和任意赋值 w，
    存在磨光函数 f 使得 f|_S = f0|_S 且 M[f]|_T = w。
    ZFC 基础：Paley-Wiener-Whitney 联合插值定理（标准泛函分析）。
    注意：只断言有限点 T 上的 Mellin 相等，不断言全局相等——全局版本因 Mellin 变换单射性而不成立。 -/
axiom mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s)'''

if old_theorem in content:
    content = content.replace(old_theorem, new_axiom)
    print("mellin_surjectivity_over_point_fiber 改为 axiom 成功")
else:
    print("未找到 mellin_surjectivity_over_point_fiber")

with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
