with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_axiom = '''/-- 点插值纤维的 Mellin 丰富性（公理，磨光函数空间结构性质）：
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
      (melinTransform f.toTestFunction = melinTransform f0.toTestFunction + melinTransform h)'''

new_axiom = '''/-- 点插值纤维的有限 Mellin 丰富性（公理，磨光函数空间结构性质）：
    对任意磨光函数 f0、可分离可数点集 S、任意满足 nontrivialZeroSum(h)=0 的 TestFunction h，
    以及任意有限复点集 T，存在磨光函数 f 保持 f0 在 S 上的取值，且 M[f]|_T = (M[f0]+M[h])|_T。
    数学含义：点插值约束不减少有限点上的 Mellin 变换自由度——
    可以在保持可数个点取值的同时，在有限个复点上叠加上 nontrivialZeroSum 为零的 TestFunction 的 Mellin 变换。
    前提 nontrivialZeroSum(h)=0 是必要的：由 spectral_zero_equality，谱点取值相同 ⟹ nontrivialZeroSum 相同，
    故叠加的 h 必须满足 nontrivialZeroSum(h)=0，否则与 spectral_zero_equality 矛盾。
    ZFC 基础：有限维插值 + 支集分离约束下的磨光函数空间丰富性（标准泛函分析）。
    注意：只断言有限点 T 上的相等，不断言全局 Mellin 相等——全局版本过强且非必要。 -/
axiom mollified_point_fiber_mellin_rich
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (h : TestFunction) (h_nz : nontrivialZeroSum h = 0)
    (T : Set ℂ) (hT : T.Finite) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s)'''

if old_axiom in content:
    content = content.replace(old_axiom, new_axiom)
    print("公理修改成功")
else:
    print("未找到旧公理")

# 修改 mellin_surjectivity_over_point_fiber 中的调用
old_call = '''  rcases mollified_point_fiber_mellin_rich f0 S hS h_sep h h_nz with ⟨f, h_pts, h_melin_eq⟩
  refine ⟨f, h_pts, ?_⟩
  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    have h_eq := congrFun h_melin_eq s
    exact h_eq
  rw [h1]'''

new_call = '''  rcases mollified_point_fiber_mellin_rich f0 S hS h_sep h h_nz T hT with ⟨f, h_pts, h_melin_eq⟩
  refine ⟨f, h_pts, ?_⟩
  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := h_melin_eq s hs
  rw [h1]'''

if old_call in content:
    content = content.replace(old_call, new_call)
    print("调用修改成功")
else:
    print("未找到旧调用")

with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
