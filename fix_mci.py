f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 可数集上的 Mellin 任意赋值（公理，Paley-Wiener 插值理论核心）：
    对任意可数点集 S ⊆ ℂ 和任意赋值函数 v : ℂ → ℂ，
    存在磨光函数 f，使得 M[f](s) = v(s) 对所有 s ∈ S。

    数学依据：紧支光滑函数的 Mellin 变换像空间是速降整函数空间（Paley-Wiener 定理），
    在可数离散点集上可以任意指定取值。这是 Weierstrass 插值定理在 Paley-Wiener 空间的版本。
    磨光函数的支集分离和椭圆项消失约束不改变无限维本质（椭圆类有限，仅有限约束）。
    风险等级：中高（Paley-Wiener 空间的满插值性质，标准泛函分析结果但证明非平凡）。 -/
axiom mellin_countable_interpolation (S : Set ℂ) (hS : S.Countable) (v : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ S → melinTransform f.toTestFunction s = v s"""

new = """/-- 可数集上 Mellin 变换任意赋值（定理，由 PWW 联合插值取 S=∅ 推出）：
    对任意可数集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在磨光函数 f，使得
    M[f](s) = w(s) 对所有 s ∈ T。 -/
theorem mellin_countable_interpolation (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s := by
  rcases paley_wiener_whitney_joint_interpolation (∅ : Set ℝ) Set.countable_empty (fun _ => 0) T hT w with ⟨f, _, h_melin⟩
  exact ⟨f, h_melin⟩"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: mellin_countable_interpolation -> theorem')
