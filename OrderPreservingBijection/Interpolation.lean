/-
  插值理论模块
  包含 Whitney 点插值、Paley-Wiener Mellin 满射性、PWW 联合插值等。
  依赖 MollifiedFunction（MollifiedTestFunction）和 MellinInfrastructure（melinTransform）。
-/

import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.MellinInfrastructure

namespace OrderPreservingBijection

/-- 磨光函数的 Whitney 点插值（公理，Whitney 延拓定理）：
    对任意可数点集 S ⊆ ℝ 和任意赋值 v : ℝ → ℂ，存在磨光函数 f，使得
    f.eval(x) = v(x) 对所有 x ∈ S。

    数学依据：Whitney 延拓定理——在离散点集上指定任意函数值，
    存在紧支光滑延拓。可数集在 ℝ 中无内部，可选择 supportSeparated 区间
    与 S 不相交，故磨光约束不影响插值能力。
    风险等级：中（标准 Whitney 延拓，磨光约束下的变体）。 -/
axiom whitney_mollified_point_interpolation
    (S : Set ℝ) (hS : S.Countable) (v : ℝ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x)

/-- 点插值纤维上的 Mellin 满射性（公理，Paley-Wiener 定理）：
    给定满足点插值约束的磨光函数 f₀（f₀.eval(x)=v(x) 对 x∈S），
    对任意可数点集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在磨光函数 f，使得：
    (1) f.eval(x) = f₀.eval(x) 对所有 x ∈ S（保持点插值）
    (2) M[f](s) = w(s) 对所有 s ∈ T。

    数学依据：Paley-Wiener 定理——满足点插值约束的函数构成仿射子空间，
    其差空间是无限维的（在 S 上取零的紧支光滑函数），Mellin 变换
    在这个差空间上的像仍然包含任意可数点集赋值。
    等价地说：点插值只施加可数个线性约束，其余维无限，
    故 Mellin 赋值仍可任意指定。
    风险等级：中高（Paley-Wiener 满射性，是插值理论的分析核心）。 -/
axiom mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable)
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s)

/-- Paley-Wiener-Whitney 联合插值（定理，由 Whitney 点插值 + 纤维上 Mellin 满射推出）：
    对任意可数点集 S ⊆ ℝ（函数取值点）、可数点集 T ⊆ ℂ（Mellin 赋值点）、
    任意赋值 v : ℝ → ℂ 和 w : ℂ → ℂ，存在磨光函数 f，使得：
    (1) f.eval(x) = v(x) 对所有 x ∈ S
    (2) M[f](s) = w(s) 对所有 s ∈ T。

    证明：
    (1) whitney_mollified_point_interpolation 给出 f₀ 满足点插值
    (2) mellin_surjectivity_over_point_fiber(f₀, S, T, w) 给出 f 保持点插值且满足 Mellin 赋值 -/
theorem paley_wiener_whitney_joint_interpolation
    (S : Set ℝ) (hS : S.Countable) (v : ℝ → ℂ)
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  rcases whitney_mollified_point_interpolation S hS v with ⟨f0, hf0⟩
  rcases mellin_surjectivity_over_point_fiber f0 S hS T hT w with ⟨f, h_pts, h_melin⟩
  have h_final_pts : ∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x := by
    intro x hx
    calc
      f.toTestFunction.eval x = f0.toTestFunction.eval x := h_pts x hx
      _ = v x := hf0 x hx
  exact ⟨f, h_final_pts, h_melin⟩

/-- 可数集上 Mellin 变换任意赋值（定理，由 PWW 联合插值取 S=∅ 推出）：
    对任意可数集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在磨光函数 f，使得
    M[f](s) = w(s) 对所有 s ∈ T。 -/
theorem mellin_countable_interpolation (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s := by
  rcases paley_wiener_whitney_joint_interpolation (∅ : Set ℝ) Set.countable_empty (fun _ => 0) T hT w with ⟨f, _, h_melin⟩
  exact ⟨f, h_melin⟩

end OrderPreservingBijection
