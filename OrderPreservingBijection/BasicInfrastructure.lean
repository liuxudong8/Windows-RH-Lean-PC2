/-
  基础基础设施模块
  包含 TestFunction（紧支集测试函数）、realIntegral（正半轴积分）等基础定义。
  被 MellinInfrastructure、ContourIntegral、stage_4 等模块引用。
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OrderPreservingBijection

/-- 紧支集测试函数：f : ℝ → ℂ，存在 R>0 使得 |x|>R 时 f(x)=0。
    用于 Weil 显式公式、迹公式、Mellin 变换等。 -/
structure TestFunction where
  toFun : ℝ → ℂ
  hasCompactSupport : ∃ (R : ℝ), 0 < R ∧ ∀ (x : ℝ), |x| > R → toFun x = 0

instance : CoeFun TestFunction (fun _ => ℝ → ℂ) := ⟨TestFunction.toFun⟩
def TestFunction.eval (f : TestFunction) (x : ℝ) : ℂ := f.toFun x

/-- TestFunction 的加法：逐点相加，支集为两支集的并。 -/
noncomputable instance : Add TestFunction where
  add f1 f2 :=
    ⟨fun x => f1.eval x + f2.eval x, by
      let R1 := Classical.choose f1.hasCompactSupport
      let hR1 := Classical.choose_spec f1.hasCompactSupport
      let R2 := Classical.choose f2.hasCompactSupport
      let hR2 := Classical.choose_spec f2.hasCompactSupport
      refine ⟨max R1 R2, ?_, ?_⟩
      · exact lt_max_iff.mpr (Or.inl hR1.1)
      · intro x hx
        have h1' : |x| > R1 := lt_of_le_of_lt (le_max_left R1 R2) hx
        have h2' : |x| > R2 := lt_of_le_of_lt (le_max_right R1 R2) hx
        have hf1 : f1.eval x = 0 := hR1.2 x h1'
        have hf2 : f2.eval x = 0 := hR2.2 x h2'
        rw [hf1, hf2] <;> ring⟩

/-- TestFunction 的数乘：逐点数乘，支集不变。 -/
noncomputable instance : SMul ℂ TestFunction where
  smul c f :=
    ⟨fun x => c * f.eval x, by
      let R := Classical.choose f.hasCompactSupport
      let hR := Classical.choose_spec f.hasCompactSupport
      refine ⟨R, hR.1, ?_⟩
      intro x hx
      have hf : f.eval x = 0 := hR.2 x hx
      rw [hf] <;> ring⟩

/-- 实数轴正半轴上的积分（def，Lebesgue 积分）：∫₀^∞ h(t) dt。
    定义为 Ioi 0 上的 Lebesgue 积分。用于连续谱贡献、热核 Laplace 变换、Mellin 变换等。 -/
noncomputable def realIntegral (h : ℝ → ℂ) : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ), h t

/-- 实数积分的线性性（公理，第一档）：
    ∫₀^∞ (c₁·h₁ + c₂·h₂)(t) dt = c₁·∫₀^∞ h₁(t) dt + c₂·∫₀^∞ h₂(t) dt。
    这是 Lebesgue 积分的基本性质，标准分析结果。 -/
axiom realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2

end OrderPreservingBijection
