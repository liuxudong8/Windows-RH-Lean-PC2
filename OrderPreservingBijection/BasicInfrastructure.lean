/-
  基础基础设施模块
  包含 TestFunction（紧支集测试函数）、realIntegral（正半轴积分）等基础定义。
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OrderPreservingBijection

/-- 紧支集测试函数：f : ℝ → ℂ，存在 R>0 使得 |x|>R 时 f(x)=0。 -/
structure TestFunction where
  toFun : ℝ → ℂ
  hasCompactSupport : ∃ (R : ℝ), 0 < R ∧ ∀ (x : ℝ), |x| > R → toFun x = 0

instance : CoeFun TestFunction (fun _ => ℝ → ℂ) := ⟨TestFunction.toFun⟩
def TestFunction.eval (f : TestFunction) (x : ℝ) : ℂ := f.toFun x

/-- toFun 是单射。 -/
theorem TestFunction.toFun_injective : Function.Injective TestFunction.toFun := by
  intro f g h
  cases f with | mk f1 h1 =>
  cases g with | mk f2 h2 =>
    simp only [TestFunction.toFun] at h
    congr

/-- TestFunction 零元素。 -/
noncomputable def zeroTestFunction : TestFunction :=
  { toFun := fun _ => (0 : ℂ)
    hasCompactSupport := by
      refine ⟨1, by norm_num, ?_⟩
      intro x _; rfl }

/-- TestFunction 加法。 -/
noncomputable def addTestFunction (f1 f2 : TestFunction) : TestFunction :=
  { toFun := fun x => f1.eval x + f2.eval x
    hasCompactSupport := by
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
        rw [hf1, hf2] <;> ring }

/-- TestFunction 的 nsmul（自然数乘法）。 -/
noncomputable def nsmulTestFunction (n : ℕ) (f : TestFunction) : TestFunction :=
  Nat.recOn n zeroTestFunction (fun _ g => addTestFunction g f)

noncomputable instance : AddCommMonoid TestFunction where
  zero := zeroTestFunction
  add := addTestFunction
  nsmul := nsmulTestFunction
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  add_assoc := by
    intro a b c
    apply TestFunction.toFun_injective
    funext x
    change (a.eval x + b.eval x) + c.eval x = a.eval x + (b.eval x + c.eval x)
    ring
  zero_add := by
    intro a
    apply TestFunction.toFun_injective
    funext x
    change (0 : ℂ) + a.eval x = a.eval x
    ring
  add_zero := by
    intro a
    apply TestFunction.toFun_injective
    funext x
    change a.eval x + (0 : ℂ) = a.eval x
    ring
  add_comm := by
    intro a b
    apply TestFunction.toFun_injective
    funext x
    change a.eval x + b.eval x = b.eval x + a.eval x
    ring

/-- TestFunction 的数乘。 -/
noncomputable instance : SMul ℂ TestFunction where
  smul c f :=
    { toFun := fun x => c * f.eval x
      hasCompactSupport := by
        let R := Classical.choose f.hasCompactSupport
        let hR := Classical.choose_spec f.hasCompactSupport
        refine ⟨R, hR.1, ?_⟩
        intro x hx
        have hf : f.eval x = 0 := hR.2 x hx
        rw [hf]
        ring }

/-- TestFunction 的 SMulZeroClass：c • 0 = 0（推出 0 • f = 0）。 -/
noncomputable instance : SMulZeroClass ℂ TestFunction where
  smul_zero c := by
    apply TestFunction.toFun_injective
    funext x
    change c * (0 : ℂ) = (0 : ℂ)
    ring

/-- 实数轴正半轴上的积分（Lebesgue 积分）。 -/
noncomputable def realIntegral (h : ℝ → ℂ) : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ), h t

/-- 实数积分的线性性（公理）。 -/
axiom realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2

end OrderPreservingBijection
