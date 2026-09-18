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
  isBounded : ∃ (B : ℝ), 0 < B ∧ ∀ (x : ℝ), ‖toFun x‖ ≤ B
  vanishesNearZero : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : ℝ), x < ε → toFun x = 0
  measurable : Measurable toFun

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
      intro x _; rfl
    isBounded := ⟨1, by norm_num, fun x => by simp⟩
    vanishesNearZero := ⟨1, by norm_num, fun x _ => rfl⟩
    measurable := measurable_const }

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
        rw [hf1, hf2] <;> ring
    isBounded := by
      rcases f1.isBounded with ⟨B1, hB1_pos, hB1⟩
      rcases f2.isBounded with ⟨B2, hB2_pos, hB2⟩
      refine ⟨B1 + B2, by linarith, fun x => ?_⟩
      have h : ‖f1.eval x + f2.eval x‖ ≤ ‖f1.eval x‖ + ‖f2.eval x‖ := norm_add_le _ _
      have h1 : ‖f1.eval x‖ ≤ B1 := hB1 x
      have h2 : ‖f2.eval x‖ ≤ B2 := hB2 x
      calc ‖f1.eval x + f2.eval x‖ ≤ ‖f1.eval x‖ + ‖f2.eval x‖ := h
        _ ≤ B1 + B2 := by linarith
    vanishesNearZero := by
      rcases f1.vanishesNearZero with ⟨ε1, hε1_pos, hε1⟩
      rcases f2.vanishesNearZero with ⟨ε2, hε2_pos, hε2⟩
      refine ⟨min ε1 ε2, by positivity, fun x hx => ?_⟩
      have h1 : x < ε1 := lt_of_lt_of_le hx (min_le_left ε1 ε2)
      have h2 : x < ε2 := lt_of_lt_of_le hx (min_le_right ε1 ε2)
      have hf1 : f1.eval x = 0 := hε1 x h1
      have hf2 : f2.eval x = 0 := hε2 x h2
      rw [hf1, hf2] <;> ring
    measurable := f1.measurable.add f2.measurable }

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
        ring
      isBounded := by
        rcases f.isBounded with ⟨B, hB_pos, hB⟩
        refine ⟨‖c‖ * B + 1, by positivity, fun x => ?_⟩
        have h : ‖c * f.eval x‖ = ‖c‖ * ‖f.eval x‖ := by rw [norm_mul]
        rw [h]
        have h2 : ‖c‖ * ‖f.eval x‖ ≤ ‖c‖ * B := by gcongr <;> exact hB x
        linarith
      vanishesNearZero := by
        rcases f.vanishesNearZero with ⟨ε, hε_pos, hε⟩
        refine ⟨ε, hε_pos, fun x hx => ?_⟩
        have hf : f.eval x = 0 := hε x hx
        rw [hf] <;> ring
      measurable := f.measurable.const_mul c }

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

/-- 实数积分的线性性（定理，由 Bochner 积分线性性推出，需可积性条件）。 -/
theorem realIntegral_linear (h1 h2 : ℝ → ℂ) (c1 c2 : ℂ)
    (h1_int : MeasureTheory.Integrable h1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h2_int : MeasureTheory.Integrable h2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    realIntegral (fun t => c1 * h1 t + c2 * h2 t) = c1 * realIntegral h1 + c2 * realIntegral h2 := by
  let g1 : ℝ → ℂ := fun t => c1 * h1 t
  let g2 : ℝ → ℂ := fun t => c2 * h2 t
  have hg1_int : MeasureTheory.Integrable g1 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [g1] using h1_int.const_mul c1
  have hg2_int : MeasureTheory.Integrable g2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [g2] using h2_int.const_mul c2
  have h_sum : (fun t : ℝ => c1 * h1 t + c2 * h2 t) = g1 + g2 := by
    funext t; simp [g1, g2] <;> ring
  have h_eq1 : realIntegral (fun t => c1 * h1 t + c2 * h2 t) =
      ∫ t, (g1 + g2) t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [h_sum] <;> rfl
  have h_eq2 : realIntegral h1 = ∫ t, h1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by rfl
  have h_eq3 : realIntegral h2 = ∫ t, h2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by rfl
  rw [h_eq1, h_eq2, h_eq3]
  have h4 : ∫ t, (g1 + g2) t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) =
      (∫ t, g1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) + (∫ t, g2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :=
    MeasureTheory.integral_add hg1_int hg2_int
  rw [h4]
  have h5 : ∫ t, g1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) = c1 * (∫ t, h1 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h51 : g1 = fun t => c1 * h1 t := by rfl
    rw [h51]
    exact?
  have h6 : ∫ t, g2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) = c2 * (∫ t, h2 t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h61 : g2 = fun t => c2 * h2 t := by rfl
    rw [h61]
    exact?
  rw [h5, h6] <;> ring

end OrderPreservingBijection
