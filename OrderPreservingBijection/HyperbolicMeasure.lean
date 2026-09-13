/-
HyperbolicMeasure.lean
双曲空间测度与积分的显式形式化。

目标：将 manifoldIntegral 从 opaque 降级为关于双曲测度的 Bochner 积分。
- ℍ³ 上半空间：dμ₃ = dx dy dt / t³
- ℍ² 上半平面：dμ₂ = dx dy / y²

构造方式：
1. 母空间 ℂ×ℝ / ℂ 上的 Lebesgue 测度 volume
2. 经 comap 限制到子类型 ℍ³ / ℍ²
3. 用 withDensity 乘以密度 1/t³ / 1/y²
-/

import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory MeasureTheory.Measure

namespace OrderPreservingBijection

/-- ℍ³ 上半空间：{p : ℂ × ℝ // 0 < p.2}。
    第一个分量 ℂ 对应 (x, y)，第二个分量 ℝ 对应 t > 0。 -/
abbrev UpperHalfSpace3 : Type := {p : ℂ × ℝ // 0 < p.2}

/-- ℍ² 上半平面：{z : ℂ // 0 < z.im}。 -/
abbrev UpperHalfPlane : Type := {z : ℂ // 0 < z.im}

/-- ℍ³ 上的双曲测度：dμ₃ = dx dy dt / t³。
    构造：ℂ×ℝ 上的 volume 经 comap 限制到 ℍ³，再 withDensity 乘以 1/t³。 -/
noncomputable def hyperbolicMeasure3 : Measure UpperHalfSpace3 :=
  (comap (Subtype.val : UpperHalfSpace3 → ℂ × ℝ) (volume : Measure (ℂ × ℝ)))
    |>.withDensity (fun p : UpperHalfSpace3 => ENNReal.ofReal (1 / (p.val.2)^3))

/-- ℍ² 上的双曲测度：dμ₂ = dx dy / y²。
    构造：ℂ 上的 volume 经 comap 限制到 ℍ²，再 withDensity 乘以 1/y²。 -/
noncomputable def hyperbolicMeasure2 : Measure UpperHalfPlane :=
  (comap (Subtype.val : UpperHalfPlane → ℂ) (volume : Measure ℂ))
    |>.withDensity (fun z : UpperHalfPlane => ENNReal.ofReal (1 / (z.val.im)^2))

/-- ℍ³ 上的 Bochner 积分：∫_{ℍ³} f dμ₃。 -/
noncomputable def hyperbolicIntegral3 (f : UpperHalfSpace3 → ℂ) : ℂ :=
  integral hyperbolicMeasure3 f

/-- ℍ² 上的 Bochner 积分：∫_{ℍ²} f dμ₂。 -/
noncomputable def hyperbolicIntegral2 (f : UpperHalfPlane → ℂ) : ℂ :=
  integral hyperbolicMeasure2 f

end OrderPreservingBijection
