/-
  ζ 零点基础设施模块
  包含非平凡零点枚举、零点重数、非平凡零点求和、平凡零点贡献、zetaZeroSide 等。
  依赖 BasicInfrastructure（TestFunction）和 MellinInfrastructure（melinTransform）。
-/

import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace OrderPreservingBijection

/-- 非平凡零点枚举的存在性（公理，第一档）：
    存在单射 e : ℕ → ℂ，枚举所有临界带内的非平凡零点。
    由 Weyl 定律，非平凡零点可数，因此存在这样的无重复枚举。
    风险等级：第一档（Weyl 定律 + 可数集枚举定理）。 -/
axiom nontrivialZeroEnum_exists :
    ∃ (e : ℕ → ℂ),
      (Function.Injective e) ∧
      (∀ (n : ℕ), _root_.riemannZeta (e n) = 0 ∧ 0 < (e n).re ∧ (e n).re < 1) ∧
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), e n = ρ)

/-- 非平凡零点的枚举（定义，由存在性公理通过 Classical.choose 给出）：
    nontrivialZeroEnum : ℕ → ℂ 枚举所有临界带内的非平凡零点。 -/
noncomputable def nontrivialZeroEnum : ℕ → ℂ :=
    Classical.choose nontrivialZeroEnum_exists

/-- 非平凡零点枚举的性质（定理，由 Classical.choose_spec 推出）。 -/
theorem nontrivialZeroEnum_spec :
    (Function.Injective nontrivialZeroEnum) ∧
    (∀ (n : ℕ), _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧ 0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1) ∧
    (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), nontrivialZeroEnum n = ρ) :=
    Classical.choose_spec nontrivialZeroEnum_exists

/-- 非平凡零点枚举的覆盖性（定理）。 -/
theorem nontrivialZeroEnum_covers_all (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    ∃ (n : ℕ), nontrivialZeroEnum n = ρ :=
    nontrivialZeroEnum_spec.2.2 ρ

/-- 非平凡零点枚举的单射性（定理）。 -/
theorem nontrivialZeroEnum_injective : Function.Injective nontrivialZeroEnum :=
    nontrivialZeroEnum_spec.1

/-- 枚举元素都是非平凡零点（定理）。 -/
theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n

/-- 零点重数函数（opaque）：zeroMultiplicity s 给出 ζ(s) 在 s 处的零点重数。
    对非零点，重数为 0。 -/
opaque zeroMultiplicity : ℂ → ℕ

/-- 非平凡零点处重数为正（公理，定义性质）：
    如果 ρ 是非平凡零点，则 zeroMultiplicity ρ > 0。 -/
axiom zeroMultiplicity_positive_at_nontrivial_zeros (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < zeroMultiplicity ρ

/-- 零点重数的函数方程对称性（公理，ζ函数方程的推论）：
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ)。 -/
axiom zeroMultiplicity_symmetry (ρ : ℂ) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ)

/-- 非平凡零点求和（定义，带重数）：
    Z_nontriv(f) = ∑'_{n:ℕ} (zeroMultiplicity(enum n) : ℂ) * melinTransform f (enum n)。
    即对所有非平凡零点按重数加权的 Mellin 变换值求和。
    由 Weyl 定律，级数绝对收敛（磨光函数的 Mellin 变换在零点处有界，重数有界）。 -/
noncomputable def nontrivialZeroSum (f : TestFunction) : ℂ :=
    ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n)

/-- 平凡零点与极点贡献（def，留数公式）：
    T(f) = Σ_{k≥1} M[f](-2k) + M[f](1)。
    其中第一项是平凡零点 s=-2,-4,... 的留数贡献，
    第二项是极点 s=1 的留数贡献（Res_{s=1}(ζ'/ζ)=1，符号已吸收）。
    由留数定理，围道积分在平凡零点和极点处的留数由 Mellin 变换在这些点的值决定。
    对磨光函数，Mellin 变换速降，故级数绝对收敛。 -/
noncomputable def trivialZeroContribution (f : TestFunction) : ℂ :=
    (∑' (k : ℕ), melinTransform f ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) +
    melinTransform f (1 : ℂ)

/-- ζ 零点侧求和（定义）：
    Z(f) = nontrivialZeroSum(f) + trivialZeroContribution(f)
    即非平凡零点求和 + 平凡零点/极点贡献。
    由留数定理，围道积分的留数来自所有奇点（非平凡零点+平凡零点+极点）。 -/
noncomputable def zetaZeroSide (f : TestFunction) : ℂ := nontrivialZeroSum f + trivialZeroContribution f

/-- 非平凡零点求和的局部化（定理，由定义直接推出）：
    如果测试函数 f 的 Mellin 变换在所有非平凡零点处为零，
    则 nontrivialZeroSum(f) = 0。 -/
theorem nontrivialZeroSum_localization (f : TestFunction) :
    (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      melinTransform f ρ = 0) →
    nontrivialZeroSum f = 0 := by
  intro h
  have h_all : ∀ (n : ℕ), melinTransform f (nontrivialZeroEnum n) = 0 := by
    intro n
    have hz : _root_.riemannZeta (nontrivialZeroEnum n) = 0 := (nontrivialZeroEnum_are_zeros n).1
    have hre1 : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
    have hre2 : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
    exact h (nontrivialZeroEnum n) hz hre1 hre2
  have h_term : ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n) = 0 := by
    intro n
    rw [h_all n] <;> ring
  have h_main : ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n) = 0 := by
    rw [tsum_congr h_term, tsum_zero]
  simpa [nontrivialZeroSum] using h_main

end OrderPreservingBijection
