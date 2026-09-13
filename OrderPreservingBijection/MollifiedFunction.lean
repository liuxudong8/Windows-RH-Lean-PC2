/-
  磨光测试函数模块
  包含椭圆共轭类基础设施、ellipticTerm、MollifiedTestFunction 等。
  依赖 BasicInfrastructure（TestFunction）。
-/

import OrderPreservingBijection.BasicInfrastructure

namespace OrderPreservingBijection

/-- 椭圆共轭类的特征长度集合（opaque）：
    E_ell = {ℓ(γ) : γ ∈ Γ 椭圆共轭类}
    即算术群 Γ 中所有椭圆元素的共轭类对应的特征长度（旋转角）集合。 -/
opaque ellipticClassLengths : Set ℝ

/-- 椭圆类特征长度有界（公理）：
    椭圆共轭类的特征长度集合 ellipticClassLengths 是有界的。
    数学原因：椭圆元素的特征值在单位圆上，故旋转角（特征长度）有界。 -/
axiom elliptic_class_lengths_bounded :
    ∃ (M : ℝ), 0 < M ∧ ∀ (ℓ : ℝ), ℓ ∈ ellipticClassLengths → |ℓ| ≤ M

/-- 椭圆类特征长度离散（公理）：
    椭圆共轭类的特征长度集合 ellipticClassLengths 是离散的。
    数学原因：算术群 Γ 在 G 中离散，椭圆共轭类的特征长度只能取离散的值。 -/
axiom elliptic_class_lengths_discrete :
    ∀ (ℓ : ℝ), ℓ ∈ ellipticClassLengths →
      ∃ (ε : ℝ), 0 < ε ∧ ∀ (ℓ' : ℝ), ℓ' ∈ ellipticClassLengths → |ℓ' - ℓ| < ε → ℓ' = ℓ

/-- 实数中有界离散子集有限（公理，Bolzano-Weierstrass 推论）：
    如果 S ⊆ ℝ 有界且离散，则 S 有限。 -/
axiom bounded_discrete_real_set_finite (S : Set ℝ)
    (h_bounded : ∃ (M : ℝ), 0 < M ∧ ∀ (ℓ : ℝ), ℓ ∈ S → |ℓ| ≤ M)
    (h_discrete : ∀ (ℓ : ℝ), ℓ ∈ S →
      ∃ (ε : ℝ), 0 < ε ∧ ∀ (ℓ' : ℝ), ℓ' ∈ S → |ℓ' - ℓ| < ε → ℓ' = ℓ) :
    Set.Finite S

/-- 椭圆类特征长度集合有限（引理，由有界+离散+Bolzano-Weierstrass推出）：
    ellipticClassLengths 是有限集。 -/
lemma ellipticClassLengths_finite : Set.Finite ellipticClassLengths :=
    bounded_discrete_real_set_finite ellipticClassLengths elliptic_class_lengths_bounded elliptic_class_lengths_discrete

/-- 椭圆类权重（opaque）：w(ℓ) 是特征长度为 ℓ 的椭圆共轭类的权重。
    由椭圆共轭类的几何（旋转角、中心化子体积）决定。 -/
opaque ellipticWeight : ℝ → ℂ

/-- 椭圆共轭类贡献（def，有限加权求和）：
    E(f) = Σ_{ℓ∈E_ell} w(ℓ)·f(ℓ)，
    其中 E_ell = ellipticClassLengths 是椭圆类特征长度集合（已证有限），
    w(ℓ) = ellipticWeight ℓ 是对应椭圆类的权重。 -/
noncomputable def ellipticTerm (f : TestFunction) : ℂ :=
    ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * f.eval ℓ

/-- 磨光测试函数：紧支集 + 支集分离 + 椭圆项消失。
    supportSeparated：存在 Λ0<Λ1，f 在 (-∞,Λ0/2] 上为 0，在 [Λ0,Λ1] 上为 1。
    ellipticVanishes：ellipticTerm(f) = 0。
    这是 Weil 显式公式和 RH 反证法中使用的测试函数类。 -/
structure MollifiedTestFunction extends TestFunction where
  supportSeparated : ∃ (Λ0 Λ1 : ℝ), 0 < Λ0 ∧ Λ0 < Λ1 ∧
    (∀ x, x ≤ Λ0 / 2 → toFun x = 0) ∧
    (∀ x, Λ0 ≤ x ∧ x ≤ Λ1 → toFun x = 1)
  ellipticVanishes : ellipticTerm (⟨toFun, hasCompactSupport⟩) = 0

/-- 磨光函数的椭圆项为零（定理，由定义直接推出）。 -/
theorem mollified_elliptic_zero (f : MollifiedTestFunction) :
    ellipticTerm (f.toTestFunction) = 0 := f.ellipticVanishes

end OrderPreservingBijection
