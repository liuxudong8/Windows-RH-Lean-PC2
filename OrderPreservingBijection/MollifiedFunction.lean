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

/-- 椭圆类特征长度集合有限（公理，数论事实）：
    ellipticClassLengths 是有限集。
    数学原因：算术群 Γ 中椭圆元素的阶有界，故旋转角只能取有限个值。
    注意：不能通过"有界+离散→有限"推出，反例 {1/n}。 -/
axiom ellipticClassLengths_finite : Set.Finite ellipticClassLengths

/-- 椭圆类权重（opaque）：w(ℓ) 是特征长度为 ℓ 的椭圆共轭类的权重。
    由椭圆共轭类的几何（旋转角、中心化子体积）决定。 -/
opaque ellipticWeight : ℝ → ℂ

/-- 椭圆共轭类贡献（def，有限加权求和）：
    E(f) = Σ_{ℓ∈E_ell} w(ℓ)·f(ℓ)，
    其中 E_ell = ellipticClassLengths 是椭圆类特征长度集合（已证有限），
    w(ℓ) = ellipticWeight ℓ 是对应椭圆类的权重。 -/
noncomputable def ellipticTerm (f : TestFunction) : ℂ :=
    ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * f.eval ℓ

/-- 磨光测试函数：紧支集 + 支集有界 + 椭圆项消失。
    supportBounded：存在 ε₀, R₀ > 0，f 在 (-∞, ε₀] 和 [R₀, ∞) 上为 0。
    ellipticVanishes：ellipticTerm(f) = 0。
    这是 Weil 显式公式和 RH 反证法中使用的测试函数类。 -/
structure MollifiedTestFunction extends TestFunction where
  supportBounded : ∃ (ε₀ R₀ : ℝ), 0 < ε₀ ∧ ε₀ < R₀ ∧
    (∀ x, x ≤ ε₀ → toFun x = 0) ∧
    (∀ x, x ≥ R₀ → toFun x = 0)
  ellipticVanishes : ellipticTerm (⟨toFun, hasCompactSupport, isBounded, vanishesNearZero, measurable⟩) = 0

/-- 磨光函数的椭圆项为零（定理，由定义直接推出）。 -/
theorem mollified_elliptic_zero (f : MollifiedTestFunction) :
    ellipticTerm (f.toTestFunction) = 0 := f.ellipticVanishes

/-- 磨光函数的标量乘法实例：k • f 仍是磨光函数。 -/
noncomputable instance : SMul ℂ MollifiedTestFunction where
  smul k f :=
    { toTestFunction := k • f.toTestFunction
      supportBounded := by
        rcases f.supportBounded with ⟨ε₀, R₀, hε₀_pos, hε₀_lt_R₀, h_left, h_right⟩
        refine ⟨ε₀, R₀, hε₀_pos, hε₀_lt_R₀, ?_, ?_⟩
        · intro x hx
          have h : f.eval x = 0 := h_left x hx
          have h2 : (k • f.toTestFunction).toFun x = k * f.eval x := by rfl
          have h3 : (k • f.toTestFunction).toFun x = 0 := by
            calc
              (k • f.toTestFunction).toFun x
                = k * f.eval x := h2
              _ = k * 0 := by rw [h]
              _ = 0 := by ring
          exact h3
        · intro x hx
          have h : f.eval x = 0 := h_right x hx
          have h2 : (k • f.toTestFunction).toFun x = k * f.eval x := by rfl
          have h3 : (k • f.toTestFunction).toFun x = 0 := by
            calc
              (k • f.toTestFunction).toFun x
                = k * f.eval x := h2
              _ = k * 0 := by rw [h]
              _ = 0 := by ring
          exact h3
      ellipticVanishes := by
        have h1 : ∀ (g : TestFunction), ellipticTerm (k • g) = k * ellipticTerm g := by
          intro g
          have h2 : ellipticTerm (k • g) = ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * (k • g).eval ℓ := by
            rfl
          rw [h2]
          have h3 : ∀ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * (k • g).eval ℓ = k * (ellipticWeight ℓ * g.eval ℓ) := by
            intro ℓ _
            have h4 : (k • g).eval ℓ = k * g.eval ℓ := by rfl
            rw [h4] <;> ring
          have h5 : ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * (k • g).eval ℓ =
              ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, k * (ellipticWeight ℓ * g.eval ℓ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact h3 ℓ hℓ
          rw [h5]
          have h6 : ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, k * (ellipticWeight ℓ * g.eval ℓ) =
              k * ∑ ℓ ∈ ellipticClassLengths_finite.toFinset, ellipticWeight ℓ * g.eval ℓ := by
            rw [Finset.mul_sum]
          rw [h6]
          <;> rfl
        have h : ellipticTerm (k • f.toTestFunction) = k * ellipticTerm f.toTestFunction := h1 f.toTestFunction
        rw [h, f.ellipticVanishes] <;> ring
    }

end OrderPreservingBijection
