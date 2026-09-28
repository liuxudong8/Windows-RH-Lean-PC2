/-
  ζ 零点基础设施模块
-/

import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order

namespace OrderPreservingBijection

theorem nontrivialZeroEnum_exists :
    ∃ (e : ℕ → ℂ),
      (Function.Injective e) ∧
      (∀ (n : ℕ), _root_.riemannZeta (e n) = 0 ∧ 0 < (e n).re ∧ (e n).re < 1) ∧
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), e n = ρ) := by
  let S : Set ℂ := riemannZetaZeros ∩ {s | 0 < s.re ∧ s.re < 1}
  have hS_count : S.Countable := by
    have h1 : ∀ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)).Finite := by
      intro N
      have h_comp : IsCompact (Metric.closedBall (0:ℂ) (N:ℝ)) := by exact?
      have h : (Metric.closedBall (0:ℂ) (N:ℝ) ∩ riemannZetaZeros).Finite :=
        h_comp.inter_riemannZetaZeros_finite
      have hsub : (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)) ⊆
          (Metric.closedBall (0:ℂ) (N:ℝ) ∩ riemannZetaZeros) := by
        intro z hz; exact ⟨hz.2, hz.1.1⟩
      exact h.subset hsub
    have h2 : S = ⋃ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)) := by
      ext z; simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hz; obtain ⟨N, hN⟩ := exists_nat_ge (‖z‖)
        exact ⟨N, hz, by simpa [Metric.mem_closedBall] using hN⟩
      · rintro ⟨N, hz, _⟩; exact hz
    rw [h2]
    exact Set.countable_iUnion (fun N => (h1 N).countable)
  sorry

noncomputable def nontrivialZeroEnum : ℕ → ℂ := Classical.choose nontrivialZeroEnum_exists

theorem nontrivialZeroEnum_spec :
    (Function.Injective nontrivialZeroEnum) ∧
    (∀ (n : ℕ), _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧ 0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1) ∧
    (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), nontrivialZeroEnum n = ρ) :=
    Classical.choose_spec nontrivialZeroEnum_exists

theorem nontrivialZeroEnum_covers_all (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    ∃ (n : ℕ), nontrivialZeroEnum n = ρ :=
    nontrivialZeroEnum_spec.2.2 ρ

theorem nontrivialZeroEnum_injective : Function.Injective nontrivialZeroEnum :=
    nontrivialZeroEnum_spec.1

theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n

theorem riemannZeta_neg_on_Ioo (x : ℝ) (hx1 : 0 < x) (hx2 : x < 1) :
    (riemannZeta x).re < 0 := by sorry

theorem nontrivialZero_im_ne_zero (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.im ≠ 0 := by
  intro hz hre1 hre2 him
  have h_re : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [h_re] at hz
  have h_neg : (riemannZeta (ρ.re : ℂ)).re < 0 := riemannZeta_neg_on_Ioo ρ.re hre1 hre2
  rw [hz] at h_neg <;> norm_num at h_neg

noncomputable def zeroMultiplicity (s : ℂ) : ℕ :=
    _root_.analyticOrderNatAt _root_.riemannZeta s

theorem zeroMultiplicity_positive_at_nontrivial_zeros (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < zeroMultiplicity ρ := by
  intro hz hre1 hre2
  have hne1 : ρ ≠ 1 := by
    intro h; rw [h] at hre2; norm_num at hre2
  have h_analytic : AnalyticAt ℂ _root_.riemannZeta ρ :=
    _root_.analyticOn_riemannZeta ρ hne1
  have h_order_ne_zero : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ 0 :=
    h_analytic.analyticOrderAt_ne_zero.mpr hz
  have h_order_ne_top : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ ⊤ := by sorry
  have h_goal : zeroMultiplicity ρ ≠ 0 := by
    have h_eq : (zeroMultiplicity ρ : ℕ∞) = _root_.analyticOrderAt _root_.riemannZeta ρ := by
      simpa [zeroMultiplicity, _root_.analyticOrderNatAt] using Nat.cast_analyticOrderNatAt h_order_ne_top
    intro h
    apply h_order_ne_zero
    rw [← h_eq, h] <;> norm_num
  exact Nat.pos_of_ne_zero h_goal

theorem zeroMultiplicity_symmetry (ρ : ℂ)
    (_ : _root_.riemannZeta ρ = 0) (hre1 : 0 < ρ.re) (hre2 : ρ.re < 1) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by sorry

noncomputable def nontrivialZeroSum (f : TestFunction) : ℂ :=
    ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n)

noncomputable def trivialZeroContribution (f : TestFunction) : ℂ :=
    (∑' (k : ℕ), melinTransform f ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) +
    melinTransform f (1 : ℂ)

noncomputable def zetaZeroSide (f : TestFunction) : ℂ :=
    nontrivialZeroSum f + trivialZeroContribution f

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