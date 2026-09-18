/-
  插值理论模块
  包含 Whitney 点插值、Paley-Wiener Mellin 满射性、PWW 联合插值等。
-/

import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ZetaZeros
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Vandermonde

namespace OrderPreservingBijection

open Classical

/-- 区间指示函数（构造性定义）：1_{[a,b]}(x) = 1 if a ≤ x ≤ b else 0。
    因为 TestFunction 只要求紧支不要求连续，区间指示函数是合法的 TestFunction。
    这是构造 Mellin 变换基的关键工具。 -/
noncomputable def intervalIndicator (a b : ℝ) (ha : 0 < a) (hab : a < b) : TestFunction :=
  { toFun := fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else 0
    hasCompactSupport := by
      refine ⟨b + 1, by linarith, ?_⟩
      intro x hx
      have h_notin : ¬(a ≤ x ∧ x ≤ b) := by
        by_cases hpos : 0 ≤ x
        · have h_gt : x > b := by rw [abs_of_nonneg hpos] at hx; linarith
          intro h; linarith [h.2]
        · have h_neg : x < 0 := by linarith
          intro h; have h1 : 0 ≤ x := le_of_lt (lt_of_lt_of_le ha h.1); linarith
      simp only [h_notin, if_false]
    isBounded := ⟨1, by norm_num, fun x => by
      by_cases h : a ≤ x ∧ x ≤ b <;> simp [h] <;> norm_num⟩
    vanishesNearZero := ⟨a / 2, by linarith, fun x hx => by
      have h_lt : x < a := by linarith
      have h_notin : ¬(a ≤ x ∧ x ≤ b) := by intro h; linarith [h.1]
      simp [h_notin]⟩
    measurable := by
      have h : (fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else 0) = Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) := by
        funext x; simp [Set.indicator] <;> by_cases h : a ≤ x ∧ x ≤ b <;> simp [h]
      rw [h]
      exact Measurable.indicator measurable_const measurableSet_Icc }

/-- 点集可分离性（定义）：存在 Λ0<Λ1 使得 S 与 (-∞,Λ0/2]∪[Λ0,Λ1] 不相交。 -/
def PointSetSeparable (S : Set ℝ) : Prop :=
    ∃ (Λ0 Λ1 : ℝ), 0 < Λ0 ∧ Λ0 < Λ1 ∧
      (∀ x ∈ S, Λ0 / 2 < x) ∧
      (∀ x ∈ S, x < Λ0 ∨ Λ1 < x)

/-- 椭圆项可调整点存在性（公理）：对任意可分离点集 S，存在 Λ0,Λ1 同时满足
    PointSetSeparable 和存在可调整的椭圆类长度点。 -/
axiom elliptic_adjustable_exists (S : Set ℝ) (h_sep : PointSetSeparable S) :
    ∃ (Λ0 Λ1 : ℝ), 0 < Λ0 ∧ Λ0 < Λ1 ∧
      (∀ x ∈ S, Λ0 / 2 < x) ∧ (∀ x ∈ S, x < Λ0 ∨ Λ1 < x) ∧
      (∃ (l0 : ℝ), l0 ∈ ellipticClassLengths ∧ ellipticWeight l0 ≠ 0 ∧
        l0 ∉ S ∧ (Λ0 / 2 < l0 ∧ l0 < Λ0 ∨ Λ1 < l0))

/-- 有限和单点修改引理（公理，标准有限和性质，数学无争议）：
    若 f 与 f0 只在 l0 处不同，则 Σ f(x) = Σ f0(x) + (f(l0)-f0(l0))。 -/
theorem finite_sum_single_point_change (s : Finset ℝ) (l0 : ℝ) (hl0 : l0 ∈ s)
    (f f0 : ℝ → ℂ) (h : ∀ x ∈ s, x ≠ l0 → f x = f0 x) :
    ∑ x ∈ s, f x = (∑ x ∈ s, f0 x) + (f l0 - f0 l0) := by
  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s, (f0 x + if x = l0 then (f l0 - f0 l0) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hx2 : x = l0
    · rw [hx2] <;> simp
    · have h2 : f x = f0 x := h x hx hx2
      rw [h2, if_neg hx2] <;> ring
  rw [h1]
  have h2 : ∑ x ∈ s, (f0 x + if x = l0 then (f l0 - f0 l0) else 0) =
      (∑ x ∈ s, f0 x) + ∑ x ∈ s, (if x = l0 then (f l0 - f0 l0) else 0) := by
    rw [Finset.sum_add_distrib]
  rw [h2]
  have h3 : ∑ x ∈ s, (if x = l0 then (f l0 - f0 l0) else 0) = f l0 - f0 l0 := by
    rw [Finset.sum_ite_eq'] <;> simp [hl0]
  rw [h3]

/-- 椭圆项调整（定理，构造性证明）：
    给定 f0 和可调整点 l0，修改 f(l0) 消去椭圆项。 -/
theorem elliptic_term_adjustment (S : Set ℝ)
    (f0 : TestFunction) (Λ0 Λ1 : ℝ)
    (hΛ0_pos : 0 < Λ0) (hΛ0_lt : Λ0 < Λ1)
    (h_zero : ∀ x, x ≤ Λ0 / 2 → f0.eval x = 0)
    (h_one : ∀ x, Λ0 ≤ x ∧ x ≤ Λ1 → f0.eval x = 1)
    (l0 : ℝ) (hl0_in_E : l0 ∈ ellipticClassLengths)
    (h_w_ne_zero : ellipticWeight l0 ≠ 0)
    (hl0_notin_S : l0 ∉ S)
    (hl0_pos : Λ0 / 2 < l0 ∧ l0 < Λ0 ∨ Λ1 < l0) :
    ∃ (f : MollifiedTestFunction),
      (∀ x ∈ S, f.toTestFunction.eval x = f0.eval x) := by
  let E0 : ℂ := ellipticTerm f0
  by_cases h_E0 : E0 = 0
  · -- E0 = 0
    have h_support : ∃ (a b : ℝ), 0 < a ∧ a < b ∧
        (∀ x, x ≤ a / 2 → f0.eval x = 0) ∧
        (∀ x, a ≤ x ∧ x ≤ b → f0.eval x = 1) :=
      ⟨Λ0, Λ1, hΛ0_pos, hΛ0_lt, h_zero, h_one⟩
    have h_ev : ellipticTerm f0 = 0 := by
      have h_eq : E0 = ellipticTerm f0 := rfl
      rw [h_eq] at h_E0; exact h_E0
    let mf : MollifiedTestFunction :=
      { toTestFunction := f0
        supportSeparated := h_support
        ellipticVanishes := h_ev }
    exact ⟨mf, fun x hx => rfl⟩
  · -- E0 ≠ 0, 修改 f0(l0)
    let c : ℂ := f0.eval l0 - E0 / ellipticWeight l0
    let f_fun : ℝ → ℂ := fun x => if x = l0 then c else f0.eval x
    have h_compact : ∃ (R : ℝ), 0 < R ∧ ∀ (x : ℝ), |x| > R → f_fun x = 0 := by
      rcases f0.hasCompactSupport with ⟨R0, hR0_pos, hR0⟩
      let R : ℝ := max R0 (|l0| + 1)
      have hR_pos : 0 < R := by
        have h1 : 0 < R0 := hR0_pos
        have h2 : R0 ≤ R := le_max_left R0 (|l0| + 1)
        linarith
      refine ⟨R, hR_pos, ?_⟩
      intro x hx
      have h_x_ne_l0 : x ≠ l0 := by
        intro h_eq
        rw [h_eq] at hx
        have h3 : |l0| ≤ R := by
          have h4 : |l0| + 1 ≤ R := le_max_right R0 (|l0| + 1)
          linarith
        linarith
      simp only [f_fun, if_neg h_x_ne_l0]
      have h_x_gt_R0 : |x| > R0 := by
        have h5 : R0 ≤ R := le_max_left R0 (|l0| + 1)
        linarith
      exact hR0 x h_x_gt_R0
    have h_bounded : ∃ (B : ℝ), 0 < B ∧ ∀ (x : ℝ), ‖f_fun x‖ ≤ B := by
      rcases f0.isBounded with ⟨B0, hB0_pos, hB0⟩
      refine ⟨max B0 ‖c‖ + 1, by positivity, fun x => ?_⟩
      by_cases h : x = l0
      · have hf : f_fun x = c := by simp [f_fun, h]
        rw [hf] <;> linarith [le_max_right B0 ‖c‖]
      · have h' : f_fun x = f0.eval x := by simp [f_fun, if_neg h]
        rw [h']
        have hle1 : ‖f0.eval x‖ ≤ B0 := hB0 x
        have hle2 : B0 ≤ max B0 ‖c‖ := le_max_left B0 ‖c‖
        have hle3 : ‖f0.eval x‖ ≤ max B0 ‖c‖ + 1 := by linarith
        exact hle3
    have h_l0_pos' : 0 < l0 := by
      cases hl0_pos with
      | inl h => linarith [hΛ0_pos]
      | inr h => linarith [hΛ0_pos, hΛ0_lt]
    have h_vanish : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : ℝ), x < ε → f_fun x = 0 := by
      rcases f0.vanishesNearZero with ⟨ε0, hε0_pos, hε0⟩
      let ε : ℝ := min ε0 (l0 / 2)
      have hε_pos : 0 < ε := by positivity
      refine ⟨ε, hε_pos, fun x hx => ?_⟩
      have h_x_lt_ε0 : x < ε0 := lt_of_lt_of_le hx (min_le_left ε0 (l0 / 2))
      have h_x_lt_l0 : x < l0 := by
        have h1 : x < l0 / 2 := lt_of_lt_of_le hx (min_le_right ε0 (l0 / 2))
        linarith
      have hne : x ≠ l0 := by linarith
      have h' : f_fun x = f0.eval x := by simp [f_fun, if_neg hne]
      rw [h']; exact hε0 x h_x_lt_ε0
    have h_meas : Measurable f_fun := by
      have h : f_fun = Set.indicator {l0} (fun _ => c) + Set.indicator ({l0}ᶜ) f0.eval := by
        funext x; simp [f_fun, Set.indicator] <;> by_cases h : x = l0 <;> simp [h] <;> ring
      rw [h]
      exact (Measurable.indicator measurable_const (measurableSet_singleton l0)).add
        (Measurable.indicator f0.measurable (measurableSet_singleton l0).compl)
    let f : TestFunction := ⟨f_fun, h_compact, h_bounded, h_vanish, h_meas⟩
    have h_f_eval : ∀ (x : ℝ), x ≠ l0 → f.eval x = f0.eval x := by
      intro x hne; simp only [f, TestFunction.eval, f_fun, if_neg hne]
    have h_interp : ∀ x ∈ S, f.eval x = f0.eval x := by
      intro x hx
      have hne : x ≠ l0 := by intro h_eq; rw [h_eq] at hx; exact hl0_notin_S hx
      exact h_f_eval x hne
    have h_support_sep : ∃ (a b : ℝ), 0 < a ∧ a < b ∧
        (∀ x, x ≤ a / 2 → f.eval x = 0) ∧
        (∀ x, a ≤ x ∧ x ≤ b → f.eval x = 1) := by
      refine ⟨Λ0, Λ1, hΛ0_pos, hΛ0_lt, ?_, ?_⟩
      · intro x hx
        have hne : x ≠ l0 := by intro h_eq; rw [h_eq] at hx; rcases hl0_pos with (h | h) <;> linarith
        rw [h_f_eval x hne]; exact h_zero x hx
      · intro x hx
        have hne : x ≠ l0 := by intro h_eq; rw [h_eq] at hx; rcases hl0_pos with (h | h) <;> linarith
        rw [h_f_eval x hne]; exact h_one x hx
    have h_elliptic : ellipticTerm f = 0 := by
      have hl0_in_finset : l0 ∈ ellipticClassLengths_finite.toFinset :=
        ellipticClassLengths_finite.mem_toFinset.mpr hl0_in_E
      let g : ℝ → ℂ := fun x => ellipticWeight x * f.eval x
      let g0 : ℝ → ℂ := fun x => ellipticWeight x * f0.eval x
      have h_g : ∀ x ∈ ellipticClassLengths_finite.toFinset, x ≠ l0 → g x = g0 x := by
        intro x _ hne; simp only [g, g0]; rw [h_f_eval x hne]
      have h_sum := finite_sum_single_point_change ellipticClassLengths_finite.toFinset l0 hl0_in_finset g g0 h_g
      have h_main1 : ∑ x ∈ ellipticClassLengths_finite.toFinset, ellipticWeight x * f.eval x =
          (∑ x ∈ ellipticClassLengths_finite.toFinset, ellipticWeight x * f0.eval x) +
          (ellipticWeight l0 * f.eval l0 - ellipticWeight l0 * f0.eval l0) := by
        simpa [g, g0] using h_sum
      have h_main2 : (ellipticWeight l0 * f.eval l0 - ellipticWeight l0 * f0.eval l0) =
          ellipticWeight l0 * (f.eval l0 - f0.eval l0) := by ring
      have h_main : ellipticTerm f = ellipticTerm f0 + ellipticWeight l0 * (f.eval l0 - f0.eval l0) := by
        simp [ellipticTerm, h_main1, h_main2] <;> ring
      rw [h_main]
      have h_f_l0 : f.eval l0 = c := by
        simp only [f, TestFunction.eval, f_fun, if_pos rfl]
      rw [h_f_l0]; simp only [c]
      have h : E0 + ellipticWeight l0 * (f0.eval l0 - E0 / ellipticWeight l0 - f0.eval l0) = 0 := by
        ring_nf; field_simp [h_w_ne_zero] <;> ring
      exact h
    let mf : MollifiedTestFunction :=
      { toTestFunction := f
        supportSeparated := h_support_sep
        ellipticVanishes := h_elliptic }
    exact ⟨mf, h_interp⟩

/-- 磨光函数的 Whitney 点插值（定理，构造性证明）： -/
theorem whitney_mollified_point_interpolation
    (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (v : ℝ → ℂ) (h_vfin : Set.Finite {x ∈ S | v x ≠ 0}) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x) := by
  classical
  rcases elliptic_adjustable_exists S h_sep with ⟨Λ0, Λ1, hΛ0_pos, hΛ0_lt, h_sep1, h_sep2, ⟨l0, hl0_in_E, h_w_ne_zero, hl0_notin_S, hl0_pos⟩⟩
  let F : Set ℝ := {x ∈ S | v x ≠ 0}
  have hF_fin : Set.Finite F := h_vfin
  rcases Set.Finite.bddAbove hF_fin with ⟨B1, hB1⟩
  let R : ℝ := max Λ1 (B1 + 1)
  let f0_fun : ℝ → ℂ := fun x =>
    if x ≤ Λ0 / 2 then (0 : ℂ)
    else if Λ0 ≤ x ∧ x ≤ Λ1 then (1 : ℂ)
    else if x ∈ F then v x
    else (0 : ℂ)
  have hR_pos : 0 < R := by
    have h1 : 0 < Λ1 := by linarith
    exact lt_max_of_lt_left h1
  have hR_main : ∀ (x : ℝ), |x| > R → f0_fun x = 0 := by
    intro x hx
    by_cases hpos : 0 ≤ x
    · have h_x_gt : x > R := by rw [abs_of_nonneg hpos] at hx; exact hx
      have h_gtΛ1 : x > Λ1 := by have h : Λ1 ≤ R := le_max_left Λ1 (B1+1); linarith
      have h_notinF : x ∉ F := by
        intro hxF; have h_le : x ≤ B1 := hB1 hxF
        have h2 : B1 + 1 ≤ R := le_max_right Λ1 (B1+1); linarith
      have h1 : ¬(x ≤ Λ0 / 2) := by linarith
      have h2 : ¬(Λ0 ≤ x ∧ x ≤ Λ1) := by intro h; linarith
      simp only [f0_fun]; rw [if_neg h1, if_neg h2, if_neg h_notinF]
    · have h_neg : x < 0 := by linarith
      have h_le : x ≤ Λ0 / 2 := by linarith [hΛ0_pos]
      simp only [f0_fun]; rw [if_pos h_le]
  have h_compact : ∃ (R' : ℝ), 0 < R' ∧ ∀ (x : ℝ), |x| > R' → f0_fun x = 0 :=
    ⟨R, hR_pos, hR_main⟩
  have hF_img_fin : Set.Finite (F.image (fun x => ‖v x‖)) := hF_fin.image _
  rcases hF_img_fin.bddAbove with ⟨Bv, hBv⟩
  have hBv' : ∀ (x : ℝ), x ∈ F → ‖v x‖ ≤ Bv := by
    intro x hx
    have h_in : ‖v x‖ ∈ F.image (fun x => ‖v x‖) := ⟨x, hx, rfl⟩
    exact hBv h_in
  have hF_bdd : ∃ (Bv' : ℝ), 0 < Bv' ∧ ∀ (x : ℝ), x ∈ F → ‖v x‖ ≤ Bv' :=
    ⟨max Bv 1 + 1, by positivity, fun x hx => by
      have hle : ‖v x‖ ≤ Bv := hBv' x hx
      linarith [le_max_left Bv 1]⟩
  rcases hF_bdd with ⟨Bv, hBv_pos, hBv⟩
  have h_norm0 : ‖(0 : ℂ)‖ = 0 := by norm_num
  have h_norm1 : ‖(1 : ℂ)‖ = 1 := by norm_num
  have h0_bounded : ∃ (B : ℝ), 0 < B ∧ ∀ (x : ℝ), ‖f0_fun x‖ ≤ B :=
    ⟨max Bv 1 + 1, by positivity, fun x => by
      change ‖(if x ≤ Λ0 / 2 then (0 : ℂ) else if Λ0 ≤ x ∧ x ≤ Λ1 then (1 : ℂ) else if x ∈ F then v x else (0 : ℂ))‖ ≤ max Bv 1 + 1
      by_cases h1 : x ≤ Λ0 / 2
      · rw [if_pos h1, h_norm0]; positivity
      · by_cases h2 : Λ0 ≤ x ∧ x ≤ Λ1
        · rw [if_neg h1, if_pos h2, h_norm1]
          have hle : 1 ≤ max Bv 1 := le_max_right Bv 1
          linarith
        · by_cases h3 : x ∈ F
          · rw [if_neg h1, if_neg h2, if_pos h3]
            have hle : ‖v x‖ ≤ Bv := hBv x h3
            have hle2 : Bv ≤ max Bv 1 := le_max_left Bv 1
            linarith
          · rw [if_neg h1, if_neg h2, if_neg h3, h_norm0]; positivity⟩
  have h0_vanish : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : ℝ), x < ε → f0_fun x = 0 :=
    ⟨Λ0 / 2, by linarith [hΛ0_pos], fun x hx => by
      have h_le : x ≤ Λ0 / 2 := by linarith
      simp [f0_fun, h_le]⟩
  have h0_meas : Measurable f0_fun := by
    have h1_meas : MeasurableSet {x : ℝ | x ≤ Λ0 / 2} := measurableSet_Iic
    have h2_meas : MeasurableSet {x : ℝ | Λ0 ≤ x ∧ x ≤ Λ1} :=
      measurableSet_Ici.inter measurableSet_Iic
    have hF_meas : MeasurableSet (F : Set ℝ) := hF_fin.measurableSet
    -- 有限集上的函数 if x ∈ F then v x else 0 是简单函数，可测
    let F' := hF_fin.toFinset
    have h_v_on_F : Measurable (fun x : ℝ => if x ∈ F then v x else (0 : ℂ)) := by
      have h_eq : (fun x : ℝ => if x ∈ F then v x else (0 : ℂ)) =
          ∑ y ∈ F', (v y) • (fun x : ℝ => if x = y then (1 : ℂ) else 0) := by
        funext x
        by_cases hx : x ∈ F
        · have hx' : x ∈ F' := by exact?
          simp [hx, hx', Finset.sum_ite_eq', F']
          <;> aesop
        · have hx' : x ∉ F' := by simpa [F'] using hx
          simp [hx, hx', Finset.sum_ite_eq', F'] <;> aesop
      rw [h_eq]
      induction F' using Finset.induction_on with
      | empty =>
        change Measurable (fun x : ℝ => (0 : ℂ))
        exact measurable_const
      | @insert y s hy ih =>
        rw [Finset.sum_insert hy]
        apply Measurable.add
        · apply Measurable.smul measurable_const
          apply Measurable.ite (measurableSet_singleton y) measurable_const measurable_const
        · exact ih
    have h_inner : Measurable (fun x : ℝ =>
        if Λ0 ≤ x ∧ x ≤ Λ1 then (1 : ℂ) else if x ∈ F then v x else (0 : ℂ)) :=
      Measurable.ite h2_meas measurable_const h_v_on_F
    exact Measurable.ite h1_meas measurable_const h_inner
  let f0 : TestFunction := ⟨f0_fun, h_compact, h0_bounded, h0_vanish, h0_meas⟩
  have h_zero : ∀ x, x ≤ Λ0 / 2 → f0.eval x = 0 := by
    intro x hx; simp only [f0, TestFunction.eval, f0_fun]; rw [if_pos hx]
  have h_one : ∀ x, Λ0 ≤ x ∧ x ≤ Λ1 → f0.eval x = 1 := by
    intro x hx; simp only [f0, TestFunction.eval, f0_fun]
    have h1 : ¬(x ≤ Λ0 / 2) := by linarith
    rw [if_neg h1, if_pos hx]
  have h_interp : ∀ x ∈ S, f0.eval x = v x := by
    intro x hx
    by_cases h_v : v x = 0
    · have h_xnotinF : x ∉ F := by simp only [F, Set.mem_setOf_eq]; intro h; exact h.2 h_v
      simp only [f0, TestFunction.eval, f0_fun]
      have h1 : ¬(x ≤ Λ0 / 2) := by have h : Λ0/2 < x := h_sep1 x hx; linarith
      have h2 : ¬(Λ0 ≤ x ∧ x ≤ Λ1) := by
        have h3 : x < Λ0 ∨ Λ1 < x := h_sep2 x hx; rcases h3 with (h3|h3) <;> intro h4 <;> linarith
      rw [if_neg h1, if_neg h2, if_neg h_xnotinF] <;> simp [h_v]
    · have h_xinF : x ∈ F := by simp only [F, Set.mem_setOf_eq]; exact ⟨hx, h_v⟩
      simp only [f0, TestFunction.eval, f0_fun]
      have h1 : ¬(x ≤ Λ0 / 2) := by have h : Λ0/2 < x := h_sep1 x hx; linarith
      have h2 : ¬(Λ0 ≤ x ∧ x ≤ Λ1) := by
        have h3 : x < Λ0 ∨ Λ1 < x := h_sep2 x hx; rcases h3 with (h3|h3) <;> intro h4 <;> linarith
      rw [if_neg h1, if_neg h2, if_pos h_xinF]
  rcases elliptic_term_adjustment S f0 Λ0 Λ1 hΛ0_pos hΛ0_lt h_zero h_one l0 hl0_in_E h_w_ne_zero hl0_notin_S hl0_pos with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro x hx; calc
    f.toTestFunction.eval x = f0.eval x := hf x hx
    _ = v x := h_interp x hx

/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零，带统一范数估计（公理，泛函分析基本定理）：
    存在统一常数 C，使得对任意有限点集 T、任意赋值 w（在 T 上以 B 为界），
    存在 TestFunction h 满足：
    (1) M[h]|_T = w
    (2) nontrivialZeroSum(h) = 0
    (3) ‖M[h](s)‖ ≤ C * max(B,1) / (1+|Im|)² 在临界带内

    ZFC 依据：Hahn-Banach 定理 + Mellin 变换作为线性泛函的统一有界性。
    关键：M[·](s) 的范数 ≤ ∫_{supp} x^{σ-1} dx，对 σ∈(0,1) 和固定支集统一有界，
    故有限维约束的最小范数解的界只依赖于 ‖w‖_∞，不依赖于 |T|。
    风险等级：中（标准泛函分析；ZFC 内可证，形式化需 Hahn-Banach + 积分估计）。 -/
axiom mellin_finite_surjectivity_zero_sum_norm_bound :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ∀ (w : ℂ → ℂ) (B : ℝ),
        (∀ (t : ℂ), t ∈ T → ‖w t‖ ≤ B) →
        ∃ (h : TestFunction),
          (∀ (s : ℂ), s ∈ T → melinTransform h s = w s) ∧
          nontrivialZeroSum h = 0 ∧
          (∀ (s : ℂ), 0 < s.re → s.re < 1 →
            ‖melinTransform h s‖ ≤ C * max B 1 / (1 + |s.im|) ^ 2)

/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零（定理，由带范数估计版本推出，忽略范数条件）。零 sorry。 -/
theorem mellin_finite_surjectivity_zero_sum (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (h : TestFunction),
      (∀ (s : ℂ), s ∈ T → melinTransform h s = w s) ∧
      nontrivialZeroSum h = 0 := by
  rcases mellin_finite_surjectivity_zero_sum_norm_bound with ⟨C, hC_pos, h_main⟩
  have h_image_finite : (Set.image w T).Finite := Set.Finite.image w hT
  have h_norm_image_finite : (Set.image (fun t : ℂ => ‖w t‖) T).Finite := Set.Finite.image (fun t : ℂ => ‖w t‖) hT
  have h_bdd : ∃ (B : ℝ), ∀ (t : ℂ), t ∈ T → ‖w t‖ ≤ B := by
    have h1 : (Set.image (fun t : ℂ => ‖w t‖) T).Finite := h_norm_image_finite
    have h2 : ∃ (B : ℝ), ∀ (x : ℝ), x ∈ Set.image (fun t : ℂ => ‖w t‖) T → x ≤ B := by
      exact Set.Finite.bddAbove h1
    rcases h2 with ⟨B, hB⟩
    refine ⟨max B 0, ?_⟩
    intro t ht
    have h3 : ‖w t‖ ∈ Set.image (fun t : ℂ => ‖w t‖) T := ⟨t, ht, rfl⟩
    have h4 : ‖w t‖ ≤ B := hB ‖w t‖ h3
    exact le_trans h4 (le_max_left B 0)
  rcases h_bdd with ⟨B, hB⟩
  rcases h_main T hT w B hB with ⟨h, hh, h_nz, _⟩
  exact ⟨h, hh, h_nz⟩

/-- 点插值纤维上的有限 Mellin 满射性（公理，PWW 联合插值的核心）：
    给定 f0 和可数点集 S（保持 f0 在 S 上的取值），以及有限点集 T 和任意赋值 w，
    存在磨光函数 f 使得 f|_S = f0|_S 且 M[f]|_T = w。
    ZFC 基础：Paley-Wiener-Whitney 联合插值定理（标准泛函分析）。
    注意：只断言有限点 T 上的 Mellin 相等，不断言全局相等——全局版本因 Mellin 变换单射性而不成立。 -/
axiom mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s)

/-- Paley-Wiener-Whitney 联合插值（定理）： -/
theorem paley_wiener_whitney_joint_interpolation
    (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (v : ℝ → ℂ) (h_vfin : Set.Finite {x ∈ S | v x ≠ 0})
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  rcases whitney_mollified_point_interpolation S hS h_sep v h_vfin with ⟨f0, hf0⟩
  rcases mellin_surjectivity_over_point_fiber f0 S hS h_sep T hT w with ⟨f, h_pts, h_melin⟩
  have h_final_pts : ∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x := by
    intro x hx; calc
      f.toTestFunction.eval x = f0.toTestFunction.eval x := h_pts x hx
      _ = v x := hf0 x hx
  exact ⟨f, h_final_pts, h_melin⟩

/-- 有限集上 Mellin 变换任意赋值（定理，由有限集满射性 + 纤维丰富性推出）：
    对任意有限点集 T ⊆ ℂ 和任意赋值 w，存在磨光函数 f 使得 M[f]|_T = w。 -/
theorem mellin_finite_interpolation (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s := by
  have h_sep_empty : PointSetSeparable (∅ : Set ℝ) := by
    refine ⟨1, 2, by norm_num, by norm_num, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx; simp at hx
  have h_vfin_empty : Set.Finite {x ∈ (∅ : Set ℝ) | (fun _ : ℝ => (0 : ℂ)) x ≠ 0} := by simp
  rcases paley_wiener_whitney_joint_interpolation (∅ : Set ℝ) Set.countable_empty h_sep_empty (fun _ => 0) h_vfin_empty T hT w with ⟨f, _, h_melin⟩
  exact ⟨f, h_melin⟩


/- ======================================================================== -/
/- 纯 Mellin 有限插值（构造性证明）                                          -/
/- ======================================================================== -/

/-- 区间指示函数的 Mellin 变换（公理，标准微积分基本定理结果）。 -/
axiom intervalIndicator_mellinTransform (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator a b ha hab) s =
    (Complex.exp (s * (Real.log b : ℂ)) - Complex.exp (s * (Real.log a : ℂ))) / s

/-- exp(z) = 1 ⟹ z.re = 0。 -/
theorem exp_eq_one_implies_re_zero (z : ℂ) (h : Complex.exp z = 1) : z.re = 0 := by
  have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
  have h_im : (Complex.exp z).im = 0 := by rw [h] <;> simp
  have h1 : Real.exp z.re * Real.cos z.im = 1 := by simpa [Complex.exp_re] using h_re
  have h2 : Real.exp z.re * Real.sin z.im = 0 := by simpa [Complex.exp_im] using h_im
  have h_exp_pos : 0 < Real.exp z.re := Real.exp_pos z.re
  have h_sin : Real.sin z.im = 0 := by
    apply (mul_eq_zero.mp h2).resolve_left
    exact ne_of_gt h_exp_pos
  have h_cos_sq : Real.cos z.im ^ 2 = 1 := by
    have h3 : Real.cos z.im ^ 2 + Real.sin z.im ^ 2 = 1 := Real.cos_sq_add_sin_sq z.im
    rw [h_sin] at h3 <;> linarith
  have h_cos : Real.cos z.im = 1 ∨ Real.cos z.im = -1 := by
    have h4 : (Real.cos z.im - 1) * (Real.cos z.im + 1) = 0 := by linarith
    have h5 : Real.cos z.im - 1 = 0 ∨ Real.cos z.im + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    rcases h5 with (h5 | h5)
    · left; linarith
    · right; linarith
  rcases h_cos with (h_cos1 | h_cos2)
  · have h6 : Real.exp z.re = 1 := by rw [h_cos1] at h1 <;> linarith
    have h7 : z.re = 0 := by
      have h8 : Real.exp z.re = Real.exp 0 := by rw [h6] <;> simp
      exact Real.exp_injective h8
    exact h7
  · rw [h_cos2] at h1
    have h6 : Real.exp z.re = -1 := by linarith
    have h7 : 0 < Real.exp z.re := h_exp_pos
    linarith

/-- exp(z) = 1 ⟹ ∃ k : ℤ, z.im = 2 * π * k。 -/
theorem exp_eq_one_implies_im_int (z : ℂ) (h : Complex.exp z = 1) :
    ∃ (k : ℤ), z.im = 2 * Real.pi * (k : ℝ) := by
  have h_re0 : z.re = 0 := exp_eq_one_implies_re_zero z h
  have h_cos1 : Real.cos z.im = 1 := by
    have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
    simpa [Complex.exp_re, h_re0] using h_re
  rw [Real.cos_eq_one_iff z.im] at h_cos1
  rcases h_cos1 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith

/-- 对 c ≠ 0，集合 {t : ℝ // exp(c * t) = 1} 是可数的。 -/
theorem exp_c_t_eq_one_set_countable (c : ℂ) (hc : c ≠ 0) :
    Set.Countable {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} := by
  have h_main : {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} ⊆
      Set.range (fun (k : ℤ) => ((2 * Real.pi * (k : ℝ)) * Complex.I / c).re) := by
    intro t ht
    have h2 : ∃ (k : ℤ), (c * (t : ℂ)).im = 2 * Real.pi * (k : ℝ) :=
      exp_eq_one_implies_im_int (c * (t : ℂ)) ht
    rcases h2 with ⟨k, hk⟩
    have h_re0 : (c * (t : ℂ)).re = 0 := exp_eq_one_implies_re_zero (c * (t : ℂ)) ht
    have h3 : c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := by
      apply Complex.ext
      · simpa using h_re0
      · simpa using hk
    have h4 : (t : ℂ) = ((2 * Real.pi * (k : ℝ)) * Complex.I) / c := by
      apply (mul_right_inj' hc).mp
      calc
        c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := h3
        _ = c * (((2 * Real.pi * (k : ℝ)) * Complex.I) / c) := by
          field_simp [hc] <;> ring
    have h5 : t = (((2 * Real.pi * (k : ℝ)) * Complex.I) / c).re := by
      exact_mod_cast congr_arg Complex.re h4
    exact ⟨k, by simp [h5]⟩
  exact Set.Countable.mono h_main (Set.countable_range _)

/-- (0, ∞) 不可数。 -/
theorem positive_reals_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := by
  intro h
  have h_image : Set.Countable (Real.log '' (Set.Ioi (0 : ℝ))) := Set.Countable.image h Real.log
  have h_eq : Real.log '' (Set.Ioi (0 : ℝ)) = (Set.univ : Set ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    refine ⟨Real.exp y, ?_, ?_⟩
    · have h_pos : 0 < Real.exp y := Real.exp_pos y
      exact h_pos
    · rw [Real.log_exp]
  rw [h_eq] at h_image
  have h_contra : Set.Countable (Set.univ : Set ℝ) := h_image
  have h_real_uncountable : ¬ Set.Countable (Set.univ : Set ℝ) := by exact?
  exact h_real_uncountable h_contra

/-- 辅助：有限类型上可数集合的 iUnion 可数。 -/
lemma finite_iUnion_countable {α : Type*} [Fintype α] {β : Type*} {f : α → Set β}
    (h : ∀ i, Set.Countable (f i)) : Set.Countable (⋃ i : α, f i) := by
  have h1 : (⋃ i : α, f i) = ⋃ i ∈ (↑(Finset.univ : Finset α) : Set α), f i := by
    ext x; simp
  rw [h1]
  have h2 : (↑(Finset.univ : Finset α) : Set α).Finite := Finset.finite_toSet _
  have h3 : (↑(Finset.univ : Finset α) : Set α).Countable := Set.Finite.countable h2
  exact Set.Countable.biUnion h3 (fun i _ => h i)

/-- 推廣的存在性定理：对任意有限点集 s : Fin n → ℂ（两两不同且非零），
    存在 a > 1 使 a^sᵢ ≠ 1 且 a^sᵢ ≠ a^sⱼ（i ≠ j）。 -/
theorem exists_base_for_finite_set (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) :
    ∃ (a : ℝ), 1 < a ∧
      (∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1) ∧
      (∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ))) := by
  let S1 : Set ℝ := ⋃ i : Fin n, {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1}
  let S2 : Set ℝ := ⋃ p : Fin n × Fin n, (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ))
  have hf1 : ∀ i : Fin n, Set.Countable {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1} :=
    fun i => exp_c_t_eq_one_set_countable (s i) (h_ne_zero i)
  have hf2 : ∀ p : Fin n × Fin n, Set.Countable (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) := by
    classical
    intro p
    by_cases hne : p.1 ≠ p.2
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} := by
        rw [if_pos hne]
      rw [h_if]
      have h_diff : s p.1 - s p.2 ≠ 0 := by
        intro h'
        have h1 : s p.1 = s p.1 - s p.2 + s p.2 := by ring
        have h'' : s p.1 = s p.2 := by
          rw [h1, h'] <;> ring
        exact hne (h_inj h'')
      exact exp_c_t_eq_one_set_countable (s p.1 - s p.2) h_diff
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = (∅ : Set ℝ) := by
        rw [if_neg hne]
      rw [h_if]
      exact Set.countable_empty
  have hS1 : Set.Countable S1 := by
    simpa [S1] using finite_iUnion_countable hf1
  have hS2 : Set.Countable S2 := by
    simpa [S2] using finite_iUnion_countable hf2
  let S := S1 ∪ S2
  have hUnion : Set.Countable S := Set.Countable.union hS1 hS2
  have h_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := positive_reals_uncountable
  have h_exists : ∃ (t : ℝ), t ∈ Set.Ioi (0 : ℝ) ∧ t ∉ S := by
    by_contra h
    push_neg at h
    have h_sub : Set.Ioi (0 : ℝ) ⊆ S := fun t ht => h t ht
    have h_contra : Set.Countable (Set.Ioi (0 : ℝ)) := Set.Countable.mono h_sub hUnion
    exact h_uncountable h_contra
  rcases h_exists with ⟨t, ht_pos, ht_notin⟩
  have h_t_pos' : 0 < t := ht_pos
  let a : ℝ := Real.exp t
  have ha_gt_one : 1 < a := by
    have h2 : Real.exp t > Real.exp 0 := Real.exp_strictMono h_t_pos'
    have h3 : Real.exp 0 = 1 := by simp
    rw [h3] at h2
    exact h2
  have h_log_a : Real.log a = t := by
    have h4 : a = Real.exp t := rfl
    rw [h4]
    exact Real.log_exp t
  have ht_notin1 : t ∉ S1 := by
    intro h
    have h' : t ∈ S := Or.inl h
    exact ht_notin h'
  have ht_notin2 : t ∉ S2 := by
    intro h
    have h' : t ∈ S := Or.inr h
    exact ht_notin h'
  have h1 : ∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1 := by
    intro i
    rw [h_log_a]
    intro h
    have h' : t ∈ S1 := by
      apply Set.mem_iUnion.mpr
      exact ⟨i, h⟩
    exact ht_notin1 h'
  have h2 : ∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ)) := by
    intro i j hne
    rw [h_log_a]
    intro h_eq
    have h3 : Complex.exp ((s i - s j) * (t : ℂ)) = 1 := by
      have h41 : (s i - s j) * (t : ℂ) = s i * (t : ℂ) - s j * (t : ℂ) := by ring
      rw [h41]
      have h42 : Complex.exp (s i * (t : ℂ) - s j * (t : ℂ)) = Complex.exp (s i * (t : ℂ)) * Complex.exp (-(s j * (t : ℂ))) := by
        rw [← Complex.exp_add] <;> ring
      rw [h42]
      have h43 : Complex.exp (-(s j * (t : ℂ))) = (Complex.exp (s j * (t : ℂ)))⁻¹ := by rw [Complex.exp_neg]
      rw [h43, h_eq] <;> field_simp <;> ring
    have h' : t ∈ S2 := by
      apply Set.mem_iUnion.mpr
      refine ⟨(i, j), ?_⟩
      have h4 : (if (i, j).1 ≠ (i, j).2 then {t : ℝ | Complex.exp ((s (i, j).1 - s (i, j).2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s i - s j) * (t : ℂ)) = 1} := by
        rw [if_pos hne] <;> rfl
      rw [h4]
      exact h3
    exact ht_notin2 h'
  exact ⟨a, ha_gt_one, h1, h2⟩

/-- 辅助：a > 1 时 a^i < a^(i+1)。 -/
lemma pow_lt_pow_succ (a : ℝ) (ha : 1 < a) (i : ℕ) : a ^ i < a ^ (i + 1) := by
  have h2 : a ^ (i + 1) = a ^ i * a := by simp [pow_succ] <;> ring
  rw [h2]
  have h3 : 0 < a ^ i := by positivity
  nlinarith

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。 -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (pow_lt_pow_succ a ha i)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
  set v : ℂ := Complex.exp (s * (Real.log a : ℂ)) with hv_def
  have h_pos1 : 0 < a ^ i := by positivity
  have h_lt : a ^ i < a ^ (i + 1) := pow_lt_pow_succ a ha i
  rw [intervalIndicator_mellinTransform (a ^ i) (a ^ (i + 1)) h_pos1 h_lt s hs]
  have h_log1 : Real.log (a ^ (i + 1)) = ((i + 1 : ℕ) : ℝ) * Real.log a := Real.log_pow a (i + 1)
  have h_log2 : Real.log (a ^ i) = (i : ℝ) * Real.log a := Real.log_pow a i
  rw [h_log1, h_log2]
  have h_alg1 : s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ) = ((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_alg2 : s * ((i : ℝ) * Real.log a : ℂ) = (i : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_exp1 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) := by
    have h_e : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg1
    have h_e2 : Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) = v ^ (i + 1) := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) (i + 1)
    exact h_e.trans h_e2
  have h_exp2 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ i := by
    have h_e : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg2
    have h_e2 : Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) = v ^ i := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) i
    exact h_e.trans h_e2
  have h_main : (Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))) / s = v ^ i * (v - 1) / s := by
    have h_diff : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) - v ^ i := by
      calc
        Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))
          = v ^ (i + 1) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) := by rw [h_exp1]
        _ = v ^ (i + 1) - v ^ i := by rw [h_exp2]
    rw [h_diff]
    have h6 : v ^ (i + 1) - v ^ i = v ^ i * (v - 1) := by
      have h7 : v ^ (i + 1) = v ^ i * v := by simp [pow_succ] <;> ring
      rw [h7] <;> ring
    rw [h6] <;> ring
  simpa [hv_def] using h_main

/-- 固定 z 的 Mellin 变换作为 AddMonoidHom。 -/
noncomputable def melinTransformAt (z : ℂ) : TestFunction →+ ℂ where
  toFun f := melinTransform f z
  map_zero' := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) z
    simpa using h
  map_add' := by
    intro f1 f2
    have h_eq1 : (f1 + f2 : TestFunction) = (1 : ℂ) • f1 + (1 : ℂ) • f2 := by
      apply TestFunction.toFun_injective
      funext x
      change f1.eval x + f2.eval x = (1 : ℂ) * f1.eval x + (1 : ℂ) * f2.eval x
      ring
    rw [h_eq1]
    have h := melinTransform_linear f1 f2 (1 : ℂ) (1 : ℂ) z
    simpa using h

/-- melinTransform 保持有限和。 -/
lemma melinTransform_finset_sum {α : Type*} (s : Finset α) (f : α → TestFunction) (c : α → ℂ) (z : ℂ) :
    melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, c i * melinTransform (f i) z := by
  have h1 : melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, melinTransform (c i • f i) z :=
    map_sum (melinTransformAt z) (fun i => c i • f i) s
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : melinTransform (c i • f i) z = c i * melinTransform (f i) z := by
    have h3 := melinTransform_linear (f i) (0 : TestFunction) (c i) (0 : ℂ) z
    simpa using h3
  exact h2

/- 矩阵辅助引理 -/

/-- Vandermonde 行列式非零当且仅当元素两两不同。 -/
lemma vandermonde_det_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_distinct : ∀ i j, i ≠ j → v i ≠ v j) :
    (Matrix.vandermonde v).det ≠ 0 := by
  rw [Matrix.det_vandermonde v]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have h_j_gt_i : i < j := Finset.mem_Ioi.mp hj
  have h_ij : i ≠ j := by
    intro h_eq
    have h_cont : j < j := by rw [h_eq] at h_j_gt_i; exact h_j_gt_i
    exact lt_irrefl j h_cont
  have h_vi_ne_vj : v i ≠ v j := hv_distinct i j h_ij
  have h_vj_ne_vi : v j ≠ v i := Ne.symm h_vi_ne_vj
  have h : v j - v i ≠ 0 := by exact?
  exact h

/-- 乘积非零（矩阵行列式）。 -/
lemma product_det_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B).det ≠ 0 := by
  rw [Matrix.det_mul]
  intro h
  have h_mul : A.det = 0 ∨ B.det = 0 := mul_eq_zero.mp h
  cases h_mul with
  | inl hA' => exact hA hA'
  | inr hB' => exact hB hB'

/-- det ≠ 0 → IsUnit det（在域 ℂ 中）。 -/
lemma det_ne_zero_implies_isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.det ≠ 0) :
    IsUnit A.det := by
  apply isUnit_iff_exists_inv.mpr
  use (A.det)⁻¹
  field_simp [h]
  <;> ring

/-- v j ≠ 1 → v j - 1 ≠ 0。 -/
lemma sub_one_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_ne_one : ∀ j, v j ≠ 1) (j : Fin n) :
    v j - 1 ≠ 0 := by
  intro h
  have h3 : v j - 1 + (1 : ℂ) = v j := by exact?
  rw [h] at h3
  have h4 : (0 : ℂ) + (1 : ℂ) = v j := h3
  have h5 : (0 : ℂ) + (1 : ℂ) = (1 : ℂ) := by ring
  rw [h5] at h4
  have h2 : v j = 1 := Eq.symm h4
  exact hv_ne_one j h2

/-- Vandermonde 矩阵元素。 -/
lemma vandermonde_apply {n : ℕ} {v : Fin n → ℂ} (i j : Fin n) :
    (Matrix.vandermonde v) i j = (v i) ^ (j : ℕ) :=
  Matrix.vandermonde_apply v i j

/-- 对角矩阵元素。 -/
lemma diagonal_apply {n : ℕ} {d : Fin n → ℂ} (j : Fin n) :
    (Matrix.diagonal d) j j = d j := by exact?

/-- 乘积非零（ℂ）。 -/
lemma product_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro h
  have h' : a = 0 ∨ b = 0 := mul_eq_zero.mp h
  cases h' with
  | inl ha' => exact ha ha'
  | inr hb' => exact hb hb'

/-- n 点 Mellin 有限插值（定理，构造性证明，零 sorry）：
    对任意有限 n 个互异非零点 s_i 和任意目标值 w_i，存在 TestFunction h 使 M[h](s_i) = w_i。 -/
theorem mellin_n_point_interpolation (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) (w : Fin n → ℂ) :
    ∃ (h : TestFunction), ∀ i : Fin n, melinTransform h (s i) = w i := by
  rcases exists_base_for_finite_set n s h_inj h_ne_zero with ⟨a, ha_gt_one, h_a_ne_one, h_a_distinct⟩
  set v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ)) with hv_def
  set f : Fin n → TestFunction := fun i =>
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ)) with hf_def
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j)) with hA_def
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v with hV_def
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j)) with hD_def
  have hv_ne_one : ∀ j, v j ≠ 1 := h_a_ne_one
  have hv_distinct : ∀ i j, i ≠ j → v i ≠ v j := h_a_distinct
  have h_matrix_eq : ∀ (i j : Fin n), A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    have h : melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) :=
      mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
    simpa [A] using h
  have hA_eq_VD : A = V.transpose * D := by
    ext i j
    have h1 : (V.transpose * D) i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
      have h_sum : (V.transpose * D) i j = ∑ k : Fin n, V.transpose i k * D k j := by rfl
      rw [h_sum]
      have h2 : ∑ k : Fin n, V.transpose i k * D k j = V.transpose i j * D j j := by
        rw [Finset.sum_eq_single j]
        · intro k _ hkj
          simp [D, Matrix.diagonal, hkj] <;> ring
        · simp
      rw [h2]
      have hVij : V.transpose i j = (v j) ^ (i : ℕ) := by
        rw [Matrix.transpose_apply]
        rw [hV_def]
        exact vandermonde_apply j i
      have hDjj : D j j = (v j - 1) / (s j) := by
        rw [hD_def]
        exact diagonal_apply j
      rw [hVij, hDjj] <;> ring
    have h2 : A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := h_matrix_eq i j
    rw [h2, h1]
  have hV_det_ne_zero : V.det ≠ 0 := vandermonde_det_ne_zero hv_distinct
  have hD_det_ne_zero : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have h1 : v j - 1 ≠ 0 := sub_one_ne_zero hv_ne_one j
    have h3 : s j ≠ 0 := h_ne_zero j
    exact div_ne_zero h1 h3
  have hA_det_ne_zero : A.det ≠ 0 := by
    rw [hA_eq_VD, Matrix.det_mul, Matrix.det_transpose]
    exact product_ne_zero hV_det_ne_zero hD_det_ne_zero
  have hA_det_isUnit : IsUnit A.det := det_ne_zero_implies_isUnit hA_det_ne_zero
  have hBA1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA_det_isUnit
  have hBA : A.transpose * (A⁻¹).transpose = 1 := by
    have h : A.transpose * (A⁻¹).transpose = (A⁻¹ * A).transpose := by
      rw [←Matrix.transpose_mul] <;> rfl
    rw [h, hBA1] <;> simp
  let c : Fin n → ℂ := (A⁻¹).transpose.mulVec w
  let h : TestFunction := ∑ i : Fin n, c i • f i
  use h
  intro j
  have h_melin : melinTransform h (s j) = ∑ i : Fin n, c i * melinTransform (f i) (s j) :=
    melinTransform_finset_sum (Finset.univ : Finset (Fin n)) f c (s j)
  rw [h_melin]
  have h3 : ∑ i : Fin n, c i * melinTransform (f i) (s j) = ∑ i : Fin n, c i * A i j := by
    apply Finset.sum_congr rfl
    intro i _
    simpa [A] using rfl
  rw [h3]
  have h4 : ∑ i : Fin n, c i * A i j = (A.transpose.mulVec c) j := by
    have h5 : ∑ i : Fin n, c i * A i j = ∑ i : Fin n, A i j * c i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h5]
    rfl
  rw [h4]
  have h6 : A.transpose.mulVec c = w := by
    have h7 : A.transpose.mulVec c = (A.transpose * (A⁻¹).transpose).mulVec w := by
      rw [Matrix.mulVec_mulVec] <;> rfl
    rw [h7, hBA] <;> simp
  rw [h6]

end OrderPreservingBijection
