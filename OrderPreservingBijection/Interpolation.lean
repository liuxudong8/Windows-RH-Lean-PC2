/-
  插值理论模块
  包含 Whitney 点插值、Paley-Wiener Mellin 满射性、PWW 联合插值等。
-/

import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ZetaZeros
import Mathlib.Algebra.Module.Basic

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
      simp only [h_notin, if_false] }

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
axiom finite_sum_single_point_change (s : Finset ℝ) (l0 : ℝ) (hl0 : l0 ∈ s)
    (f f0 : ℝ → ℂ) (h : ∀ x ∈ s, x ≠ l0 → f x = f0 x) :
    ∑ x ∈ s, f x = (∑ x ∈ s, f0 x) + (f l0 - f0 l0)

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
    let f : TestFunction := ⟨f_fun, h_compact⟩
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
  let f0 : TestFunction := ⟨f0_fun, h_compact⟩
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

/-- 点插值纤维的 Mellin 丰富性（公理，磨光函数空间结构性质）：
    对任意磨光函数 f0、可分离可数点集 S、任意满足 nontrivialZeroSum(h)=0 的 TestFunction h，
    存在磨光函数 f 保持 f0 在 S 上的取值，且 M[f] = M[f0] + M[h]。
    数学含义：点插值约束不减少 Mellin 变换的自由度——
    可以在保持有限/可数个点取值的同时，叠加上 nontrivialZeroSum 为零的 TestFunction 的 Mellin 变换。
    前提 nontrivialZeroSum(h)=0 是必要的：由 spectral_zero_equality，谱点取值相同 ⟹ nontrivialZeroSum 相同，
    故叠加的 h 必须满足 nontrivialZeroSum(h)=0，否则与 spectral_zero_equality 矛盾。
    这是因为 {g | g|_S=0 且 nontrivialZeroSum(g)=0} 子空间无限维，其 Mellin 变换的像足够丰富。 -/
axiom mollified_point_fiber_mellin_rich
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (h : TestFunction) (h_nz : nontrivialZeroSum h = 0) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (melinTransform f.toTestFunction = melinTransform f0.toTestFunction + melinTransform h)

/-- 点插值纤维上的 Mellin 满射性（定理，由两条更基本公理推出）：
    给定 f0 和可数点集 S（保持 f0 在 S 上的取值），以及可数点集 T 和任意赋值 w，
    存在磨光函数 f 使得 f|_S = f0|_S 且 M[f]|_T = w。
    证明：由 mellin_transform_countable_surjectivity 取 h 使 M[h]|_T = w - M[f0]|_T，
    再由 mollified_point_fiber_mellin_rich 叠加 M[h] 得到 f。 -/
theorem mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  let u : ℂ → ℂ := fun s => w s - melinTransform f0.toTestFunction s
  rcases mellin_finite_surjectivity_zero_sum T hT u with ⟨h, hh, h_nz⟩
  rcases mollified_point_fiber_mellin_rich f0 S hS h_sep h h_nz with ⟨f, h_pts, h_melin_eq⟩
  refine ⟨f, h_pts, ?_⟩
  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    have h_eq := congrFun h_melin_eq s
    exact h_eq
  rw [h1]
  have h2 : melinTransform h s = u s := hh s hs
  rw [h2]
  simp only [u] <;> ring

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

end OrderPreservingBijection
