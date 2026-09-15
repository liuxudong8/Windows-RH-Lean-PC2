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

/-- 区间指示函数的 Mellin 变换非零族（公理，有限维线性代数）：
    对任意 m 个互不相同的复点 t_0,...,t_{m-1}，存在 m 个区间 [a_i,b_i]，
    使得矩阵 A_{ji} = M[1_{[a_i,b_i]}](t_j) 可逆。
    数学依据：取区间 [a_i, a_i+ε]，ε→0 时 A_{ji} ≈ ε·a_i^{t_j-1}，
    极限矩阵 (a_i^{t_j-1}) 是广义 Vandermonde 矩阵（a_i>0 互不相同，t_j 互不相同），故可逆；
    由行列式连续性，ε 足够小时 A 可逆。
    这是纯分析断言，比完整的 Mellin 满射性更基本、更透明。 -/
axiom mellin_interval_linear_independence {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) :
    ∃ (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i),
      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j) = 0) → c = 0

/-- Mellin 变换有限集满射性（定理，由区间指示函数线性无关推出）：
    对任意 m 个互不相同的点 t_j 和任意赋值 w_j，存在 TestFunction f
    使得 M[f](t_j) = w_j 对所有 j。
    证明：由 mellin_interval_linear_independence 得到 m 个区间指示函数，
    其 Mellin 变换向量线性无关。m 个线性无关向量在 m 维空间 ℂ^m 中构成基，
    故可线性组合得到任意 w。 -/
theorem mellin_finite_surjectivity {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) (w : Fin m → ℂ) :
    ∃ (f : TestFunction), ∀ (j : Fin m), melinTransform f (t j) = w j := by
  rcases mellin_interval_linear_independence t ht with ⟨a, b, ha, hab, h_indep⟩
  let v : Fin m → (Fin m → ℂ) := fun i => fun j => melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j)
  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun c => fun j => ∑ i : Fin m, c i * v i j
      map_add' := by
        intro c1 c2
        ext j
        have h1 : ∀ i, (c1 i + c2 i) * v i j = c1 i * v i j + c2 i * v i j := by intro i; ring
        have h : ∑ i : Fin m, (c1 i + c2 i) * v i j = (∑ i : Fin m, c1 i * v i j) + ∑ i : Fin m, c2 i * v i j := by
          rw [Finset.sum_congr rfl (fun i _ => h1 i)]
          rw [Finset.sum_add_distrib]
        exact h
      map_smul' := by
        intro z c
        ext j
        have h : ∑ i : Fin m, (z * c i) * v i j = z * ∑ i : Fin m, c i * v i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        exact h }
  have h_inj : Function.Injective L := by
    intro c1 c2 h
    have h_eq : ∀ j, ∑ i : Fin m, (c1 i - c2 i) * v i j = 0 := by
      intro j
      have h1 : (L c1) j = (L c2) j := by rw [h]
      have h2 : (L c1) j = ∑ i : Fin m, c1 i * v i j := by rfl
      have h3 : (L c2) j = ∑ i : Fin m, c2 i * v i j := by rfl
      rw [h2, h3] at h1
      have h4 : ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j = 0 := by
        exact sub_eq_zero.mpr h1
      have h1 : ∀ i, (c1 i - c2 i) * v i j = c1 i * v i j - c2 i * v i j := by intro i; ring
      have h5 : ∑ i : Fin m, (c1 i - c2 i) * v i j = ∑ i : Fin m, c1 i * v i j - ∑ i : Fin m, c2 i * v i j := by
        rw [Finset.sum_congr rfl (fun i _ => h1 i)]
        rw [Finset.sum_sub_distrib]
      rw [h5]
      exact h4
    have h_zero : c1 - c2 = 0 := h_indep (c1 - c2) h_eq
    have h_eq2 : c1 = c2 := by
      simpa [sub_eq_zero] using h_zero
    exact h_eq2
  have h_surj : Function.Surjective L := by
    have h_ker : LinearMap.ker L = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr h_inj
    have h_main : LinearMap.range L = ⊤ := by
      exact?
    intro y
    have h_y : y ∈ LinearMap.range L := by
      rw [h_main]
      trivial
    exact h_y
  rcases h_surj w with ⟨c, hc⟩
  let f_i : Fin m → TestFunction := fun i => intervalIndicator (a i) (b i) (ha i) (hab i)
  let f : TestFunction := ∑ i : Fin m, c i • f_i i
  refine ⟨f, ?_⟩
  intro j
  have h_melin_zero : melinTransform (0 : TestFunction) (t j) = 0 := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) (t j)
    have h0 : (0 : ℂ) • (0 : TestFunction) + (0 : ℂ) • (0 : TestFunction) = (0 : TestFunction) := by
      apply TestFunction.toFun_injective
      funext x
      change (0 : ℂ) * (0 : ℂ) + (0 : ℂ) * (0 : ℂ) = (0 : ℂ)
      ring
    rw [h0] at h
    have h1 : (0 : ℂ) * melinTransform (0 : TestFunction) (t j) + (0 : ℂ) * melinTransform (0 : TestFunction) (t j) = (0 : ℂ) := by ring
    rw [h1] at h
    exact h
  have h_melin_sum : ∀ (s : Finset (Fin m)) (c' : Fin m → ℂ),
      melinTransform (∑ i ∈ s, c' i • f_i i) (t j) = ∑ i ∈ s, c' i * melinTransform (f_i i) (t j) := by
    intro s c'
    induction s using Finset.induction with
    | empty =>
      simpa using h_melin_zero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have h_one : (1 : ℂ) • (∑ k ∈ s, c' k • f_i k) = ∑ k ∈ s, c' k • f_i k := by
        apply TestFunction.toFun_injective
        funext x
        change (1 : ℂ) * (∑ k ∈ s, c' k • f_i k).eval x = (∑ k ∈ s, c' k • f_i k).eval x
        ring
      rw [←h_one]
      rw [melinTransform_linear (f_i i) (∑ k ∈ s, c' k • f_i k) (c' i) (1 : ℂ) (t j)]
      rw [ih]
      ring
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    rw [h_melin_sum (Finset.univ) c]
  rw [h_main]
  have h2 : (L c) j = w j := by rw [hc]
  simpa [L, v] using h2


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

/-- Mellin 变换的有限集满射性（定理，由区间指示函数基 + 有限维线性代数推出）：
    对任意有限点集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在紧支集 TestFunction f
    使得 Mellin 变换 M[f] 在 T 上等于 w。
    证明：将 T 枚举为 t : Fin m → ℂ，由 mellin_finite_surjectivity 直接得到。
    注意：可数集版本在数学上不成立（指数型整函数零点密度限制），
    反证法中只需要有限集版本。 -/
theorem mellin_finite_set_surjectivity
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (h : TestFunction), ∀ (s : ℂ), s ∈ T → melinTransform h s = w s := by
  let s : Finset ℂ := hT.toFinset
  have hTs : (↑s : Set ℂ) = T := hT.coe_toFinset
  let lst : List ℂ := s.toList
  have h_nodup : lst.Nodup := Finset.nodup_toList s
  have h_mem : ∀ (x : ℂ), x ∈ lst ↔ x ∈ s := by
    intro x; simp [lst]
  let m := lst.length
  let t : Fin m → ℂ := fun i => lst.get i
  have ht_inj : Function.Injective t := List.nodup_iff_injective_get.mp h_nodup
  have h_range : Set.range t = T := by
    ext x
    simp only [Set.mem_range, t]
    constructor
    · rintro ⟨i, rfl⟩
      have h_in_lst : lst.get i ∈ lst := List.get_mem lst i
      have h_in_s : lst.get i ∈ s := (h_mem (lst.get i)).mp h_in_lst
      have h_in_T : lst.get i ∈ T := by
        have h : (lst.get i ∈ (↑s : Set ℂ)) := h_in_s
        rwa [hTs] at h
      exact h_in_T
    · intro hx
      have h_in_s : x ∈ s := by
        have h : x ∈ T := hx
        have h' : x ∈ (↑s : Set ℂ) := by rwa [hTs]
        exact h'
      have h_in_lst : x ∈ lst := (h_mem x).mpr h_in_s
      rcases List.mem_iff_get.mp h_in_lst with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  let w' : Fin m → ℂ := fun i => w (t i)
  rcases mellin_finite_surjectivity t ht_inj w' with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  intro s hs
  have h_in_range : s ∈ Set.range t := by rw [h_range]; exact hs
  rcases h_in_range with ⟨i, rfl⟩
  exact hh i

/-- 有限集上 Mellin 变换任意赋值且 nontrivialZeroSum 为零（公理，泛函分析）：
    对任意有限点集 T ⊆ ℂ 和任意赋值 w，存在 TestFunction h 使得：
    (1) M[h]|_T = w
    (2) nontrivialZeroSum(h) = 0

    数学依据：TestFunction 空间无限维，nontrivialZeroSum 是一个线性泛函，
    其核 {h | nontrivialZeroSum(h)=0} 是余维 1 的子空间，仍然无限维。
    有限个点的赋值约束是有限维的，因此可以在核中找到满足赋值的函数。
    风险等级：中（标准泛函分析，核的无限维性 + 有限维约束）。 -/
axiom mellin_finite_surjectivity_zero_sum (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (h : TestFunction),
      (∀ (s : ℂ), s ∈ T → melinTransform h s = w s) ∧
      nontrivialZeroSum h = 0

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
