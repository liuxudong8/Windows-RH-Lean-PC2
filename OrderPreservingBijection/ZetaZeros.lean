/-
  ζ 零点基础设施模块
-/

import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OrderPreservingBijection

open Complex
open Filter
open scoped Interval
open scoped Real
open scoped Topology

/-- 非平凡零点集合的覆盖枚举（真证，2026-10-02）：
    临界带零点集 S = riemannZetaZeros ∩ {s | 0 < s.re ∧ s.re < 1} 可数，
    故存在 ℕ → ℂ 的满射覆盖枚举（枚举值不一定落在 S 内，也不要求互异）。
    集合论依据：可数集有 ℕ 的满射覆盖（空集情形真空成立），
    不依赖"ζ 存在非平凡零点"（S.Nonempty）或"零点无限"（Hadamard）。
    S.Countable 由 mathlib 的"紧集 ∩ 零点集有限"（inter_riemannZetaZeros_finite）给出。 -/
theorem nontrivialZeroEnum_covers_exists :
    ∃ (e : ℕ → ℂ),
      ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), e n = ρ := by
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
  by_cases hne : S.Nonempty
  · rcases Set.Countable.exists_eq_range hS_count hne with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro ρ hz hre1 hre2
    have hρS : ρ ∈ S := by
      dsimp [S]
      exact ⟨mem_riemannZetaZeros.mpr hz, hre1, hre2⟩
    have hρrange : ρ ∈ Set.range e := by
      rw [← he]
      exact hρS
    exact Set.mem_range.mp hρrange
  · refine ⟨fun _ => 0, ?_⟩
    intro ρ hz hre1 hre2
    exfalso
    apply hne
    refine ⟨ρ, ?_⟩
    dsimp [S]
    exact ⟨mem_riemannZetaZeros.mpr hz, hre1, hre2⟩

/-- 全枚举（覆盖 + 单射 + 枚举值全在临界带）存在性。
    【可改正的遗留，2026-10-02 精化审计】
    覆盖分量已由 nontrivialZeroEnum_covers_exists 真证（可数集满射覆盖，无需额外前提）。
    剩余缺口（数论级，mathlib 无现成定理，非机械）：
      (i)  S.Nonempty：ζ 存在非平凡零点（临界带零点非空）——数学依据：
           ζ(1/2 ± 14.13…i) = 0（Hadamard 因子分解 / 数值事实），mathlib 无形式化；
      (ii) 单射 + range e ⊆ S：需要 S 无限（Hadamard/Hardy 级定理，mathlib 无）。
      [i+ii 合起来即"存在双射 ℕ ↔ S"，等价于 S 可数无限。]
    用途现状（2026-10-02 核实）：仅 tsum 精确层使用——stage_4 的
    nontrivialZeroSum_pair_localization / zero_side_melin_localization
    （后者无调用者）依赖 nontrivialZeroEnum_covers_all / _injective / _are_zeros；
    反证主链 off_critical_zero_tail_dominated 证明体 unfold nontrivialZeroSum 后
    纯 contourZeroFinset + farZeroSubtype 子类型 tsum，已完全绕开 ℕ 枚举。
    退役路径：P0.3 将 tsum 精确层子类型化后，本遗留可整体删除。 -/
theorem nontrivialZeroEnum_exists :
    ∃ (e : ℕ → ℂ),
      (Function.Injective e) ∧
      (∀ (n : ℕ), _root_.riemannZeta (e n) = 0 ∧ 0 < (e n).re ∧ (e n).re < 1) ∧
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), e n = ρ) := by
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

/-- Dirichlet eta 函数在 Re s > 1 的级数表示与恒等式 η(s) = (1 - 2^(1-s))·ζ(s)。
这是 `riemannZeta_neg_on_Ioo`（ζ(x) < 0 for 0 < x < 1）证明的基础步：
对实 x ∈ (0,1) 有 2^(1-x) > 1，而交错级数 η(x) > 0（Leibniz）。-/
lemma eta_eq_mul_riemannZeta {s : ℂ} (hs : 1 < re s) :
    (∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hζ : riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hs
  let f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s
  let A : ℂ := ∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s
  let B : ℂ := ∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s
  have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  have hsum_all : Summable f := by
    simpa [f, Function.comp_def] using (h0.comp_injective Nat.succ_injective)
  have hA_sum : Summable (fun k : ℕ => 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s) := by
    have hg : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have h' := hsum_all.comp_injective hg
    simpa [f, Function.comp_def] using h'
  have hB_sum : Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) := by
    have hg : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      have h' : 2 * a = 2 * b := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
    have h' := hsum_all.comp_injective hg
    simpa [f, Function.comp_def] using h'
  -- 偶部：1/(2(k+1))^s = 2^(-s) · 1/(k+1)^s
  have hpt : ∀ k : ℕ, (1 : ℂ) / (2 * ((k : ℂ) + 1)) ^ s = 2 ^ (-s) * (1 / ((k : ℂ) + 1) ^ s) := by
    intro k
    have hcp : ((2 : ℂ) * ((k : ℂ) + 1)) ^ (-s) = (2 : ℂ) ^ (-s) * ((k : ℂ) + 1) ^ (-s) := by
      simpa using
        (mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := ((k : ℝ) + 1)) (by norm_num) (by positivity) (-s))
    have hk : ((k : ℂ) + 1) ^ (-s) = 1 / ((k : ℂ) + 1) ^ s := by
      rw [cpow_neg]
      simp [one_div]
    calc
      (1 : ℂ) / (2 * ((k : ℂ) + 1)) ^ s = (2 * ((k : ℂ) + 1)) ^ (-s) := by
        rw [one_div, ← cpow_neg]
      _ = ((2 : ℂ) * ((k : ℂ) + 1)) ^ (-s) := rfl
      _ = (2 : ℂ) ^ (-s) * ((k : ℂ) + 1) ^ (-s) := hcp
      _ = 2 ^ (-s) * (1 / ((k : ℂ) + 1) ^ s) := by rw [hk]
  -- 偶部 tsum 与 B 的 tsum 在 pointwise ring 意义下相同
  have hB_eq_tsum : (∑' k : ℕ, 1 / (2 * ((k : ℂ) + 1)) ^ s) = B := by
    apply tsum_congr
    intro k
    have hb : 2 * ((k : ℂ) + 1) = (((2 * k + 1 : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    rw [hb]
  have h_even : (∑' k : ℕ, 1 / (2 * ((k : ℂ) + 1)) ^ s) = 2 ^ (-s) * riemannZeta s := by
    calc
      (∑' k : ℕ, 1 / (2 * ((k : ℂ) + 1)) ^ s)
          = ∑' k : ℕ, 2 ^ (-s) * (1 / ((k : ℂ) + 1) ^ s) := by
            congr 1 with k; exact hpt k
      _ = 2 ^ (-s) * (∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ s) := by rw [tsum_mul_left]
      _ = 2 ^ (-s) * riemannZeta s := by rw [hζ]
  have hB_even : B = ∑' k : ℕ, 1 / (2 * ((k : ℂ) + 1)) ^ s := by
    rw [← hB_eq_tsum]
  have hzeta_split : riemannZeta s = A + B := by
    have hAB : HasSum f (A + B) := hA_sum.hasSum.even_add_odd hB_sum.hasSum
    have hs_all : HasSum f (riemannZeta s) := by
      rw [hζ]
      exact hsum_all.hasSum
    exact HasSum.unique hs_all hAB
  have h_odd : A = (1 - 2 ^ (-s)) * riemannZeta s := by
    calc
      A = riemannZeta s - B := by
        rw [hzeta_split]
        ring
      _ = riemannZeta s - 2 ^ (-s) * riemannZeta s := by rw [hB_even, h_even]
      _ = (1 - 2 ^ (-s)) * riemannZeta s := by ring
  have h_eta_sum : HasSum (fun n : ℕ => (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) (A - B) := by
    let g : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s
    have hA2 : HasSum (fun k : ℕ => g (2 * k)) A := by
      apply HasSum.congr_fun hA_sum.hasSum
      intro k
      simp [g, pow_mul, neg_sq]
    have hBneg : HasSum (fun k : ℕ => -((1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)) (-B) := by
      change HasSum (fun k : ℕ => -((1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s))
        (-(∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s))
      simpa using hB_sum.hasSum.neg
    have hB2 : HasSum (fun k : ℕ => g (2 * k + 1)) (-B) := by
      apply HasSum.congr_fun hBneg
      intro k
      simp [g, pow_succ, pow_mul, neg_sq, neg_div]
    have hg' : HasSum g (A + -B) := hA2.even_add_odd hB2
    simpa [g, sub_eq_add_neg] using hg'
  have h_eta : (∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) = A - B :=
    h_eta_sum.tsum_eq
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h2mul : (2 : ℂ) * 2 ^ (-s) = 2 ^ (1 - s) := by
    calc
      (2 : ℂ) * 2 ^ (-s) = 2 ^ (1 : ℂ) * 2 ^ (-s) := by rw [cpow_one]
      _ = (2 : ℂ) ^ (1 + -s) := by rw [cpow_add (x := (2 : ℂ)) 1 (-s) h2]
      _ = (2 : ℂ) ^ (1 - s) := by rfl
  calc
    (∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) = A - B := h_eta
    _ = (1 - 2 ^ (-s)) * riemannZeta s - 2 ^ (-s) * riemannZeta s := by rw [h_odd, hB_even, h_even]
    _ = (1 - 2 * 2 ^ (-s)) * riemannZeta s := by ring
    _ = (1 - 2 ^ (1 - s)) * riemannZeta s := by rw [h2mul]

/-! ### η 的成对级数：解析延拓与实轴符号 -/

/-- 成对项 1/(2k+1)^s - 1/(2k+2)^s（Re s > 0 时绝对收敛）。 -/
noncomputable def etaPairTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

/-- 成对 eta 级数：对 0 < re s 局部一致收敛，且等于 η(s) = ∑(-1)^n/(n+1)^s。 -/
noncomputable def etaPaired (s : ℂ) : ℂ :=
  ∑' k : ℕ, etaPairTerm k s

/-- cpow 在正实轴上的积分表示（FTC）：(b)^(-s) - (a)^(-s) = -s·∫_a^b x^(-s-1)。 -/
lemma cpow_real_sub_integral {s : ℂ} (hs : s ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b : ℂ) ^ (-s) - (a : ℂ) ^ (-s) = -s * ∫ x in a..b, (x : ℂ) ^ (-s - 1) := by
  have hder : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hne : x ≠ 0 := ne_of_gt hx0
    have hns : -s ≠ 0 := neg_ne_zero.mpr hs
    simpa using (hasDerivAt_ofReal_cpow_const hne hns)
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
    intro x hx
    apply (continuousAt_ofReal_cpow_const x (-s - 1) (Or.inr ?_)).continuousWithinAt
    intro h
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    linarith
  have hcont : ContinuousOn (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hc.const_mul (-s)
  have hcont' : ContinuousOn (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (Set.uIcc a b) := by
    rwa [Set.uIcc_of_le hab]
  have hint : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) MeasureTheory.volume a b :=
    hcont'.intervalIntegrable
  have hder' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      rwa [Set.uIcc_of_le hab] at hx
    exact hder x hx'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) hder' hint
  calc
    (b : ℂ) ^ (-s) - (a : ℂ) ^ (-s) = ∫ x in a..b, -s * (x : ℂ) ^ (-s - 1) := hFTC.symm
    _ = -s * ∫ x in a..b, (x : ℂ) ^ (-s - 1) := by
      rw [intervalIntegral.integral_const_mul]

/-- 成对项的模界：|(2k+1)^(-y) - (2k+2)^(-y)| ≤ ‖y‖·(2k+1)^(-re y - 1)。 -/
lemma norm_etaPairTerm_le {y : ℂ} (hy : 0 < y.re) (k : ℕ) :
    ‖etaPairTerm k y‖ ≤ ‖y‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1)) := by
  let a : ℝ := (2 * k + 1 : ℝ)
  let b : ℝ := (2 * k + 2 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; norm_num
  have hdiff := cpow_real_sub_integral (s := y)
    (hs := by
      intro hy0
      have : (0 : ℝ) < (0 : ℝ) := by simpa [hy0] using hy
      exact (lt_irrefl _ this))
    (a := a) (b := b) ha hab
  have hterm : etaPairTerm k y = y * ∫ x in a..b, (x : ℂ) ^ (-y - 1) := by
    calc
      etaPairTerm k y = (a : ℂ) ^ (-y) - (b : ℂ) ^ (-y) := by simp [etaPairTerm, a, b]
      _ = -((b : ℂ) ^ (-y) - (a : ℂ) ^ (-y)) := by ring
      _ = y * ∫ x in a..b, (x : ℂ) ^ (-y - 1) := by
        rw [hdiff]
        ring
  have hni : ‖∫ x in a..b, (x : ℂ) ^ (-y - 1)‖ ≤
      ∫ x in a..b, ‖(x : ℂ) ^ (-y - 1)‖ := by
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hnorm : ∀ x ∈ Set.uIcc a b, ‖(x : ℂ) ^ (-y - 1)‖ = x ^ (-y.re - 1) := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      rwa [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx'.1
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  have hineq : ∫ x in a..b, ‖(x : ℂ) ^ (-y - 1)‖ ≤ (b - a) * a ^ (-y.re - 1) := by
    have hz : -y.re - 1 ≤ 0 := by linarith [hy]
    have hfc : ContinuousOn (fun x : ℝ => x ^ (-y.re - 1)) (Set.Icc a b) := by
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      exact Or.inl (ne_of_gt hx0)
    have hf_int : IntervalIntegrable (fun x : ℝ => x ^ (-y.re - 1)) MeasureTheory.volume a b :=
      hfc.intervalIntegrable_of_Icc hab
    have hg_int : IntervalIntegrable (fun _ : ℝ => a ^ (-y.re - 1)) MeasureTheory.volume a b :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => a ^ (-y.re - 1)) (Set.Icc a b)).intervalIntegrable_of_Icc hab
    calc
      ∫ x in a..b, ‖(x : ℂ) ^ (-y - 1)‖ = ∫ x in a..b, x ^ (-y.re - 1) := by
        exact intervalIntegral.integral_congr hnorm
      _ ≤ ∫ x in a..b, a ^ (-y.re - 1) := by
        refine intervalIntegral.integral_mono_on (hab := hab) (hf := hf_int) (hg := hg_int) ?_
        intro x hx
        exact Real.rpow_le_rpow_of_nonpos ha hx.1 hz
      _ = (b - a) * a ^ (-y.re - 1) := by
        simp [intervalIntegral.integral_const]
  calc
    ‖etaPairTerm k y‖ = ‖y * ∫ x in a..b, (x : ℂ) ^ (-y - 1)‖ := by rw [hterm]
    _ = ‖y‖ * ‖∫ x in a..b, (x : ℂ) ^ (-y - 1)‖ := by rw [norm_mul]
    _ ≤ ‖y‖ * ∫ x in a..b, ‖(x : ℂ) ^ (-y - 1)‖ := mul_le_mul_of_nonneg_left hni (norm_nonneg _)
    _ ≤ ‖y‖ * ((b - a) * a ^ (-y.re - 1)) := mul_le_mul_of_nonneg_left hineq (norm_nonneg _)
    _ = ‖y‖ * a ^ (-y.re - 1) := by dsimp [a, b]; ring
    _ = ‖y‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1)) := by
      dsimp [a]
      norm_num [Nat.cast_mul, Nat.cast_add]
/-- 成对 eta 级数在 Re s > 0 逐点绝对收敛。 -/
lemma summable_etaPairTerm {y : ℂ} (hy : 0 < y.re) :
    Summable (fun k : ℕ => etaPairTerm k y) := by
  refine Summable.of_norm_bounded
    (g := fun k : ℕ => ‖y‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1))) ?_ ?_
  · have hp : -y.re - 1 < -1 := by linarith [hy]
    have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-y.re - 1)) :=
      (Real.summable_nat_rpow).mpr hp
    have hsub : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1)) := by
      have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
        intro a b h
        have h' : 2 * a = 2 * b := Nat.add_right_cancel h
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
      have h' := hnat.comp_injective hinj
      simpa [Function.comp_def] using h'
    exact hsub.mul_left ‖y‖
  · intro k
    exact norm_etaPairTerm_le hy k

/-- 成对重排等式：对 Re s > 1，η(s) = ∑' (-1)^n/(n+1)^s = ∑' [(2k+1)^(-s) - (2k+2)^(-s)]。
这是 identity theorem 延拓的『在开集上相等』输入。 -/
lemma etaPaired_eq_eta {s : ℂ} (hs : 1 < re s) :
    etaPaired s = ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s := by
  let g : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s
  have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  have hsucc : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using (h0.comp_injective Nat.succ_injective)
  have hg_sum : Summable g := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re)) ?_ ?_
    · have hp : -s.re < -1 := by linarith [hs]
      have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
        (Real.summable_nat_rpow).mpr hp
      have h' := hnat.comp_injective Nat.succ_injective
      simpa only [Function.comp_def] using h'
    · intro n
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hnorm : ‖(((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ s.re := by
        convert norm_cpow_eq_rpow_re_of_pos hn s using 1
        · norm_cast
      calc
        ‖g n‖ = ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ := by simp [g, Nat.cast_add, Nat.cast_one]
        _ = 1 / ‖(((n + 1 : ℕ) : ℂ) ^ s)‖ := by rw [norm_div, norm_one]
        _ = 1 / ((n + 1 : ℕ) : ℝ) ^ s.re := by rw [hnorm]
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
          rw [one_div, Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)) s.re]
  have hpair : ∀ k : ℕ, etaPairTerm k s = g (2 * k) + g (2 * k + 1) := by
    intro k
    have h1 : ((2 * k : ℕ) : ℂ) + 1 = ((2 * k + 1 : ℕ) : ℂ) := by
      norm_cast
    have h2 : ((2 * k + 1 : ℕ) : ℂ) + 1 = ((2 * k + 2 : ℕ) : ℂ) := by
      norm_cast
    calc
      etaPairTerm k s = ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s) := rfl
      _ = g (2 * k) + g (2 * k + 1) := by
        dsimp [g]
        rw [h1, h2]
        have hpow_even : (-1 : ℂ) ^ (2 * k) = 1 := by
          simp [pow_mul, neg_sq, one_pow]
        have hpow_odd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, hpow_even]
          simp
        rw [hpow_even, hpow_odd]
        simp [cpow_neg, div_eq_mul_inv]
        ring
  have heven : Summable (fun k : ℕ => g (2 * k)) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
    exact hg_sum.comp_injective hinj
  have hodd : Summable (fun k : ℕ => g (2 * k + 1)) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      have h' : 2 * a = 2 * b := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
    exact hg_sum.comp_injective hinj
  calc
    etaPaired s = ∑' k : ℕ, etaPairTerm k s := rfl
    _ = ∑' k : ℕ, (g (2 * k) + g (2 * k + 1)) := by
      congr 1 with k
      exact hpair k
    _ = (∑' k : ℕ, g (2 * k)) + ∑' k : ℕ, g (2 * k + 1) := by
      exact heven.tsum_add hodd
    _ = ∑' n : ℕ, g n := by
      have hsum : HasSum g ((∑' k : ℕ, g (2 * k)) + ∑' k : ℕ, g (2 * k + 1)) :=
        heven.hasSum.even_add_odd hodd.hasSum
      exact hsum.tsum_eq.symm
    _ = ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s := rfl

/-! ### etaPaired 在 Re > 0 半平面解析：逐项导数与局部一致可和 -/

/-- 固定正实底 `a`，`z ↦ a ^ (-z)` 的导数。 -/
lemma hasDerivAt_cpow_neg_const_of_pos (a : ℕ) (ha : 0 < a) (s : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℕ) : ℂ) ^ (-z))
      (-(((a : ℕ) : ℂ) ^ (-s)) * Complex.log ((a : ℕ) : ℂ)) s := by
  have hf : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) s := hasDerivAt_neg' s
  have hc : ((a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  simpa [mul_comm, mul_left_comm, mul_assoc] using (hf.const_cpow (Or.inl hc))

/-- `etaPairTerm k` 的导数项。 -/
noncomputable def etaPairTermDeriv (k : ℕ) (s : ℂ) : ℂ :=
  -(((2 * k + 1 : ℕ) : ℂ) ^ (-s)) * Complex.log ((2 * k + 1 : ℕ) : ℂ)
    + (((2 * k + 2 : ℕ) : ℂ) ^ (-s)) * Complex.log ((2 * k + 2 : ℕ) : ℂ)

lemma hasDerivAt_etaPairTerm (k : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => etaPairTerm k z) (etaPairTermDeriv k s) s := by
  have h1 : HasDerivAt (fun z : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-z))
      (-(((2 * k + 1 : ℕ) : ℂ) ^ (-s)) * Complex.log ((2 * k + 1 : ℕ) : ℂ)) s :=
    hasDerivAt_cpow_neg_const_of_pos (2 * k + 1) (by omega) s
  have h2 : HasDerivAt (fun z : ℂ => ((2 * k + 2 : ℕ) : ℂ) ^ (-z))
      (-(((2 * k + 2 : ℕ) : ℂ) ^ (-s)) * Complex.log ((2 * k + 2 : ℕ) : ℂ)) s :=
    hasDerivAt_cpow_neg_const_of_pos (2 * k + 2) (by omega) s
  unfold etaPairTerm etaPairTermDeriv
  convert! (h1.sub h2) using 1
  · simp [sub_eq_add_neg]

/-- `‖log ((a:ℕ):ℂ)‖ = log (a:ℝ)`（正实数）。 -/
lemma norm_log_natCast (a : ℕ) (ha : 0 < a) :
    ‖Complex.log ((a : ℕ) : ℂ)‖ = Real.log (a : ℝ) := by
  rw [← Complex.natCast_log]
  exact (RCLike.norm_ofReal (K := ℂ) (Real.log (a : ℝ))).trans
    (abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt ha) : 1 ≤ (a : ℝ))))

/-- 导数范数界：‖etaPairTermDeriv k y‖ ≤ (‖y‖·log(2k+2)+1)·(2k+1)^(-y.re-1)。 -/
lemma norm_deriv_etaPairTerm_le {y : ℂ} (hy : 0 < y.re) (k : ℕ) :
    ‖etaPairTermDeriv k y‖
      ≤ (‖y‖ * Real.log (2 * k + 2 : ℝ) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := by
  let A : ℂ := ((2 * k + 1 : ℕ) : ℂ) ^ (-y)
  let B : ℂ := ((2 * k + 2 : ℕ) : ℂ) ^ (-y)
  have hlogA : ‖Complex.log ((2 * k + 1 : ℕ) : ℂ)‖ = Real.log (2 * k + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using norm_log_natCast (2 * k + 1) (by omega)
  have hlogB : ‖Complex.log ((2 * k + 2 : ℕ) : ℂ)‖ = Real.log (2 * k + 2 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using norm_log_natCast (2 * k + 2) (by omega)
  have hA : ‖A‖ = ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re) := by
    convert norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < ((2 * k + 1 : ℕ) : ℝ)) (-y) using 2
    · norm_cast
    · simp
  have hdiff : ‖B - A‖ ≤ ‖y‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := by
    calc
      ‖B - A‖ = ‖A - B‖ := by
        rw [← norm_neg]
        congr 1
        ring
      _ = ‖etaPairTerm k y‖ := by simp [etaPairTerm, A, B]
      _ ≤ ‖y‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := norm_etaPairTerm_le hy k
  have hlogdiff : Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ)
      ≤ (2 * k + 1 : ℝ)⁻¹ := by
    have hx : 0 < (2 * k + 2 : ℝ) / (2 * k + 1 : ℝ) := by positivity
    have hb := Real.log_le_sub_one_of_pos hx
    -- log((2k+2)/(2k+1)) ≤ (2k+2)/(2k+1) - 1 = 1/(2k+1)
    have hlogdiv : Real.log ((2 * k + 2 : ℝ) / (2 * k + 1 : ℝ)) =
        Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ) := by
      exact Real.log_div (by positivity : (2 * k + 2 : ℝ) ≠ 0)
        (by positivity : (2 * k + 1 : ℝ) ≠ 0)
    rw [← hlogdiv]
    have hsub : (2 * k + 2 : ℝ) / (2 * k + 1 : ℝ) - 1 = (2 * k + 1 : ℝ)⁻¹ := by
      field_simp [show (2 * k + 1 : ℝ) ≠ 0 by positivity]
      ring
    rw [← hsub]
    exact hb
  have hlog2 : 0 ≤ Real.log (2 * k + 2 : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * k + 2))
  calc
    ‖etaPairTermDeriv k y‖
        = ‖-A * Complex.log ((2 * k + 1 : ℕ) : ℂ) + B * Complex.log ((2 * k + 2 : ℕ) : ℂ)‖ := by
          rw [etaPairTermDeriv]
    _ = ‖Complex.log ((2 * k + 2 : ℕ) : ℂ) * (B - A)
        + (Complex.log ((2 * k + 2 : ℕ) : ℂ) - Complex.log ((2 * k + 1 : ℕ) : ℂ)) * A‖ := by
          congr 1
          ring
    _ ≤ ‖Complex.log ((2 * k + 2 : ℕ) : ℂ) * (B - A)‖
        + ‖(Complex.log ((2 * k + 2 : ℕ) : ℂ) - Complex.log ((2 * k + 1 : ℕ) : ℂ)) * A‖ := by
          exact norm_add_le _ _
    _ ≤ Real.log (2 * k + 2 : ℝ) * ‖B - A‖
        + ‖Complex.log ((2 * k + 2 : ℕ) : ℂ) - Complex.log ((2 * k + 1 : ℕ) : ℂ)‖ * ‖A‖ := by
          rw [norm_mul]
          rw [hlogB]
          rw [norm_mul]
    _ ≤ Real.log (2 * k + 2 : ℝ) * ‖B - A‖
        + (Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ)) * ‖A‖ := by
          have hlogdiff_c : ‖Complex.log ((2 * k + 2 : ℕ) : ℂ) - Complex.log ((2 * k + 1 : ℕ) : ℂ)‖
              ≤ Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ) := by
            rw [← Complex.natCast_log, ← Complex.natCast_log, ← Complex.ofReal_sub]
            norm_cast
            rw [Real.norm_eq_abs]
            rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log
                (by positivity : 0 < ((2 * k + 1 : ℕ) : ℝ))
                (by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2))))]
          exact add_le_add_right (mul_le_mul_of_nonneg_right hlogdiff_c (norm_nonneg A)) _
    _ ≤ Real.log (2 * k + 2 : ℝ) * (‖y‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1))
        + (2 * k + 1 : ℝ)⁻¹ * ‖A‖ := by
          calc
            Real.log (2 * k + 2 : ℝ) * ‖B - A‖ + (Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ)) * ‖A‖
                ≤ Real.log (2 * k + 2 : ℝ) * (‖y‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1))
                    + (Real.log (2 * k + 2 : ℝ) - Real.log (2 * k + 1 : ℝ)) * ‖A‖ := by
                  exact add_le_add_left (mul_le_mul_of_nonneg_left hdiff hlog2) _
            _ ≤ Real.log (2 * k + 2 : ℝ) * (‖y‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1))
                    + (2 * k + 1 : ℝ)⁻¹ * ‖A‖ := by
                  exact add_le_add_right (mul_le_mul_of_nonneg_right hlogdiff (norm_nonneg A)) _
    _ = (‖y‖ * Real.log (2 * k + 2 : ℝ) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := by
          rw [hA]
          -- (2k+1)⁻¹ · (2k+1)^(-y.re) = (2k+1)^(-y.re-1)
          have hrpow : (2 * k + 1 : ℝ)⁻¹ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re)
              = ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := by
            have hx : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
            calc
              (2 * k + 1 : ℝ)⁻¹ * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re)
                  = ((2 * k + 1 : ℕ) : ℝ) ^ (-1 : ℝ) * ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re) := by
                    rw [← Real.rpow_neg_one (2 * k + 1 : ℝ)]
                    norm_cast
              _ = ((2 * k + 1 : ℕ) : ℝ) ^ (-1 + -y.re) := by
                    rw [← Real.rpow_add hx]
              _ = ((2 * k + 1 : ℕ) : ℝ) ^ (-y.re - 1) := by
                    congr 1
                    ring
          rw [hrpow]
          ring

/-! ### etaPaired 在 Re s > 0 解析（逐项导数 + 局部一致可和） -/

/-- etaPaired 在右半平面 {s | 0 < re s} 解析。
在每点 y 取小圆盘 t（半径 y.re/2），圆盘内 Re z ≥ y.re/2，‖z‖ ≤ ‖y‖ + y.re/2，
用 `hasDerivAt_tsum_of_isPreconnected` 逐项求导；范数界中 log 因子用
`Real.log_le_rpow_div` 换成 rpow，得到对 k 可和的上界。 -/
lemma analyticOnNhd_etaPaired : AnalyticOnNhd ℂ etaPaired {s : ℂ | 0 < re s} := by
  intro y hy
  let δ : ℝ := y.re / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos hy (by norm_num : (0 : ℝ) < 2)
  let t : Set ℂ := Metric.ball y δ
  have ht_open : IsOpen t := by
    simpa [t] using (Metric.isOpen_ball : IsOpen (Metric.ball y δ))
  have hyt : y ∈ t := by
    simpa [t] using (Metric.mem_ball_self hδ : y ∈ Metric.ball y δ)
  have ht_pre : IsPreconnected t := by
    simpa [t] using (Metric.isPreconnected_ball (x := y) (r := δ))
  let R : ℝ := ‖y‖ + δ
  let u : ℕ → ℝ := fun k =>
    (R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)
  have hsu : Summable u := by
    have hp1 : -δ - 1 < -1 := by linarith [hδ]
    have hnat1 : Summable (fun n : ℕ => (n : ℝ) ^ (-δ - 1)) :=
      (Real.summable_nat_rpow).mpr hp1
    have hodd1 : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
      have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
        intro a b h
        have h' : 2 * a = 2 * b := Nat.add_right_cancel h
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
      simpa [Function.comp_def] using (hnat1.comp_injective hinj)
    have hp2 : -δ / 2 - 1 < -1 := by linarith [hδ]
    have hnat2 : Summable (fun n : ℕ => (n : ℝ) ^ (-δ / 2 - 1)) :=
      (Real.summable_nat_rpow).mpr hp2
    have hodd2 : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1)) := by
      have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
        intro a b h
        have h' : 2 * a = 2 * b := Nat.add_right_cancel h
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
      simpa [Function.comp_def] using (hnat2.comp_injective hinj)
    let C : ℝ := R * (2 : ℝ) ^ (δ / 2) / (δ / 2)
    have hC : Summable (fun k : ℕ => C * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1)) :=
      hodd2.mul_left C
    have hsum : Summable (fun k : ℕ =>
        C * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1) + ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)) :=
      hC.add hodd1
    refine Summable.of_nonneg_of_le ?_ ?_ hsum
    · intro k
      dsimp [u]
      positivity
    · intro k
      -- u k = R·(2k+2)^(δ/2)/(δ/2)·(2k+1)^(-δ-1) + (2k+1)^(-δ-1)
      -- ≤ C·(2k+1)^(-δ/2-1) + (2k+1)^(-δ-1)
      have hlogb : (2 * k + 2 : ℝ) ^ (δ / 2) ≤ (2 : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2) := by
        have hle : (2 * k + 2 : ℝ) ≤ (2 : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
          norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
          linarith
        have hnonneg : 0 ≤ (2 * k + 2 : ℝ) := by positivity
        have hb2 : 0 ≤ (2 : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by positivity
        calc
          (2 * k + 2 : ℝ) ^ (δ / 2) ≤ ((2 : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) ^ (δ / 2) := by
            exact Real.rpow_le_rpow hnonneg hle (by linarith [hδ])
          _ = (2 : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2) := by
            exact Real.mul_rpow (by positivity) (by positivity)
      have hpow : ((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)
          = ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1) := by
        have hx : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.rpow_add hx]
        congr 1
        ring
      calc
        u k = R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)
            + ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
              dsimp [u]
              ring
        _ ≤ C * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1) + ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
          have h1 : R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)
              ≤ C * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1) := by
            dsimp [C]
            have hnonneg2 : 0 ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
              Real.rpow_nonneg (by positivity : 0 ≤ ((2 * k + 1 : ℕ) : ℝ)) (-δ - 1)
            have hnonneg3 : 0 ≤ (2 : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2) := by positivity
            calc
              R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)
                  = R * ((2 * k + 2 : ℝ) ^ (δ / 2)) / (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
                    ring
              _ ≤ R * ((2 : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2)) / (δ / 2)
                    * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
                    exact mul_le_mul_of_nonneg_right
                      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogb (by dsimp [R]; positivity))
                        (by dsimp [δ]; positivity))
                      (Real.rpow_nonneg (by positivity : 0 ≤ ((2 * k + 1 : ℕ) : ℝ)) (-δ - 1))
              _ = C * (((2 * k + 1 : ℕ) : ℝ) ^ (δ / 2) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
                    dsimp [C]
                    ring
              _ = C * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ / 2 - 1) := by rw [hpow]
          exact add_le_add h1 (le_refl (((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)))
  have hder : ∀ k z, z ∈ t → HasDerivAt (fun w : ℂ => etaPairTerm k w) (etaPairTermDeriv k z) z :=
    fun k z hz => hasDerivAt_etaPairTerm k z
  have hbound : ∀ k z, z ∈ t → ‖etaPairTermDeriv k z‖ ≤ u k := by
    intro k z hz
    have hzre : 0 < z.re := by
      have hd : dist z y < δ := hz
      have hrz : ‖z.re - y.re‖ ≤ ‖z - y‖ := by simpa using (Complex.abs_re_le_norm (z - y))
      have hthis : |z.re - y.re| < y.re / 2 := by
        simpa [δ] using (lt_of_le_of_lt hrz (by simpa [dist_eq_norm] using hd))
      linarith [abs_lt.mp hthis, hy]
    have hzed : δ ≤ z.re := by
      have hd : dist z y < δ := hz
      have hrz : ‖z.re - y.re‖ ≤ ‖z - y‖ := by simpa using (Complex.abs_re_le_norm (z - y))
      have hthis : |z.re - y.re| < y.re / 2 := by
        simpa [δ] using (lt_of_le_of_lt hrz (by simpa [dist_eq_norm] using hd))
      change y.re / 2 ≤ z.re
      linarith [abs_lt.mp hthis]
    have hzR : ‖z‖ ≤ R := by
      have hd : dist z y < δ := hz
      have hnorm : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
        simpa using (norm_add_le (z - y) y)
      have hd' : ‖z - y‖ ≤ δ := le_of_lt (by simpa [dist_eq_norm] using hd)
      change ‖z‖ ≤ ‖y‖ + δ
      linarith
    have hn := norm_deriv_etaPairTerm_le hzre k
    -- 放缩 ‖z‖·log(2k+2)+1 ≤ R·(2k+2)^(δ/2)/(δ/2)+1，且 (2k+1)^(-z.re-1) ≤ (2k+1)^(-δ-1)
    have hlog : Real.log (2 * k + 2 : ℝ) ≤ (2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2) :=
      Real.log_le_rpow_div (by positivity : 0 ≤ (2 * k + 2 : ℝ)) (by linarith [hδ])
    have hpz : ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
      have hx : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
      have hze : -z.re - 1 ≤ -δ - 1 := by linarith [hzed]
      have hlogp : 0 ≤ Real.log ((2 * k + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by norm_num : 1 ≤ ((2 * k + 1 : ℕ) : ℝ))
      have hmono : Real.log ((2 * k + 1 : ℕ) : ℝ) * (-z.re - 1)
          ≤ Real.log ((2 * k + 1 : ℕ) : ℝ) * (-δ - 1) :=
        mul_le_mul_of_nonneg_left hze hlogp
      calc
        ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1)
            = Real.exp (Real.log ((2 * k + 1 : ℕ) : ℝ) * (-z.re - 1)) := by
              rw [Real.rpow_def_of_pos hx]
        _ ≤ Real.exp (Real.log ((2 * k + 1 : ℕ) : ℝ) * (-δ - 1)) := Real.exp_le_exp.mpr hmono
        _ = ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
              rw [Real.rpow_def_of_pos hx]
    have h1 : ‖z‖ * Real.log (2 * k + 2 : ℝ) ≤ R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) := by
      calc
        ‖z‖ * Real.log (2 * k + 2 : ℝ) ≤ R * Real.log (2 * k + 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hzR (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * k + 2)))
        _ ≤ R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) := by
          exact mul_le_mul_of_nonneg_left hlog (by dsimp [R]; positivity)
    have h2 : (‖z‖ * Real.log (2 * k + 2 : ℝ) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1)
        ≤ (R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
      calc
        (‖z‖ * Real.log (2 * k + 2 : ℝ) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1)
            ≤ (R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1) := by
              exact mul_le_mul_of_nonneg_right (add_le_add h1 (le_refl 1))
                (Real.rpow_nonneg (by positivity : 0 ≤ ((2 * k + 1 : ℕ) : ℝ)) (-z.re - 1))
        _ ≤ (R * ((2 * k + 2 : ℝ) ^ (δ / 2) / (δ / 2)) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
              exact mul_le_mul_of_nonneg_left hpz (by dsimp [R]; positivity)
    calc
      ‖etaPairTermDeriv k z‖ ≤ (‖z‖ * Real.log (2 * k + 2 : ℝ) + 1) * ((2 * k + 1 : ℕ) : ℝ) ^ (-z.re - 1) := hn
      _ ≤ u k := by
        dsimp [u]
        exact h2
  have hy0_sum : Summable (fun k : ℕ => etaPairTerm k y) := summable_etaPairTerm hy
  have hd : ∀ z ∈ t, HasDerivAt (fun w : ℂ => ∑' k : ℕ, etaPairTerm k w) (∑' k : ℕ, etaPairTermDeriv k z) z := by
    intro z hz
    exact hasDerivAt_tsum_of_isPreconnected hsu ht_open ht_pre hder hbound hyt hy0_sum hz
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Metric.ball_mem_nhds y hδ] with z hz
  exact (hd z hz).differentiableAt

/-! ### 延拓：η(s) = (1-2^(1-s))·ζ(s) 在 Re s > 0 -/

/-- 延拓定义域：四片凸集链式并（连通、避开 1、落在 Re > 0，含 (0,1) 实段与 2）。 -/
noncomputable def etaDomain : Set ℂ :=
  {s | 0 < re s ∧ re s < 1} ∪ {s | 0 < re s ∧ 0 < im s} ∪
    {s | 1 < re s} ∪ {s | 0 < re s ∧ im s < 0}

lemma isPreconnected_etaDomain : IsPreconnected etaDomain := by
  let A : Set ℂ := {s | 0 < re s ∧ re s < 1}
  let C : Set ℂ := {s | 0 < re s ∧ 0 < im s}
  let B : Set ℂ := {s | 1 < re s}
  let D : Set ℂ := {s | 0 < re s ∧ im s < 0}
  have hA : IsPreconnected A :=
    (Convex.inter (convex_halfSpace_re_gt 0) (convex_halfSpace_re_lt 1)).isPreconnected
  have hB : IsPreconnected B := (convex_halfSpace_re_gt 1).isPreconnected
  have hC : IsPreconnected C :=
    (Convex.inter (convex_halfSpace_re_gt 0) (convex_halfSpace_im_gt 0)).isPreconnected
  have hD : IsPreconnected D :=
    (Convex.inter (convex_halfSpace_re_gt 0) (convex_halfSpace_im_lt 0)).isPreconnected
  have hAC : IsPreconnected (A ∪ C) := by
    refine IsPreconnected.union' ?_ hA hC
    refine ⟨(1 / 2 : ℂ) + Complex.I, ?_, ?_⟩
    · norm_num [A]
    · norm_num [C]
  have hACB : IsPreconnected (A ∪ C ∪ B) := by
    refine IsPreconnected.union' ?_ hAC hB
    refine ⟨(2 : ℂ) + Complex.I, ?_, ?_⟩
    · exact Or.inr (by norm_num [C])
    · norm_num [B]
  have hAll : IsPreconnected ((A ∪ C ∪ B) ∪ D) := by
    refine IsPreconnected.union' ?_ hACB hD
    refine ⟨(1 / 2 : ℂ) - Complex.I, ?_, ?_⟩
    · exact Or.inl (Or.inl (by norm_num [A]))
    · norm_num [D]
  simpa [etaDomain, A, B, C, D] using hAll

/-- (2:ℂ)^(1-s) 在 etaDomain 解析（= exp(log 2 · (1-s))，cpow_def_of_ne_zero）。 -/
lemma analyticOnNhd_two_pow_one_sub :
    AnalyticOnNhd ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) etaDomain := by
  have hz : ∀ s : ℂ, (2 : ℂ) ^ (1 - s) =
      Complex.exp ((Complex.log (2 : ℂ)) * (1 - s)) := by
    intro s
    exact Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (1 - s)
  have hid : AnalyticOnNhd ℂ (fun s : ℂ => 1 - s) etaDomain := by
    exact AnalyticOnNhd.sub (analyticOnNhd_const (v := (1 : ℂ)))
      (analyticOnNhd_id (𝕜 := ℂ) (E := ℂ) : AnalyticOnNhd ℂ (fun x : ℂ => x) etaDomain)
  have hlin : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.log (2 : ℂ)) * (1 - s)) etaDomain := by
    simpa using (AnalyticOnNhd.mul (analyticOnNhd_const (v := Complex.log (2 : ℂ))) hid)
  exact (analyticOnNhd_congr'
      (s := etaDomain)
      (f := fun s : ℂ => (2 : ℂ) ^ (1 - s))
      (g := fun s : ℂ => Complex.exp ((Complex.log (2 : ℂ)) * (1 - s)))
      (by filter_upwards with x; exact hz x)).2
    (AnalyticOnNhd.comp (analyticOnNhd_cexp (u := Set.univ)) hlin (by intro s hs; simp))

/-- η(s) = (1-2^(1-s))·ζ(s) 在 etaDomain 上成立（identity theorem 从 Re s > 1 延拓）。 -/
lemma etaPaired_eq_mul_riemannZeta_on_etaDomain :
    Set.EqOn etaPaired (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) etaDomain := by
  have hf : AnalyticOnNhd ℂ etaPaired etaDomain := analyticOnNhd_etaPaired.mono (by
    intro s hs
    unfold etaDomain at hs
    simp at hs
    match hs with
    | Or.inl h1 =>
      match h1 with
      | Or.inl h2 =>
        match h2 with
        | Or.inl h => exact h.1
        | Or.inr h => exact h.1
      | Or.inr h => exact (lt_trans zero_lt_one h)
    | Or.inr h2 => exact h2.1)
  have hg : AnalyticOnNhd ℂ (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) etaDomain := by
    have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) etaDomain :=
      analyticOnNhd_two_pow_one_sub
    have hone : AnalyticOnNhd ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) etaDomain :=
      AnalyticOnNhd.sub (analyticOnNhd_const (v := (1 : ℂ))) hpow
    have hζ : AnalyticOnNhd ℂ riemannZeta etaDomain :=
      analyticOn_riemannZeta.mono (by
        intro s hs
        unfold etaDomain at hs
        simp at hs
        match hs with
        | Or.inl h1 =>
          match h1 with
          | Or.inl h2 =>
            match h2 with
            | Or.inl h => intro hs1; rw [hs1] at h; norm_num at h
            | Or.inr h => intro hs1; rw [hs1] at h; norm_num at h
          | Or.inr h => intro hs1; rw [hs1] at h; norm_num at h
        | Or.inr h2 => intro hs1; rw [hs1] at h2; norm_num at h2)
    exact AnalyticOnNhd.mul hone hζ
  have hz2 : (2 : ℂ) ∈ etaDomain := by simp [etaDomain]
  have hfg : etaPaired =ᶠ[𝓝 (2 : ℂ)]
      (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    have hb : Metric.ball (2 : ℂ) (1 / 2) ∈ 𝓝 (2 : ℂ) := Metric.ball_mem_nhds 2 (by norm_num)
    filter_upwards [hb] with s hs
    have hs1 : 1 < re s := by
      have hrz : ‖re s - re 2‖ ≤ ‖s - 2‖ := by simpa using (Complex.abs_re_le_norm (s - 2))
      have hlt : |re s - 2| < 1 / 2 :=
        lt_of_le_of_lt hrz (by simpa [dist_eq_norm] using hs)
      linarith [abs_lt.mp hlt]
    calc
      etaPaired s = (∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) := etaPaired_eq_eta hs1
      _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := eta_eq_mul_riemannZeta hs1
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_etaDomain hz2 hfg

theorem riemannZeta_neg_on_Ioo (x : ℝ) (hx1 : 0 < x) (hx2 : x < 1) :
    (riemannZeta x).re < 0 := by
  have hxU : (x : ℂ) ∈ etaDomain := by
    simp [etaDomain]
    exact Or.inl ⟨hx1, by exact_mod_cast hx2⟩
  have hEqx := etaPaired_eq_mul_riemannZeta_on_etaDomain hxU
  -- η 的正实部：成对级数逐项非负、首项为正
  have hηpos : 0 < (etaPaired (x : ℂ)).re := by
    have hsum : Summable (fun k : ℕ => etaPairTerm k (x : ℂ)) :=
      summable_etaPairTerm (by simpa using hx1)
    have hre : (etaPaired (x : ℂ)).re = ∑' k : ℕ, (etaPairTerm k (x : ℂ)).re :=
      re_tsum hsum
    have hsum_re : Summable (fun k : ℕ => (etaPairTerm k (x : ℂ)).re) :=
      (Complex.hasSum_re hsum.hasSum).summable
    rw [hre]
    refine Summable.tsum_pos hsum_re ?_ 0 ?_
    · intro k
      have hk : (etaPairTerm k (x : ℂ)).re =
          ((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x) := by
        have h1 : (2 * (k : ℂ) + 1) ^ (-(x : ℂ)) =
            (Real.rpow ((2 * k + 1 : ℕ) : ℝ) (-x) : ℂ) := by
          have hcast : (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) := by norm_cast
          rw [hcast]
          have h01 : 0 ≤ ((2 * k + 1 : ℕ) : ℝ) := by positivity
          rw [← Complex.ofReal_neg]
          exact (Complex.ofReal_cpow h01 (-x)).symm
        have h2 : (2 * (k : ℂ) + 2) ^ (-(x : ℂ)) =
            (Real.rpow ((2 * k + 2 : ℕ) : ℝ) (-x) : ℂ) := by
          have hcast : (2 * (k : ℂ) + 2) = ((2 * k + 2 : ℕ) : ℂ) := by norm_cast
          rw [hcast]
          have h02 : 0 ≤ ((2 * k + 2 : ℕ) : ℝ) := by positivity
          rw [← Complex.ofReal_neg]
          exact (Complex.ofReal_cpow h02 (-x)).symm
        simp [etaPairTerm, h1, h2, Real.rpow_eq_pow]
      have hposk : ((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x) ≥ 0 := by
        have hx1' : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
        have hx2' : 0 < ((2 * k + 2 : ℕ) : ℝ) := by positivity
        have hlt : ((2 * k + 2 : ℕ) : ℝ) ^ (-x) < ((2 * k + 1 : ℕ) : ℝ) ^ (-x) := by
          rw [Real.rpow_neg (le_of_lt hx2') x, Real.rpow_neg (le_of_lt hx1') x]
          have hltk : ((2 * k + 1 : ℕ) : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)
          have hltx : ((2 * k + 1 : ℕ) : ℝ) ^ x < ((2 * k + 2 : ℕ) : ℝ) ^ x :=
            Real.rpow_lt_rpow (by positivity : 0 ≤ ((2 * k + 1 : ℕ) : ℝ)) hltk
              (by linarith : 0 < x)
          exact (inv_strictAntiOn (by simpa using (Real.rpow_pos_of_pos hx1' x))
            (by simpa using (Real.rpow_pos_of_pos hx2' x)) hltx)
        exact le_of_lt (sub_pos.mpr hlt)
      rw [hk]
      exact hposk
    · have hk0 : (etaPairTerm 0 (x : ℂ)).re =
          ((2 * 0 + 1 : ℕ) : ℝ) ^ (-x) - ((2 * 0 + 2 : ℕ) : ℝ) ^ (-x) := by
        have h1 : (1 : ℂ) ^ (-(x : ℂ)) =
            (Real.rpow (1 : ℝ) (-x) : ℂ) := by
          have h01 : 0 ≤ (1 : ℝ) := by norm_num
          rw [← Complex.ofReal_neg]
          exact (Complex.ofReal_cpow h01 (-x)).symm
        have h2 : (2 : ℂ) ^ (-(x : ℂ)) =
            (Real.rpow (2 : ℝ) (-x) : ℂ) := by
          have h02 : 0 ≤ (2 : ℝ) := by norm_num
          rw [← Complex.ofReal_neg]
          exact (Complex.ofReal_cpow h02 (-x)).symm
        simp [etaPairTerm, h1, h2, Real.rpow_eq_pow]
      have hpos0 : 0 < ((2 * 0 + 1 : ℕ) : ℝ) ^ (-x) - ((2 * 0 + 2 : ℕ) : ℝ) ^ (-x) := by
        have h2x : 1 < (2 : ℝ) ^ x := by
          simpa [Real.one_rpow] using
            (Real.rpow_lt_rpow (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) < 2)
              (by linarith : 0 < x))
        have h2neg : (2 : ℝ) ^ (-x) < 1 := by
          rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) x]
          exact inv_lt_one_of_one_lt₀ h2x
        simpa [Real.one_rpow, sub_pos] using h2neg
      rw [hk0]
      exact hpos0
  -- 分母 1 - 2^(1-x) < 0
  have hden : 1 - (2 : ℝ) ^ (1 - x) < 0 := by
    have h21 : 1 < (2 : ℝ) ^ (1 - x) := by
      have hx0 : 0 < 1 - x := by linarith
      simpa [Real.one_rpow] using
        (Real.rpow_lt_rpow (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx0)
    exact sub_neg.mpr h21
  -- re(ζ x) = re(η x) / (1 - 2^(1-x))
  have hEqx' : (etaPaired (x : ℂ)).re =
      ((1 - (2 : ℂ) ^ (1 - (x : ℂ))) * riemannZeta (x : ℂ)).re :=
    congrArg Complex.re hEqx
  have hpow_real : (2 : ℂ) ^ (1 - (x : ℂ)) = (((2 : ℝ) ^ (1 - x) : ℝ) : ℂ) := by
    calc
      (2 : ℂ) ^ (1 - (x : ℂ)) = (2 : ℂ) ^ ((1 - x : ℝ) : ℂ) := by
        congr 1
        simp [Complex.ofReal_sub]
      _ = (((2 : ℝ) ^ (1 - x) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (by norm_num : 0 ≤ (2 : ℝ)) (1 - x)).symm
  have hre_mul : ((1 - (2 : ℂ) ^ (1 - (x : ℂ))) * riemannZeta (x : ℂ)).re
      = (1 - (2 : ℝ) ^ (1 - x)) * (riemannZeta (x : ℂ)).re := by
    rw [hpow_real]
    simp
  have hEqx'' : (etaPaired (x : ℂ)).re =
      (1 - (2 : ℝ) ^ (1 - x)) * (riemannZeta (x : ℂ)).re := by
    rw [hEqx']
    exact hre_mul
  have hzre : (riemannZeta (x : ℂ)).re =
      (etaPaired (x : ℂ)).re / (1 - (2 : ℝ) ^ (1 - x)) := by
    have hdnz : 1 - (2 : ℝ) ^ (1 - x) ≠ 0 := ne_of_lt hden
    calc
      (riemannZeta (x : ℂ)).re
          = ((1 - (2 : ℝ) ^ (1 - x)) * (riemannZeta (x : ℂ)).re) / (1 - (2 : ℝ) ^ (1 - x)) := by
            field_simp [hdnz]
      _ = (etaPaired (x : ℂ)).re / (1 - (2 : ℝ) ^ (1 - x)) := by rw [← hEqx'']
  rw [hzre]
  exact div_neg_of_pos_of_neg hηpos hden

theorem nontrivialZero_im_ne_zero (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.im ≠ 0 := by
  intro hz hre1 hre2 him
  have h_re : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [h_re] at hz
  have h_neg : (riemannZeta (ρ.re : ℂ)).re < 0 := riemannZeta_neg_on_Ioo ρ.re hre1 hre2
  rw [hz] at h_neg <;> norm_num at h_neg

/-- In the critical strip, ζ has finite analytic order at every point (it is not locally
    constant zero).  Follows from the identity theorem: ζ(0) = -1/2 ≠ 0 and ℂ \ {1} is
    connected. -/
theorem analyticOrder_riemannZeta_ne_top {s : ℂ} (hre1 : 0 < s.re) (hre2 : s.re < 1) :
    _root_.analyticOrderAt _root_.riemannZeta s ≠ ⊤ := by
  have h_analytic : AnalyticOnNhd ℂ _root_.riemannZeta ({1}ᶜ : Set ℂ) :=
    _root_.analyticOn_riemannZeta
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hx0 : (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hs : s ∈ ({1}ᶜ : Set ℂ) := by
    simp
    intro h
    rw [h] at hre2
    norm_num at hre2
  have horder0 : _root_.analyticOrderAt _root_.riemannZeta (0 : ℂ) ≠ ⊤ := by
    have h0a : AnalyticAt ℂ _root_.riemannZeta (0 : ℂ) :=
      _root_.analyticOn_riemannZeta 0 (by norm_num)
    have h0ne : _root_.riemannZeta (0 : ℂ) ≠ 0 := by
      rw [_root_.riemannZeta_zero]
      norm_num
    have h0 : _root_.analyticOrderAt _root_.riemannZeta (0 : ℂ) = 0 :=
      h0a.analyticOrderAt_eq_zero.mpr h0ne
    simp [h0]
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    h_analytic hU hx0 hs horder0

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
  have h_order_ne_top : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ ⊤ :=
    analyticOrder_riemannZeta_ne_top hre1 hre2
  have h_goal : zeroMultiplicity ρ ≠ 0 := by
    have h_eq : (zeroMultiplicity ρ : ℕ∞) = _root_.analyticOrderAt _root_.riemannZeta ρ := by
      simpa [zeroMultiplicity, _root_.analyticOrderNatAt] using Nat.cast_analyticOrderNatAt h_order_ne_top
    intro h
    apply h_order_ne_zero
    rw [← h_eq, h] <;> norm_num
  exact Nat.pos_of_ne_zero h_goal

theorem zeroMultiplicity_symmetry (ρ : ℂ)
    (_ : _root_.riemannZeta ρ = 0) (hre1 : 0 < ρ.re) (hre2 : ρ.re < 1) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by
  -- ζ(1-s) = 2(2π)^(-s) Γ(s) cos(πs/2) ζ(s) on a neighborhood of ρ
  have hs_all : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    have : (ρ.re : ℝ) = -(n : ℝ) := by rw [h]; simp
    linarith
  have hs1 : ρ ≠ 1 := by
    intro h
    rw [h] at hre2
    norm_num at hre2
  let c : ℂ → ℂ := fun s => 2 * (2 * (π : ℂ)) ^ (-s) * Gamma s * cos (π * s / 2)
  -- c ρ ≠ 0: 2 ≠ 0, (2π)^(-ρ) ≠ 0, Γ(ρ) ≠ 0, cos(πρ/2) ≠ 0
  have hcos_ne : cos (π * ρ / 2) ≠ 0 := by
    rw [ne_eq, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hρ : ρ = 2 * (k : ℂ) + 1 := by
      have hk' := congr_arg (fun x : ℂ => x * (2 / π)) hk
      field_simp [Real.pi_ne_zero] at hk'
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk'
    have hre_eq : ρ.re = (2 * (k : ℝ) + 1) := by
      have h := congrArg Complex.re hρ
      simpa using h
    have hk_range : (2 * (k : ℝ) + 1 ≤ 0) ∨ (1 ≤ 2 * (k : ℝ) + 1) := by
      rcases le_or_gt (0 : ℤ) k with hk0 | hk0
      · right
        have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
        linarith
      · left
        have hk_neg : k ≤ -1 := by omega
        have : (k : ℝ) ≤ -1 := by exact_mod_cast hk_neg
        linarith
    rcases hk_range with h | h
    · linarith [hre1, hre_eq, h]
    · linarith [hre2, hre_eq, h]
  have hc_ne : c ρ ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact (by
            rw [cpow_ne_zero_iff]
            exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))
      · exact Complex.Gamma_ne_zero_of_re_pos hre1
    · exact hcos_ne
  -- functional equation holds on a neighborhood of ρ (kept inside the strip)
  have hδ : 0 < min (ρ.re / 2) ((1 - ρ.re) / 2) := by
    exact lt_min (by positivity) (by linarith)
  have hFE_ev : (fun s : ℂ => riemannZeta (1 - s)) =ᶠ[𝓝 ρ]
      (fun s : ℂ => c s * riemannZeta s) := by
    rw [Filter.EventuallyEq, Metric.eventually_nhds_iff]
    refine ⟨min (ρ.re / 2) ((1 - ρ.re) / 2), hδ, ?_⟩
    intro s hs
    have hdist : dist s ρ < min (ρ.re / 2) ((1 - ρ.re) / 2) := hs
    have hre_lt : |s.re - ρ.re| < min (ρ.re / 2) ((1 - ρ.re) / 2) := by
      have hre_abs : |(s - ρ).re| ≤ dist s ρ := by
        simpa [dist_eq_norm] using abs_re_le_norm (s - ρ)
      have hre_abs' : |s.re - ρ.re| ≤ dist s ρ := by simpa using hre_abs
      exact lt_of_le_of_lt hre_abs' hdist
    have hs_pos : 0 < s.re := by
      have h1 : |s.re - ρ.re| < ρ.re / 2 := lt_of_lt_of_le hre_lt (min_le_left _ _)
      have hlo : -(ρ.re / 2) < s.re - ρ.re := (abs_lt.mp h1).1
      linarith
    have hs_lt : s.re < 1 := by
      have h2 : |s.re - ρ.re| < (1 - ρ.re) / 2 := lt_of_lt_of_le hre_lt (min_le_right _ _)
      have hhi : s.re - ρ.re < (1 - ρ.re) / 2 := (abs_lt.mp h2).2
      linarith
    have hs_ne_neg : ∀ n : ℕ, s ≠ -n := by
      intro n h
      have : s.re = -(n : ℝ) := by rw [h]; simp
      linarith [hs_pos]
    have hs_ne_one : s ≠ 1 := by
      intro h
      rw [h] at hs_lt
      norm_num at hs_lt
    have hFE : riemannZeta (1 - s) =
        2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s :=
      riemannZeta_one_sub hs_ne_neg hs_ne_one
    dsimp [c]
    exact hFE
  -- c is analytic at ρ, and c ρ ≠ 0 ⟹ order c ρ = 0
  have hc_analytic : AnalyticAt ℂ c ρ := by
    have hcpow_a : AnalyticAt ℂ (fun s : ℂ => (2 * (π : ℂ)) ^ (-s)) ρ := by
      apply AnalyticAt.cpow (f := fun _ : ℂ => (2 * (π : ℂ) : ℂ)) (g := fun s : ℂ => -s)
      · fun_prop
      · fun_prop
      · have h2pi : (0 : ℝ) < 2 * π := by positivity
        simpa [map_mul] using (ofReal_mem_slitPlane.mpr h2pi)
    have hgamma_a : AnalyticAt ℂ (fun s : ℂ => Gamma s) ρ := by
      have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
      have hd : DifferentiableOn ℂ (fun s : ℂ => Gamma s) {s : ℂ | 0 < s.re} := by
        intro s hs
        refine (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
        intro m hm
        have hs' : 0 < (-(↑m : ℂ)).re := by simpa [hm] using hs
        have hm_nonneg : (0 : ℝ) ≤ ↑m := by exact_mod_cast (Nat.zero_le m)
        exact not_lt_of_ge (neg_nonpos.mpr hm_nonneg) (by simpa using hs')
      exact (hd.analyticOnNhd hU) ρ hre1
    have hcos_a : AnalyticAt ℂ (fun s : ℂ => cos (π * s / 2)) ρ := by fun_prop
    have htwo_a : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) ρ := by fun_prop
    have h12 : AnalyticAt ℂ (fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s)) ρ := htwo_a.mul hcpow_a
    have h123 : AnalyticAt ℂ (fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) * Gamma s) ρ := h12.mul hgamma_a
    exact h123.mul hcos_a
  have hc_order : analyticOrderAt c ρ = 0 := by
    apply analyticOrderAt_eq_zero.mpr
    exact Or.inr hc_ne
  have hc_ne_top : analyticOrderAt c ρ ≠ ⊤ := by
    rw [hc_order]
    simp
  have hc_nat : analyticOrderNatAt c ρ = 0 := by
    have h_cast : (analyticOrderNatAt c ρ : ℕ∞) = 0 := by
      rw [Nat.cast_analyticOrderNatAt hc_ne_top, hc_order]
    exact_mod_cast h_cast
  -- orderNat (ζ ∘ (1-·)) ρ = orderNat ζ (1-ρ) (change of variables, deriv ≠ 0)
  have hcomp : analyticOrderAt (fun s : ℂ => riemannZeta (1 - s)) ρ =
      analyticOrderAt riemannZeta (1 - ρ) := by
    have hg_an : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
    have hg_der : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by simp
    exact analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) (g := fun s : ℂ => 1 - s) hg_an hg_der
  have hre1' : 0 < (1 - ρ).re := by simp [Complex.sub_re]; linarith
  have hre2' : (1 - ρ).re < 1 := by simp [Complex.sub_re]; linarith
  have h1ρ_ne_top : analyticOrderAt riemannZeta (1 - ρ) ≠ ⊤ :=
    analyticOrder_riemannZeta_ne_top hre1' hre2'
  have hF_ne_top : analyticOrderAt (fun s : ℂ => riemannZeta (1 - s)) ρ ≠ ⊤ := by
    rw [hcomp]
    exact h1ρ_ne_top
  have hF_nat : analyticOrderNatAt (fun s : ℂ => riemannZeta (1 - s)) ρ =
      analyticOrderNatAt riemannZeta (1 - ρ) := by
    have h_cast : (analyticOrderNatAt (fun s : ℂ => riemannZeta (1 - s)) ρ : ℕ∞) =
        analyticOrderNatAt riemannZeta (1 - ρ) := by
      rw [Nat.cast_analyticOrderNatAt hF_ne_top, hcomp, ← Nat.cast_analyticOrderNatAt h1ρ_ne_top]
    exact_mod_cast h_cast
  -- orderNat (c · ζ) ρ = orderNat ζ ρ (c ρ ≠ 0 ⟹ order c = 0)
  have hζ_an : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hs1
  have hζ_ne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrder_riemannZeta_ne_top hre1 hre2
  have h_mul : analyticOrderNatAt (fun s : ℂ => c s * riemannZeta s) ρ =
      analyticOrderNatAt riemannZeta ρ := by
    have hsum : analyticOrderNatAt (fun s : ℂ => c s * riemannZeta s) ρ =
        analyticOrderNatAt c ρ + analyticOrderNatAt riemannZeta ρ :=
      analyticOrderNatAt_mul (f := c) (g := riemannZeta) hc_analytic hζ_an hc_ne_top hζ_ne_top
    simpa [hc_nat] using hsum
  -- orderNat (ζ ∘ (1-·)) ρ = orderNat (c · ζ) ρ (eventually equal)
  have hcζ_order : analyticOrderAt (fun s : ℂ => c s * riemannZeta s) ρ =
      analyticOrderAt riemannZeta ρ := by
    have hmul : analyticOrderAt (c * riemannZeta) ρ =
        analyticOrderAt c ρ + analyticOrderAt riemannZeta ρ :=
      analyticOrderAt_mul (f := c) (g := riemannZeta) hc_analytic hζ_an
    change analyticOrderAt (c * riemannZeta) ρ = analyticOrderAt riemannZeta ρ
    rw [hmul, hc_order, zero_add]
  have hR_ne_top : analyticOrderAt (fun s : ℂ => c s * riemannZeta s) ρ ≠ ⊤ := by
    rw [hcζ_order]
    exact hζ_ne_top
  have h_congr : analyticOrderNatAt (fun s : ℂ => riemannZeta (1 - s)) ρ =
      analyticOrderNatAt (fun s : ℂ => c s * riemannZeta s) ρ := by
    have ho : analyticOrderAt (fun s : ℂ => riemannZeta (1 - s)) ρ =
        analyticOrderAt (fun s : ℂ => c s * riemannZeta s) ρ :=
      analyticOrderAt_congr hFE_ev
    have h_cast : (analyticOrderNatAt (fun s : ℂ => riemannZeta (1 - s)) ρ : ℕ∞) =
        analyticOrderNatAt (fun s : ℂ => c s * riemannZeta s) ρ := by
      rw [Nat.cast_analyticOrderNatAt hF_ne_top, ho, ← Nat.cast_analyticOrderNatAt hR_ne_top]
    exact_mod_cast h_cast
  calc
    zeroMultiplicity ρ = analyticOrderNatAt riemannZeta ρ := by simp [zeroMultiplicity]
    _ = analyticOrderNatAt (fun s : ℂ => c s * riemannZeta s) ρ := h_mul.symm
    _ = analyticOrderNatAt (fun s : ℂ => riemannZeta (1 - s)) ρ := h_congr.symm
    _ = analyticOrderNatAt riemannZeta (1 - ρ) := hF_nat
    _ = zeroMultiplicity (1 - ρ) := by simp [zeroMultiplicity]

/-- 围道内非平凡零点集有限（定理，紧集 ∩ 零点有限）：
    集合 {ρ | ζ(ρ)=0 ∧ 0<Re ρ<1 ∧ ‖ρ−1/2‖<1} 有限。
    半径 1 与 ContourIntegral.contourRadius = 1 一致（字面值，避免循环依赖）。
    证明：包含在紧集 closedBall(1/2,1) ∩ riemannZetaZeros 内（后者有限）。 -/
lemma contourZeroFinset_finite : Set.Finite
    {ρ : ℂ | _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ - (1 / 2 : ℂ)‖ < 1} := by
  let B : Set ℂ := Metric.closedBall (1 / 2 : ℂ) 1
  have h_comp : IsCompact B := isCompact_closedBall _ _
  have h_fin : (B ∩ riemannZetaZeros).Finite := h_comp.inter_riemannZetaZeros_finite
  have hsub : {ρ : ℂ | _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ - (1 / 2 : ℂ)‖ < 1}
      ⊆ B ∩ riemannZetaZeros := by
    intro ρ hρ
    have h_norm : ρ ∈ B := by
      change dist ρ (1 / 2 : ℂ) ≤ 1
      have hlt : dist ρ (1 / 2 : ℂ) < 1 := by
        simpa [dist_eq_norm] using hρ.2.2.2
      exact le_of_lt hlt
    exact ⟨h_norm, hρ.1⟩
  exact h_fin.subset hsub

/-- 围道内非平凡零点集（def，Finset）：|s−1/2| < 1 内的非平凡零点。 -/
noncomputable def contourZeroFinset : Finset ℂ :=
  contourZeroFinset_finite.toFinset

/-- 围道内零点的成员性质（定理）：
    ρ ∈ contourZeroFinset ⟺ ζ(ρ)=0 ∧ 0<Re ρ<1 ∧ ‖ρ−1/2‖<1。 -/
theorem contourZeroFinset_mem (ρ : ℂ) :
    ρ ∈ contourZeroFinset ↔
      _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ - (1 / 2 : ℂ)‖ < 1 := by
  unfold contourZeroFinset
  simp [contourZeroFinset_finite.coe_toFinset]

/-- 围道外非平凡零点的判定谓词（2026-10-01）：|s−1/2| ≥ 1 的非平凡零点。
    供 farZeroSubtype 成员与 stage_4 反证链（mollified/off_critical 的 ρ 项分离）使用。 -/
abbrev IsFarZero (ρ : ℂ) : Prop :=
  _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ - (1 / 2 : ℂ)‖ ≥ 1

/-- 围道外非平凡零点子类型（2026-10-01）：|s−1/2| ≥ 1 的非平凡零点。
    farZeroContribution 与 stage_4 反证链（mollified_pair_tail_sum_negligible、
    off_critical_zero_tail_dominated）共用；tsum 对任意类型有定义，不依赖
    nontrivialZeroEnum 的 ℕ 枚举（从主链摘除 :56 sorry 的 S 无限需求）。 -/
abbrev farZeroSubtype : Type :=
  {ρ : ℂ // IsFarZero ρ}

/-- 围道外非平凡零点贡献（def）：|s−1/2| ≥ 1 的零点（含围道上）的 Mellin 加权项。
    半径 1 与 ContourIntegral.contourRadius = 1 一致。
    围道上零点的处理：归入围道外（≥ 1）；围道避开零点的形变是模型层标准处理。
    2026-10-01 改：直接对"围道外非平凡零点子类型"求和（子类型 tsum），不再依赖
    nontrivialZeroEnum 的 ℕ 枚举——从主链摘除 nontrivialZeroEnum_exists（:49 sorry 的
    "S 无限/单射枚举"需求）。tsum 对任意类型有定义，可数性与可和性只决定收敛，不影响定义。 -/
noncomputable def farZeroContribution (f : TestFunction) : ℂ :=
  ∑' ρ : farZeroSubtype, (zeroMultiplicity ρ.1 : ℂ) * melinTransform f ρ.1

/-- 非平凡零点求和（def，显式拆分围道内/外）：
    nontrivialZeroSum(f) = Σ_{ρ ∈ contourZeroFinset} m(ρ)·M[f](ρ) + farZeroContribution f。
    围道内（有限 Finset）+ 围道外（tsum，M[f] 超衰减保证收敛——模型层）。
    旧定义 ∑' n 全枚举 tsum 是"全零点"表达，数学上等价但隐藏了围道结构；
    重构后与围道积分（ContourIntegral :109 围道内版本）的对应显式化。 -/
noncomputable def nontrivialZeroSum (f : TestFunction) : ℂ :=
    (∑ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ) +
    farZeroContribution f

/-- 平凡零点贡献（围道外约定，机制 A 紧商）：
    trivialZeroContribution(f) = -M[f](1)。
    围道只包围临界带内非平凡零点，平凡零点（负偶数）与 s=1 极点都在围道外，
    故平凡零点项不出现；围道外 s=1 极点（ζ 一阶极点）的净贡献折入负号。
    旧定义 Σ_k M[f](-2(k+1)) + M[f](1) 把围道外奇点算成围道内项，废弃。
    s=1 极点项与谱侧恒等项的配对见 stage_4.lean identity_orbit_normalization。 -/
noncomputable def trivialZeroContribution (f : TestFunction) : ℂ :=
    - melinTransform f (1 : ℂ)

noncomputable def zetaZeroSide (f : TestFunction) : ℂ :=
    nontrivialZeroSum f + trivialZeroContribution f

theorem nontrivialZeroSum_localization (f : TestFunction) :
    (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      melinTransform f ρ = 0) →
    nontrivialZeroSum f = 0 := by
  intro h
  unfold nontrivialZeroSum
  -- 围道内 Finset 项全 0
  have h_fin : ∀ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ = 0 := by
    intro ρ hρ
    have hz : _root_.riemannZeta ρ = 0 := (contourZeroFinset_mem ρ).mp hρ |>.1
    have hre1 : 0 < ρ.re := (contourZeroFinset_mem ρ).mp hρ |>.2.1
    have hre2 : ρ.re < 1 := (contourZeroFinset_mem ρ).mp hρ |>.2.2.1
    rw [h ρ hz hre1 hre2] <;> ring
  have h_sum_fin : (∑ ρ ∈ contourZeroFinset, (zeroMultiplicity ρ : ℂ) * melinTransform f ρ) = 0 := by
    exact Finset.sum_eq_zero h_fin
  -- 围道外子类型 tsum 项全 0
  have h_tsum : farZeroContribution f = 0 := by
    unfold farZeroContribution
    have h_zero : ∀ ρ : farZeroSubtype,
        (zeroMultiplicity ρ.1 : ℂ) * melinTransform f ρ.1 = 0 := by
      intro ρ
      have hz : _root_.riemannZeta ρ.1 = 0 := ρ.2.1
      have hre1 : 0 < ρ.1.re := ρ.2.2.1
      have hre2 : ρ.1.re < 1 := ρ.2.2.2.1
      rw [h ρ.1 hz hre1 hre2] <;> ring
    have h_sum : (fun ρ : farZeroSubtype =>
        (zeroMultiplicity ρ.1 : ℂ) * melinTransform f ρ.1) = fun _ => 0 := by
      funext ρ; exact h_zero ρ
    rw [h_sum, tsum_zero]
  rw [h_sum_fin, h_tsum] <;> ring

end OrderPreservingBijection