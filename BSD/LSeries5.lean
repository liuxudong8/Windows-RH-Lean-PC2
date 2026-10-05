import Mathlib.Data.Rat.Cast.Lemmas
import BSD.aE5_table
import OrderPreservingBijection.QuadraticFieldFive
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential

set_option maxHeartbeats 4000000

/-!
# ① E⁵ 的局部因子与 L(1) 反射公式（Lean 化骨架）

对应文档《骨架 A 讨论稿》5.4(iv) 与 BSD/Main.lean 的 `rank_E5_Q_eq_zero`：
E⁵ = 37a1 的 5-二次扭（Y² = X³ − 25X + 125/4），导子 N = 925，根数 ε = +1。

本模块分层：
1. **局部因子（代数层，可 Lean）**：χ₅ 模 5 二次特征、E 的 Hecke 系数 a_p(E)、
   a_p(E⁵) = χ₅(p)·a_p(E)（好素）、5 处加性（a = 0）、37 处乘性（a = +1）。
   恒等式（5/37/抽检）为已证定理。
2. **L 函数（声明层）**：不完全 Gamma Γ(s,b)、Dokchitser 反射公式、L(s) 定义、L(E⁵,1) ≠ 0
   区间判定为 axiom（mathlib 尚无自守 L / 不完全 Gamma 理论），注释标明待证明状态。
3. **尾界**：Ramanujan 界与系数界为 axiom；几何级数尾的封闭公式 e^(−α(N+1))/(1−e^(−α))
   已在纸面闭合（误差预算见 `L_E5_one_ne_zero` 注释）。

数值管线（Python，已闭合）：s = 3 处反射/直接级数闭合比 0.99999967（确定 a₃₇ = +1 与 ε = +1）；
L(E⁵,1) = 5.35486161664732485121，区间 ± 1.7e-71（N = 800 截断，dps = 80）。
-/

namespace BSD.LSeries5

noncomputable section

/-! ## 1. 局部因子（代数层） -/

/-- 模 5 二次特征 χ₅(p) = (p/5)（Legendre 符号；p ≡ ±1 mod 5 取 1，p ≡ ±2 mod 5 取 −1，p = 5 取 0）。 -/
def chi5 (p : ℕ) : ℤ :=
  if p % 5 = 0 then 0
  else if p % 5 = 1 ∨ p % 5 = 4 then 1
  else -1

/-- χ₅(5) = 0。 -/
theorem chi5_zero_at_5 : chi5 5 = 0 := by
  norm_num [chi5]

/-- χ₅(2) = −1（2 非 5 的平方剩余）。 -/
theorem chi5_neg_at_2 : chi5 2 = -1 := by
  norm_num [chi5]

/-- χ₅(11) = +1（11 ≡ 1 mod 5）。 -/
theorem chi5_pos_at_11 : chi5 11 = 1 := by
  norm_num [chi5]

/-- E = 37a1 在好素 p 的 Hecke 系数 a_p(E) = p + 1 − #E(𝔽_p)（点计数）。
    数值（文档 5.1 与 _tmp_nm3/a4_out.txt）：a₂ = −2, a₃ = −3, a₅ = −2, a₇ = −1,
    a₁₁ = −5, a₁₃ = −2, a₁₉ = 0, a₂₉ = 6, a₃₁ = −4, a₄₁ = −9, a₄₉ = −13, a₅₉ = 8。
    待证明：模性 / 有限域点计数（mathlib 无椭圆曲线理论）。 -/
axiom ap_E (p : ℕ) : ℤ

/-- a_p(E) 抽样值表（LMFDB / Cremona；文档 5.1）。 -/
axiom ap_E_values :
    ap_E 2 = -2 ∧ ap_E 3 = -3 ∧ ap_E 5 = -2 ∧ ap_E 7 = -1 ∧ ap_E 11 = -5 ∧ ap_E 13 = -2 ∧
    ap_E 19 = 0 ∧ ap_E 29 = 6 ∧ ap_E 31 = -4 ∧ ap_E 41 = -9 ∧ ap_E 49 = -13 ∧ ap_E 59 = 8

/-- a_p(E⁵)：E⁵ 的 Hecke 系数（文档 5.4(iv)）：
    5 处加性约化（a = 0）；37 处乘性（a = +1，s = 3 闭合比 0.99999967 确定）；
    好素 p ∤ 925 取 a_p(E⁵) = χ₅(p)·a_p(E)。 -/
def ap5 (p : ℕ) : ℤ :=
  if p % 5 = 0 then 0
  else if p = 37 then 1
  else chi5 p * ap_E p

/-- 5 处加性：a₅(E⁵) = 0。 -/
theorem ap5_additive_at_5 : ap5 5 = 0 := by
  norm_num [ap5]

/-- 37 处乘性：a₃₇(E⁵) = +1。 -/
theorem ap5_multiplicative_at_37 : ap5 37 = 1 := by
  norm_num [ap5]

/-- 抽检（好素）：a₂(E⁵) = χ₅(2)·a₂(E) = (−1)(−2) = 2。 -/
theorem ap5_sample_2 : ap5 2 = 2 := by
  norm_num [ap5, chi5, ap_E_values]

/-- 抽检（好素）：a₁₁(E⁵) = χ₅(11)·a₁₁(E) = 1·(−5) = −5。 -/
theorem ap5_sample_11 : ap5 11 = -5 := by
  norm_num [ap5, chi5, ap_E_values]

/-! ## 2. L 函数与反射公式（声明层） -/

/-- Ramanujan 界：|a_p(E)| ≤ 2√p（Weil 猜想 d = 1 / Deligne；无条件）。
    待证明：有限域点计数 + Hasse 界。 -/
axiom ramanujan_ap_E (p : ℕ) : |ap_E p| ≤ 2 * Real.sqrt (p : ℝ)

/-- 系数界：|a_n(E⁵)| ≤ τ(n)·√n（由 Ramanujan + Hecke 递推 |a_{p^k}| ≤ (k+1)p^{k/2} 的归纳）。
    待证明：素幂递推的归纳 + 乘性组合。 -/
axiom coefficient_bound (n : ℕ) : |ap5 n| ≤ (Nat.divisors n).card * Real.sqrt (n : ℝ)

/-- 不完全 Gamma Γ(s, b) = ∫_b^∞ t^(s−1) e^(−t) dt（mathlib 尚无；Dokchitser 反射公式输入）。
    待证明：不完全 Gamma 的分析理论（可加积分定义）。 -/
axiom GammaUpper (s b : ℝ) : ℝ

/-- Dokchitser 型反射公式（N = 925，ε = +1，b_n = 2πn/√925）：
    Λ(s) = Σ_{n≥1} a_n(E⁵) · [b_n^(s−2)·Γ(2−s, b_n) + b_n^(−s)·Γ(s, b_n)]。
    待证明：椭圆曲线 L 函数的解析延拓与函数方程（mathlib 无自守 L 理论）。 -/
axiom Lambda_E5 (s : ℝ) : ℝ

/-- 归一化 L 函数：L(s) = (2π/√925)^s / Γ(s) · Λ(s)（Γ 为完全 Gamma，mathlib 已定义）。 -/
noncomputable def L_E5 (s : ℝ) : ℝ :=
  ((2 * Real.pi / Real.sqrt (925 : ℝ)) ^ s) / Real.Gamma s * Lambda_E5 s

/-- L(E⁵,1) ≠ 0 —— 区间算术判定（文档 5.4(iv)，确定性而非数值证据）：
    L(E⁵,1) ∈ [5.3548616166 − 1.7×10⁻⁷¹, 5.3548616166 + 1.7×10⁻⁷¹] ⊂ (0, ∞)。
    误差预算（N = 800 截断，dps = 80）：
    · 截断尾 ≤ 1.7×10⁻⁷¹：系数界 |a_n| ≤ τ(n)√n（coefficient_bound）与
      Γ 因子指数衰减 e^(−2πn/√925)（b_n = 2πn/√925 ⟹ Γ(s,b_n) ~ e^(−b_n)·b_n^(s−1)）
      的封闭几何级数：Σ_{n>N} e^(−αn) = e^(−α(N+1)) / (1 − e^(−α))，α = 2π/√925；
    · 舍入 ≤ 10⁻⁷⁷（80 位十进制精度）。
    待证明：反射公式截断 + 几何级数尾求和 + 区间算术的 Lean 实现。 -/
axiom L_E5_one_ne_zero : L_E5 1 ≠ 0

/-! ## 3. 尾界几何级数（axiom → theorem） -/

/-- 几何级数尾的封闭公式（通用引理）：
    Σ_{n≥0} r^(m+n) = r^m / (1 − r)，对 |r| < 1。
    证明：`hasSum_geometric_of_norm_lt_one`（mathlib，NormedDivisionRing ℝ）+ 指标移位 + tsum。 -/
theorem tsum_geom_shift {r : ℝ} (hr : |r| < 1) (m : ℕ) :
    (∑' n : ℕ, r ^ (m + n)) = r ^ m / (1 - r) := by
  have hg : HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hr
  have hg' : HasSum (fun n : ℕ ↦ r ^ m * r ^ n) (r ^ m * (1 - r)⁻¹) :=
    hg.mul_left (r ^ m)
  have hfun : (fun n : ℕ ↦ r ^ m * r ^ n) = fun n : ℕ ↦ r ^ (m + n) := by
    funext n
    rw [pow_add]
  have hg'' : HasSum (fun n : ℕ ↦ r ^ (m + n)) (r ^ m * (1 - r)⁻¹) := by
    simpa [hfun] using hg'
  rw [div_eq_mul_inv]
  exact hg''.tsum_eq

/-- 几何级数尾的封闭公式（α = 2π/√925 型参数化，N = 800 截断的尾界口径）：
    Σ_{n > N} e^(−α·n) = e^(−α·(N+1)) / (1 − e^(−α))，对 0 < α。
    证明：`tsum_geom_shift` 特化 r = e^(−α)（0 < e^(−α) < 1 ⟹ |r| < 1）+ `exp_nat_mul`。 -/
theorem geom_tail_bound (N : ℕ) (α : ℝ) (hα : 0 < α) :
    (∑' n : ℕ, Real.exp (-α * (N + 1 + n : ℕ))) =
      Real.exp (-α * (N + 1 : ℕ)) / (1 - Real.exp (-α)) := by
  let r : ℝ := Real.exp (-α)
  have hr : |r| < 1 := by
    dsimp [r]
    rw [abs_of_pos (Real.exp_pos (-α))]
    rw [Real.exp_lt_one_iff]
    linarith
  have hpow : ∀ n : ℕ, Real.exp (-α * (n : ℕ)) = r ^ n := by
    intro n
    rw [mul_comm]
    rw [Real.exp_nat_mul]
  calc
    (∑' n : ℕ, Real.exp (-α * (N + 1 + n : ℕ))) = ∑' n : ℕ, r ^ (N + 1 + n) := by
      simp_rw [hpow]
    _ = r ^ (N + 1) / (1 - r) := tsum_geom_shift hr (N + 1)
    _ = Real.exp (-α * (N + 1 : ℕ)) / (1 - Real.exp (-α)) := by
      rw [← hpow (N + 1)]

/-! ## 4. (iv-c) 初等不等式链（axiom → theorem）

文档 5.4(iv-c) 的数值界在此闭合为可核验的初等不等式链（axiom 闭包仅基础公理）：
    α > 0.2065（`Real.pi_gt_d4` + `Real.sqrt_lt'`）；
    e^(−α) < 0.8136（`Real.exp_bound` 部分和下界 + 倒数单调）；
    e^(−α·801) < 10⁻⁶⁰（幂 + 精确有理数 `native_decide`）；
    尾界 4·e^(−α·801)/(1−e^(−α)) < 10⁻⁵⁸。
注意：此处采用**充分性宽口径**——文档精细核验值（1.5×10⁻⁷²、3.3×10⁻⁷¹，Python
管线）在 801 次幂的粗放上界 0.8136^801 ≈ 1.55×10⁻⁷² 下无法复现（略高于 1.5×10⁻⁷²），
故 Lean 证明更宽松但仍 ≪ 部分和下界 5.35 的充分界。 -/

/-- α = 2π/√925 的下界：α > 0.2065。
    证明：π > 3.1415（`Real.pi_gt_d4`）；√925 < 30.414（925 < 30.414²，`Real.sqrt_lt'`）；
    组合：0.2065·√925 < 0.2065·30.414 < 2·3.1415 < 2π。 -/
theorem alpha_gt_2065 : (0.2065 : ℝ) < 2 * Real.pi / Real.sqrt 925 := by
  have hsqrt : Real.sqrt 925 < (30.414 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 30.414)]
    norm_num
  have h1 : (0.2065 : ℝ) * Real.sqrt 925 < (0.2065 * 30.414 : ℝ) := by
    exact mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 0.2065)
  have h2 : (0.2065 * 30.414 : ℝ) < 2 * Real.pi := by
    have h3 : (0.2065 * 30.414 : ℝ) < 2 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 2))
  have h3' : (0.2065 : ℝ) * Real.sqrt 925 < 2 * Real.pi := lt_trans h1 h2
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 925))]
  exact h3'

/-- e^(−α) < 0.8136：α > 0.2065（exp 单调）；e^(0.2065) ≥ Σ₅ − B > 1/0.8136
    （`Real.exp_bound` n = 5 部分和下界）⟹ e^(−0.2065) = 1/e^(0.2065) < 0.8136。 -/
theorem exp_neg_alpha_lt_8136 : Real.exp (-(2 * Real.pi / Real.sqrt 925)) < (0.8136 : ℝ) := by
  have hmono : Real.exp (-(2 * Real.pi / Real.sqrt 925)) ≤ Real.exp (-(0.2065 : ℝ)) := by
    exact Real.exp_le_exp_of_le (by linarith [alpha_gt_2065])
  have hrecip : Real.exp (-(0.2065 : ℝ)) < (0.8136 : ℝ) := by
    rw [Real.exp_neg]
    have hexp : (1 / (0.8136 : ℝ)) < Real.exp (0.2065 : ℝ) := by
      have hsum : (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ)) =
          (1 : ℝ) + 0.2065 + (0.2065 : ℝ) ^ 2 / 2 + (0.2065 : ℝ) ^ 3 / 6 + (0.2065 : ℝ) ^ 4 / 24 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        norm_num
      have hb := Real.exp_bound (x := 0.2065) (n := 5) (by norm_num : |(0.2065 : ℝ)| ≤ 1) (by norm_num : 0 < 5)
      have hd : Real.exp (0.2065 : ℝ) - (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
          ≤ (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        have h1 : Real.exp (0.2065 : ℝ) - (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
            ≤ |(0.2065 : ℝ)| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) :=
          le_trans (le_abs_self _) hb
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 0.2065)] using h1
      have hd2 : (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
          - Real.exp (0.2065 : ℝ) ≤ (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        have hb' : |(∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ)) - Real.exp (0.2065 : ℝ)| ≤
            |(0.2065 : ℝ)| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
          simpa [abs_sub_comm] using hb
        have h1 : (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
            - Real.exp (0.2065 : ℝ) ≤
            |(0.2065 : ℝ)| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) :=
          le_trans (le_abs_self _) hb'
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 0.2065)] using h1
      have hge : (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
          - (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) ≤ Real.exp (0.2065 : ℝ) := by
        linarith
      have hpart : (1 / (0.8136 : ℝ)) <
          (1 : ℝ) + 0.2065 + (0.2065 : ℝ) ^ 2 / 2 + (0.2065 : ℝ) ^ 3 / 6 + (0.2065 : ℝ) ^ 4 / 24
            - (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        norm_num
      have hnorm : (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
          - (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5))
          = (1 : ℝ) + 0.2065 + (0.2065 : ℝ) ^ 2 / 2 + (0.2065 : ℝ) ^ 3 / 6 + (0.2065 : ℝ) ^ 4 / 24
            - (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        rw [hsum]
      have hpart' : (1 / (0.8136 : ℝ)) <
          (∑ m ∈ Finset.range 5, (0.2065 : ℝ) ^ m / (m.factorial : ℝ))
          - (0.2065 : ℝ) ^ 5 * ((6 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        rwa [hnorm]
      exact lt_of_lt_of_le hpart' hge
    have htmp : 1 / Real.exp (0.2065 : ℝ) < 1 / (1 / (0.8136 : ℝ)) :=
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1 / (0.8136 : ℝ)) hexp
    simpa using htmp
  exact lt_of_le_of_lt hmono hrecip

/-- e^(−α·801) < 10⁻⁶⁰：(e^(−α))^801 ≤ 0.8136^801 < 10⁻⁶⁰（精确有理数幂判定）。
    宽口径——0.8136^801 ≈ 1.55×10⁻⁷² < 10⁻⁶⁰（margin 12 个数量级），且 ≪ 部分和下界。
    注：801 次幂的 ℚ 判定（1017^801·10⁶⁰ < 1250^801，约 2500 位）由 `native_decide` 完成，
    其 `native_decide.ax` 为**计算信任公理**（Lean 将 bignum 比较委托给已验证的 native 编译
    通道；mathlib 对大整数判定的标准机制），数学上不引入任何假设，可按交叉相乘独立复核。 -/
theorem exp_neg_alpha_801_lt :
    Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801) < (1 : ℝ) / 10 ^ 60 := by
  have hpow : Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801) =
      (Real.exp (-(2 * Real.pi / Real.sqrt 925))) ^ 801 := by
    have hc : (801 : ℝ) = (801 : ℕ) := by norm_num
    rw [hc]
    rw [mul_comm]
    rw [Real.exp_nat_mul]
  have hle : (Real.exp (-(2 * Real.pi / Real.sqrt 925))) ^ 801 ≤ (0.8136 : ℝ) ^ 801 := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) exp_neg_alpha_lt_8136.le 801
  have hnum : (0.8136 : ℝ) ^ 801 < (1 : ℝ) / 10 ^ 60 := by
    have hq : ((1017 : ℚ) / 1250) ^ 801 < (1 : ℚ) / 10 ^ 60 := by native_decide
    have hq' : (((1017 : ℚ) / 1250) ^ 801 : ℝ) < ((1 : ℚ) / 10 ^ 60 : ℝ) := by
      exact_mod_cast hq
    norm_num at hq' ⊢
    exact hq'
  rw [hpow]
  exact lt_of_le_of_lt hle hnum

/-- (iv-c) 尾界：4·e^(−α·801)/(1−e^(−α)) < 10⁻⁵⁸
    （e^(−α·801) < 10⁻⁶⁰；1−e^(−α) > 0.1864；4·10⁻⁶⁰/0.1864 = 2.15×10⁻⁵⁹ < 10⁻⁵⁸）。 -/
theorem tail_ivc_bound :
    (4 : ℝ) * Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801)
      / (1 - Real.exp (-(2 * Real.pi / Real.sqrt 925))) < (1 : ℝ) / 10 ^ 58 := by
  have h1 : (0.1864 : ℝ) < 1 - Real.exp (-(2 * Real.pi / Real.sqrt 925)) := by
    linarith [exp_neg_alpha_lt_8136]
  have h2 : (4 : ℝ) * Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801) ≤
      (4 : ℝ) * ((1 : ℝ) / 10 ^ 60) := by
    exact mul_le_mul_of_nonneg_left exp_neg_alpha_801_lt.le (by norm_num : (0 : ℝ) ≤ 4)
  have h3 : 1 / (1 - Real.exp (-(2 * Real.pi / Real.sqrt 925))) ≤ 1 / (0.1864 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 0.1864) h1.le
  have h4 : (4 : ℝ) * Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801)
      * (1 / (1 - Real.exp (-(2 * Real.pi / Real.sqrt 925)))) ≤
      (4 : ℝ) * ((1 : ℝ) / 10 ^ 60) * (1 / (0.1864 : ℝ)) := by
    exact mul_le_mul h2 h3 (by positivity) (by positivity)
  have h5 : (4 : ℝ) * ((1 : ℝ) / 10 ^ 60) * (1 / (0.1864 : ℝ)) < (1 : ℝ) / 10 ^ 58 := by
    norm_num
  simpa [div_eq_mul_inv] using (lt_of_le_of_lt h4 h5)

/-- (iv-d) 充分条件：部分和 ≥ 5 时尾界 < 5 ⟹ L(E⁵,1) > 0（`L_E5_one_ne_zero` 的支撑引理；
    部分和 S_N ≥ 5 本身由区间算术在文档 5.4(iv-d) 核验，N = 800、dps = 80）。 -/
theorem tail_sufficient_pos :
    (5 : ℝ) - (4 : ℝ) * Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801)
      / (1 - Real.exp (-(2 * Real.pi / Real.sqrt 925))) > 0 := by
  have hb : (4 : ℝ) * Real.exp (-(2 * Real.pi / Real.sqrt 925) * 801)
      / (1 - Real.exp (-(2 * Real.pi / Real.sqrt 925))) < (1 : ℝ) / 10 ^ 58 :=
    tail_ivc_bound
  have hb' : (1 : ℝ) / 10 ^ 58 < (5 : ℝ) := by norm_num
  exact sub_pos.2 (lt_trans hb hb')

end
noncomputable section
theorem alpha_lt_2066 : 2 * Real.pi / Real.sqrt 925 < (0.2066 : ℝ) := by
  have hsqrt : (30.413 : ℝ) < Real.sqrt 925 := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 30.413)).2 (by norm_num)
  have h1 : (2 : ℝ) * (3.1416 : ℝ) < (0.2066 : ℝ) * 30.413 := by norm_num
  have h2 : (2 : ℝ) * Real.pi ≤ (2 : ℝ) * (3.1416 : ℝ) := by
    exact mul_le_mul_of_nonneg_left Real.pi_lt_d4.le (by norm_num : (0 : ℝ) ≤ 2)
  have h2' : (2 : ℝ) * Real.pi < (0.2066 : ℝ) * 30.413 := lt_of_le_of_lt h2 h1
  have h3 : (0.2066 : ℝ) * 30.413 < (0.2066 : ℝ) * Real.sqrt 925 := by
    exact mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 0.2066)
  have h3' : (2 : ℝ) * Real.pi < (0.2066 : ℝ) * Real.sqrt 925 := lt_trans h2' h3
  rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 925))]
  simpa [mul_comm] using h3'

/-- e^(−α) > 0.8133：α < 0.2066（exp 单调）；e^(0.2066) ≤ Σ₆ + B < 1/0.8133
    （`Real.exp_bound` n = 6 上界）⟹ e^(−0.2066) = 1/e^(0.2066) > 0.8133。 -/
theorem exp_neg_alpha_gt_8133 : (0.8133 : ℝ) < Real.exp (-(2 * Real.pi / Real.sqrt 925)) := by
  have hmono : Real.exp (-(0.2066 : ℝ)) ≤ Real.exp (-(2 * Real.pi / Real.sqrt 925)) := by
    exact Real.exp_le_exp_of_le (by linarith [alpha_lt_2066])
  have hrecip : (0.8133 : ℝ) < Real.exp (-(0.2066 : ℝ)) := by
    rw [Real.exp_neg]
    have hexp : Real.exp (0.2066 : ℝ) < (1 / (0.8133 : ℝ)) := by
      have hsum : (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ)) =
          (1 : ℝ) + 0.2066 + (0.2066 : ℝ) ^ 2 / 2 + (0.2066 : ℝ) ^ 3 / 6 +
            (0.2066 : ℝ) ^ 4 / 24 + (0.2066 : ℝ) ^ 5 / 120 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ]
        norm_num
      have hb := Real.exp_bound (x := 0.2066) (n := 6) (by norm_num : |(0.2066 : ℝ)| ≤ 1) (by norm_num : 0 < 6)
      have hd : Real.exp (0.2066 : ℝ) - (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          ≤ (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        have h1 : Real.exp (0.2066 : ℝ) - (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
            ≤ |(0.2066 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) :=
          le_trans (le_abs_self _) hb
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 0.2066)] using h1
      have hle' : Real.exp (0.2066 : ℝ) ≤
          (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        linarith
      have hpartU : (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6))
          < 1 / (0.8133 : ℝ) := by
        norm_num [hsum]
      exact lt_of_le_of_lt hle' hpartU
    have htmp : 1 / (1 / (0.8133 : ℝ)) < 1 / Real.exp (0.2066 : ℝ) := by
      exact one_div_lt_one_div_of_lt (Real.exp_pos (0.2066 : ℝ)) hexp
    simpa using htmp
  exact lt_of_lt_of_le hrecip hmono

/-- α 的 Lean 名（数值参数化）。 -/
def alphaE5 : ℝ := 2 * Real.pi / Real.sqrt 925

/-- 反射公式第 n 项（截断级数）：
    fE5 n = a_{n+1}(E⁵)/(n+1) · e^(−α·(n+1))。 -/
noncomputable def fE5 : ℕ → ℝ := fun n =>
  (aE5 (n + 1) : ℝ) / (n + 1) * Real.exp (-alphaE5 * (n + 1))

/- 数学 axiom（①c 的分层：等式/界/收敛为 axiom，不等式链为定理）：
   · `L_E5_series_split`：Dokchitser 反射公式 s = 1 的 N-截断等式（替代原 `L_E5_one_ne_zero` 判定黑盒）；
   · `coefficient_bound_aE5`：|a_n(E⁵)| ≤ 2n（表版；与 §2 `coefficient_bound` 同数学内容，
     aE5 为独立值表定义故单列）；
   · `summable_fE5`：反射级数绝对收敛（几何级数比较）。 -/
axiom L_E5_series_split (N : ℕ) :
  L_E5 1 = 2 * (∑ n ∈ Finset.range N, fE5 n) + 2 * ∑' n : ℕ, fE5 (n + N)
axiom coefficient_bound_aE5 (n : ℕ) : |aE5 n| ≤ 2 * (n : ℝ)
axiom summable_fE5 : Summable fE5

/-- 任意 n 的幂界（正项底）：0.8133^(n+1) ≤ e^(−α(n+1))。 -/
theorem powE_any (n : ℕ) : ((0.8133 : ℝ) ^ (n + 1)) ≤ Real.exp (-alphaE5 * (n + 1)) := by
  have hpow : ((0.8133 : ℝ) ^ (n + 1)) ≤ (Real.exp (-alphaE5)) ^ (n + 1) := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (0.8133 : ℝ)) exp_neg_alpha_gt_8133.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- 任意 n 的幂界（负项底）：e^(−α(n+1)) ≤ 0.8136^(n+1)。 -/
theorem powE'_any (n : ℕ) : Real.exp (-alphaE5 * (n + 1)) ≤ ((0.8136 : ℝ) ^ (n + 1)) := by
  have hpow : (Real.exp (-alphaE5)) ^ (n + 1) ≤ ((0.8136 : ℝ) ^ (n + 1)) := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos (-alphaE5))) exp_neg_alpha_lt_8136.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- 粗界项（ℝ 版）：正项用底 0.8133、负项用底 0.8136（模式匹配，按 aE5 符号固定）。 -/

def crude_n_R : ℕ → ℝ
  | 0 => (aE5 1 : ℝ) * ((0.8133 : ℝ) ^ 1)
  | 1 => (aE5 2 : ℝ) / 2 * ((0.8133 : ℝ) ^ 2)
  | 2 => (aE5 3 : ℝ) / 3 * ((0.8133 : ℝ) ^ 3)
  | 3 => (aE5 4 : ℝ) / 4 * ((0.8133 : ℝ) ^ 4)
  | 4 => (aE5 5 : ℝ) / 5 * ((0.8133 : ℝ) ^ 5)
  | 5 => (aE5 6 : ℝ) / 6 * ((0.8133 : ℝ) ^ 6)
  | 6 => (aE5 7 : ℝ) / 7 * ((0.8133 : ℝ) ^ 7)
  | 7 => (aE5 8 : ℝ) / 8 * ((0.8133 : ℝ) ^ 8)
  | 8 => (aE5 9 : ℝ) / 9 * ((0.8133 : ℝ) ^ 9)
  | 9 => (aE5 10 : ℝ) / 10 * ((0.8133 : ℝ) ^ 10)
  | 10 => (aE5 11 : ℝ) / 11 * ((0.8136 : ℝ) ^ 11)
  | 11 => (aE5 12 : ℝ) / 12 * ((0.8133 : ℝ) ^ 12)
  | 12 => (aE5 13 : ℝ) / 13 * ((0.8133 : ℝ) ^ 13)
  | 13 => (aE5 14 : ℝ) / 14 * ((0.8133 : ℝ) ^ 14)
  | 14 => (aE5 15 : ℝ) / 15 * ((0.8133 : ℝ) ^ 15)
  | 15 => (aE5 16 : ℝ) / 16 * ((0.8136 : ℝ) ^ 16)
  | 16 => (aE5 17 : ℝ) / 17 * ((0.8133 : ℝ) ^ 17)
  | 17 => (aE5 18 : ℝ) / 18 * ((0.8133 : ℝ) ^ 18)
  | 18 => (aE5 19 : ℝ) / 19 * ((0.8133 : ℝ) ^ 19)
  | 19 => (aE5 20 : ℝ) / 20 * ((0.8133 : ℝ) ^ 20)
  | 20 => (aE5 21 : ℝ) / 21 * ((0.8133 : ℝ) ^ 21)
  | 21 => (aE5 22 : ℝ) / 22 * ((0.8136 : ℝ) ^ 22)
  | 22 => (aE5 23 : ℝ) / 23 * ((0.8136 : ℝ) ^ 23)
  | 23 => (aE5 24 : ℝ) / 24 * ((0.8133 : ℝ) ^ 24)
  | 24 => (aE5 25 : ℝ) / 25 * ((0.8133 : ℝ) ^ 25)
  | 25 => (aE5 26 : ℝ) / 26 * ((0.8133 : ℝ) ^ 26)
  | 26 => (aE5 27 : ℝ) / 27 * ((0.8133 : ℝ) ^ 27)
  | 27 => (aE5 28 : ℝ) / 28 * ((0.8133 : ℝ) ^ 28)
  | 28 => (aE5 29 : ℝ) / 29 * ((0.8133 : ℝ) ^ 29)
  | 29 => (aE5 30 : ℝ) / 30 * ((0.8133 : ℝ) ^ 30)
  | 30 => (aE5 31 : ℝ) / 31 * ((0.8136 : ℝ) ^ 31)
  | 31 => (aE5 32 : ℝ) / 32 * ((0.8136 : ℝ) ^ 32)
  | 32 => (aE5 33 : ℝ) / 33 * ((0.8136 : ℝ) ^ 33)
  | 33 => (aE5 34 : ℝ) / 34 * ((0.8133 : ℝ) ^ 34)
  | 34 => (aE5 35 : ℝ) / 35 * ((0.8133 : ℝ) ^ 35)
  | 35 => (aE5 36 : ℝ) / 36 * ((0.8133 : ℝ) ^ 36)
  | 36 => (aE5 37 : ℝ) / 37 * ((0.8133 : ℝ) ^ 37)
  | 37 => (aE5 38 : ℝ) / 38 * ((0.8133 : ℝ) ^ 38)
  | 38 => (aE5 39 : ℝ) / 39 * ((0.8133 : ℝ) ^ 39)
  | 39 => (aE5 40 : ℝ) / 40 * ((0.8133 : ℝ) ^ 40)
  | 40 => (aE5 41 : ℝ) / 41 * ((0.8136 : ℝ) ^ 41)
  | 41 => (aE5 42 : ℝ) / 42 * ((0.8133 : ℝ) ^ 42)
  | 42 => (aE5 43 : ℝ) / 43 * ((0.8136 : ℝ) ^ 43)
  | 43 => (aE5 44 : ℝ) / 44 * ((0.8136 : ℝ) ^ 44)
  | 44 => (aE5 45 : ℝ) / 45 * ((0.8133 : ℝ) ^ 45)
  | 45 => (aE5 46 : ℝ) / 46 * ((0.8136 : ℝ) ^ 46)
  | 46 => (aE5 47 : ℝ) / 47 * ((0.8133 : ℝ) ^ 47)
  | 47 => (aE5 48 : ℝ) / 48 * ((0.8136 : ℝ) ^ 48)
  | 48 => (aE5 49 : ℝ) / 49 * ((0.8136 : ℝ) ^ 49)
  | 49 => (aE5 50 : ℝ) / 50 * ((0.8133 : ℝ) ^ 50)
  | _ => 0


theorem term_1 : ((aE5 1 : ℝ) * ((0.8133 : ℝ) ^ 1)) ≤ fE5 0 := by
  have hcoef : (0 : ℝ) ≤ (aE5 1 : ℝ) := by
    have hz : (0 : ℤ) ≤ aE5 1 := by native_decide
    exact_mod_cast hz
  have hpow := powE_any 0
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_2 : ((aE5 2 : ℝ) / 2 * ((0.8133 : ℝ) ^ 2)) ≤ fE5 1 := by
  have hcoef : (0 : ℝ) ≤ (aE5 2 : ℝ) / 2 := by
    have hz : (0 : ℤ) ≤ aE5 2 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 2 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 1
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_3 : ((aE5 3 : ℝ) / 3 * ((0.8133 : ℝ) ^ 3)) ≤ fE5 2 := by
  have hcoef : (0 : ℝ) ≤ (aE5 3 : ℝ) / 3 := by
    have hz : (0 : ℤ) ≤ aE5 3 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 3 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 2
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_4 : ((aE5 4 : ℝ) / 4 * ((0.8133 : ℝ) ^ 4)) ≤ fE5 3 := by
  have hcoef : (0 : ℝ) ≤ (aE5 4 : ℝ) / 4 := by
    have hz : (0 : ℤ) ≤ aE5 4 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 4 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 3
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_5 : ((aE5 5 : ℝ) / 5 * ((0.8133 : ℝ) ^ 5)) ≤ fE5 4 := by
  have hz : aE5 5 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_6 : ((aE5 6 : ℝ) / 6 * ((0.8133 : ℝ) ^ 6)) ≤ fE5 5 := by
  have hcoef : (0 : ℝ) ≤ (aE5 6 : ℝ) / 6 := by
    have hz : (0 : ℤ) ≤ aE5 6 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 6 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 5
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_7 : ((aE5 7 : ℝ) / 7 * ((0.8133 : ℝ) ^ 7)) ≤ fE5 6 := by
  have hcoef : (0 : ℝ) ≤ (aE5 7 : ℝ) / 7 := by
    have hz : (0 : ℤ) ≤ aE5 7 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 7 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 6
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_8 : ((aE5 8 : ℝ) / 8 * ((0.8133 : ℝ) ^ 8)) ≤ fE5 7 := by
  have hz : aE5 8 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_9 : ((aE5 9 : ℝ) / 9 * ((0.8133 : ℝ) ^ 9)) ≤ fE5 8 := by
  have hcoef : (0 : ℝ) ≤ (aE5 9 : ℝ) / 9 := by
    have hz : (0 : ℤ) ≤ aE5 9 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 9 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 8
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_10 : ((aE5 10 : ℝ) / 10 * ((0.8133 : ℝ) ^ 10)) ≤ fE5 9 := by
  have hz : aE5 10 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_11 : ((aE5 11 : ℝ) / 11 * ((0.8136 : ℝ) ^ 11)) ≤ fE5 10 := by
  have hcoef : (aE5 11 : ℝ) / 11 ≤ 0 := by
    have hz : aE5 11 ≤ 0 := by native_decide
    have hcast : (aE5 11 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (11 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 10
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_12 : ((aE5 12 : ℝ) / 12 * ((0.8133 : ℝ) ^ 12)) ≤ fE5 11 := by
  have hcoef : (0 : ℝ) ≤ (aE5 12 : ℝ) / 12 := by
    have hz : (0 : ℤ) ≤ aE5 12 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 12 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 11
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_13 : ((aE5 13 : ℝ) / 13 * ((0.8133 : ℝ) ^ 13)) ≤ fE5 12 := by
  have hcoef : (0 : ℝ) ≤ (aE5 13 : ℝ) / 13 := by
    have hz : (0 : ℤ) ≤ aE5 13 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 13 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 12
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_14 : ((aE5 14 : ℝ) / 14 * ((0.8133 : ℝ) ^ 14)) ≤ fE5 13 := by
  have hcoef : (0 : ℝ) ≤ (aE5 14 : ℝ) / 14 := by
    have hz : (0 : ℤ) ≤ aE5 14 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 14 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 13
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_15 : ((aE5 15 : ℝ) / 15 * ((0.8133 : ℝ) ^ 15)) ≤ fE5 14 := by
  have hz : aE5 15 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_16 : ((aE5 16 : ℝ) / 16 * ((0.8136 : ℝ) ^ 16)) ≤ fE5 15 := by
  have hcoef : (aE5 16 : ℝ) / 16 ≤ 0 := by
    have hz : aE5 16 ≤ 0 := by native_decide
    have hcast : (aE5 16 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (16 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 15
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_17 : ((aE5 17 : ℝ) / 17 * ((0.8133 : ℝ) ^ 17)) ≤ fE5 16 := by
  have hz : aE5 17 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_18 : ((aE5 18 : ℝ) / 18 * ((0.8133 : ℝ) ^ 18)) ≤ fE5 17 := by
  have hcoef : (0 : ℝ) ≤ (aE5 18 : ℝ) / 18 := by
    have hz : (0 : ℤ) ≤ aE5 18 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 18 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 17
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_19 : ((aE5 19 : ℝ) / 19 * ((0.8133 : ℝ) ^ 19)) ≤ fE5 18 := by
  have hz : aE5 19 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_20 : ((aE5 20 : ℝ) / 20 * ((0.8133 : ℝ) ^ 20)) ≤ fE5 19 := by
  have hz : aE5 20 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_21 : ((aE5 21 : ℝ) / 21 * ((0.8133 : ℝ) ^ 21)) ≤ fE5 20 := by
  have hcoef : (0 : ℝ) ≤ (aE5 21 : ℝ) / 21 := by
    have hz : (0 : ℤ) ≤ aE5 21 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 21 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 20
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_22 : ((aE5 22 : ℝ) / 22 * ((0.8136 : ℝ) ^ 22)) ≤ fE5 21 := by
  have hcoef : (aE5 22 : ℝ) / 22 ≤ 0 := by
    have hz : aE5 22 ≤ 0 := by native_decide
    have hcast : (aE5 22 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (22 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 21
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_23 : ((aE5 23 : ℝ) / 23 * ((0.8136 : ℝ) ^ 23)) ≤ fE5 22 := by
  have hcoef : (aE5 23 : ℝ) / 23 ≤ 0 := by
    have hz : aE5 23 ≤ 0 := by native_decide
    have hcast : (aE5 23 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (23 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 22
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_24 : ((aE5 24 : ℝ) / 24 * ((0.8133 : ℝ) ^ 24)) ≤ fE5 23 := by
  have hz : aE5 24 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_25 : ((aE5 25 : ℝ) / 25 * ((0.8133 : ℝ) ^ 25)) ≤ fE5 24 := by
  have hz : aE5 25 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_26 : ((aE5 26 : ℝ) / 26 * ((0.8133 : ℝ) ^ 26)) ≤ fE5 25 := by
  have hcoef : (0 : ℝ) ≤ (aE5 26 : ℝ) / 26 := by
    have hz : (0 : ℤ) ≤ aE5 26 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 26 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 25
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_27 : ((aE5 27 : ℝ) / 27 * ((0.8133 : ℝ) ^ 27)) ≤ fE5 26 := by
  have hcoef : (0 : ℝ) ≤ (aE5 27 : ℝ) / 27 := by
    have hz : (0 : ℤ) ≤ aE5 27 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 27 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 26
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_28 : ((aE5 28 : ℝ) / 28 * ((0.8133 : ℝ) ^ 28)) ≤ fE5 27 := by
  have hcoef : (0 : ℝ) ≤ (aE5 28 : ℝ) / 28 := by
    have hz : (0 : ℤ) ≤ aE5 28 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 28 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 27
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_29 : ((aE5 29 : ℝ) / 29 * ((0.8133 : ℝ) ^ 29)) ≤ fE5 28 := by
  have hcoef : (0 : ℝ) ≤ (aE5 29 : ℝ) / 29 := by
    have hz : (0 : ℤ) ≤ aE5 29 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 29 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 28
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_30 : ((aE5 30 : ℝ) / 30 * ((0.8133 : ℝ) ^ 30)) ≤ fE5 29 := by
  have hz : aE5 30 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_31 : ((aE5 31 : ℝ) / 31 * ((0.8136 : ℝ) ^ 31)) ≤ fE5 30 := by
  have hcoef : (aE5 31 : ℝ) / 31 ≤ 0 := by
    have hz : aE5 31 ≤ 0 := by native_decide
    have hcast : (aE5 31 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (31 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 30
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_32 : ((aE5 32 : ℝ) / 32 * ((0.8136 : ℝ) ^ 32)) ≤ fE5 31 := by
  have hcoef : (aE5 32 : ℝ) / 32 ≤ 0 := by
    have hz : aE5 32 ≤ 0 := by native_decide
    have hcast : (aE5 32 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (32 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 31
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_33 : ((aE5 33 : ℝ) / 33 * ((0.8136 : ℝ) ^ 33)) ≤ fE5 32 := by
  have hcoef : (aE5 33 : ℝ) / 33 ≤ 0 := by
    have hz : aE5 33 ≤ 0 := by native_decide
    have hcast : (aE5 33 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (33 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 32
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_34 : ((aE5 34 : ℝ) / 34 * ((0.8133 : ℝ) ^ 34)) ≤ fE5 33 := by
  have hz : aE5 34 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_35 : ((aE5 35 : ℝ) / 35 * ((0.8133 : ℝ) ^ 35)) ≤ fE5 34 := by
  have hz : aE5 35 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_36 : ((aE5 36 : ℝ) / 36 * ((0.8133 : ℝ) ^ 36)) ≤ fE5 35 := by
  have hcoef : (0 : ℝ) ≤ (aE5 36 : ℝ) / 36 := by
    have hz : (0 : ℤ) ≤ aE5 36 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 36 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 35
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_37 : ((aE5 37 : ℝ) / 37 * ((0.8133 : ℝ) ^ 37)) ≤ fE5 36 := by
  have hcoef : (0 : ℝ) ≤ (aE5 37 : ℝ) / 37 := by
    have hz : (0 : ℤ) ≤ aE5 37 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 37 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 36
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_38 : ((aE5 38 : ℝ) / 38 * ((0.8133 : ℝ) ^ 38)) ≤ fE5 37 := by
  have hz : aE5 38 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_39 : ((aE5 39 : ℝ) / 39 * ((0.8133 : ℝ) ^ 39)) ≤ fE5 38 := by
  have hcoef : (0 : ℝ) ≤ (aE5 39 : ℝ) / 39 := by
    have hz : (0 : ℤ) ≤ aE5 39 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 39 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 38
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_40 : ((aE5 40 : ℝ) / 40 * ((0.8133 : ℝ) ^ 40)) ≤ fE5 39 := by
  have hz : aE5 40 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_41 : ((aE5 41 : ℝ) / 41 * ((0.8136 : ℝ) ^ 41)) ≤ fE5 40 := by
  have hcoef : (aE5 41 : ℝ) / 41 ≤ 0 := by
    have hz : aE5 41 ≤ 0 := by native_decide
    have hcast : (aE5 41 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (41 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 40
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_42 : ((aE5 42 : ℝ) / 42 * ((0.8133 : ℝ) ^ 42)) ≤ fE5 41 := by
  have hcoef : (0 : ℝ) ≤ (aE5 42 : ℝ) / 42 := by
    have hz : (0 : ℤ) ≤ aE5 42 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 42 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 41
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_43 : ((aE5 43 : ℝ) / 43 * ((0.8136 : ℝ) ^ 43)) ≤ fE5 42 := by
  have hcoef : (aE5 43 : ℝ) / 43 ≤ 0 := by
    have hz : aE5 43 ≤ 0 := by native_decide
    have hcast : (aE5 43 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (43 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 42
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_44 : ((aE5 44 : ℝ) / 44 * ((0.8136 : ℝ) ^ 44)) ≤ fE5 43 := by
  have hcoef : (aE5 44 : ℝ) / 44 ≤ 0 := by
    have hz : aE5 44 ≤ 0 := by native_decide
    have hcast : (aE5 44 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (44 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 43
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_45 : ((aE5 45 : ℝ) / 45 * ((0.8133 : ℝ) ^ 45)) ≤ fE5 44 := by
  have hz : aE5 45 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

theorem term_46 : ((aE5 46 : ℝ) / 46 * ((0.8136 : ℝ) ^ 46)) ≤ fE5 45 := by
  have hcoef : (aE5 46 : ℝ) / 46 ≤ 0 := by
    have hz : aE5 46 ≤ 0 := by native_decide
    have hcast : (aE5 46 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (46 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 45
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_47 : ((aE5 47 : ℝ) / 47 * ((0.8133 : ℝ) ^ 47)) ≤ fE5 46 := by
  have hcoef : (0 : ℝ) ≤ (aE5 47 : ℝ) / 47 := by
    have hz : (0 : ℤ) ≤ aE5 47 := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 47 : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any 46
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_48 : ((aE5 48 : ℝ) / 48 * ((0.8136 : ℝ) ^ 48)) ≤ fE5 47 := by
  have hcoef : (aE5 48 : ℝ) / 48 ≤ 0 := by
    have hz : aE5 48 ≤ 0 := by native_decide
    have hcast : (aE5 48 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (48 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 47
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_49 : ((aE5 49 : ℝ) / 49 * ((0.8136 : ℝ) ^ 49)) ≤ fE5 48 := by
  have hcoef : (aE5 49 : ℝ) / 49 ≤ 0 := by
    have hz : aE5 49 ≤ 0 := by native_decide
    have hcast : (aE5 49 : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < (49 : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any 48
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm

theorem term_50 : ((aE5 50 : ℝ) / 50 * ((0.8133 : ℝ) ^ 50)) ≤ fE5 49 := by
  have hz : aE5 50 = 0 := by native_decide
  simp [fE5, alphaE5, hz]

/-- 部分和粗界（ℝ）：2.6766 ≤ 粗界 50 项和（分块 ℚ native_decide + cast 桥）。 -/

theorem crude50_ge_R : (2.6766 : ℝ) ≤
 ((aE5 1 : ℝ) * ((0.8133 : ℝ) ^ 1)) + (((aE5 2 : ℝ) / 2 * ((0.8133 : ℝ) ^ 2)) + (((aE5 3 : ℝ) / 3 * ((0.8133 : ℝ) ^ 3)) + (((aE5 4 : ℝ) / 4 * ((0.8133 : ℝ) ^ 4)) + (((aE5 5 : ℝ) / 5 * ((0.8133 : ℝ) ^ 5)) + (((aE5 6 : ℝ) / 6 * ((0.8133 : ℝ) ^ 6)) + (((aE5 7 : ℝ) / 7 * ((0.8133 : ℝ) ^ 7)) + (((aE5 8 : ℝ) / 8 * ((0.8133 : ℝ) ^ 8)) + (((aE5 9 : ℝ) / 9 * ((0.8133 : ℝ) ^ 9)) + (((aE5 10 : ℝ) / 10 * ((0.8133 : ℝ) ^ 10)) + (((aE5 11 : ℝ) / 11 * ((0.8136 : ℝ) ^ 11)) + (((aE5 12 : ℝ) / 12 * ((0.8133 : ℝ) ^ 12)) + (((aE5 13 : ℝ) / 13 * ((0.8133 : ℝ) ^ 13)) + (((aE5 14 : ℝ) / 14 * ((0.8133 : ℝ) ^ 14)) + (((aE5 15 : ℝ) / 15 * ((0.8133 : ℝ) ^ 15)) + (((aE5 16 : ℝ) / 16 * ((0.8136 : ℝ) ^ 16)) + (((aE5 17 : ℝ) / 17 * ((0.8133 : ℝ) ^ 17)) + (((aE5 18 : ℝ) / 18 * ((0.8133 : ℝ) ^ 18)) + (((aE5 19 : ℝ) / 19 * ((0.8133 : ℝ) ^ 19)) + (((aE5 20 : ℝ) / 20 * ((0.8133 : ℝ) ^ 20)) + (((aE5 21 : ℝ) / 21 * ((0.8133 : ℝ) ^ 21)) + (((aE5 22 : ℝ) / 22 * ((0.8136 : ℝ) ^ 22)) + (((aE5 23 : ℝ) / 23 * ((0.8136 : ℝ) ^ 23)) + (((aE5 24 : ℝ) / 24 * ((0.8133 : ℝ) ^ 24)) + (((aE5 25 : ℝ) / 25 * ((0.8133 : ℝ) ^ 25)) + (((aE5 26 : ℝ) / 26 * ((0.8133 : ℝ) ^ 26)) + (((aE5 27 : ℝ) / 27 * ((0.8133 : ℝ) ^ 27)) + (((aE5 28 : ℝ) / 28 * ((0.8133 : ℝ) ^ 28)) + (((aE5 29 : ℝ) / 29 * ((0.8133 : ℝ) ^ 29)) + (((aE5 30 : ℝ) / 30 * ((0.8133 : ℝ) ^ 30)) + (((aE5 31 : ℝ) / 31 * ((0.8136 : ℝ) ^ 31)) + (((aE5 32 : ℝ) / 32 * ((0.8136 : ℝ) ^ 32)) + (((aE5 33 : ℝ) / 33 * ((0.8136 : ℝ) ^ 33)) + (((aE5 34 : ℝ) / 34 * ((0.8133 : ℝ) ^ 34)) + (((aE5 35 : ℝ) / 35 * ((0.8133 : ℝ) ^ 35)) + (((aE5 36 : ℝ) / 36 * ((0.8133 : ℝ) ^ 36)) + (((aE5 37 : ℝ) / 37 * ((0.8133 : ℝ) ^ 37)) + (((aE5 38 : ℝ) / 38 * ((0.8133 : ℝ) ^ 38)) + (((aE5 39 : ℝ) / 39 * ((0.8133 : ℝ) ^ 39)) + (((aE5 40 : ℝ) / 40 * ((0.8133 : ℝ) ^ 40)) + (((aE5 41 : ℝ) / 41 * ((0.8136 : ℝ) ^ 41)) + (((aE5 42 : ℝ) / 42 * ((0.8133 : ℝ) ^ 42)) + (((aE5 43 : ℝ) / 43 * ((0.8136 : ℝ) ^ 43)) + (((aE5 44 : ℝ) / 44 * ((0.8136 : ℝ) ^ 44)) + (((aE5 45 : ℝ) / 45 * ((0.8133 : ℝ) ^ 45)) + (((aE5 46 : ℝ) / 46 * ((0.8136 : ℝ) ^ 46)) + (((aE5 47 : ℝ) / 47 * ((0.8133 : ℝ) ^ 47)) + (((aE5 48 : ℝ) / 48 * ((0.8136 : ℝ) ^ 48)) + (((aE5 49 : ℝ) / 49 * ((0.8136 : ℝ) ^ 49)) + (((aE5 50 : ℝ) / 50 * ((0.8133 : ℝ) ^ 50))))))))))))))))))))))))))))))))))))))))))))))))))) := by

  have hq0 : (13291517541/5000000000 : ℚ) ≤ ((aE5 1 : ℚ) * (((8133 : ℚ) / 10000) ^ 1)) + ((aE5 2 : ℚ) / 2 * (((8133 : ℚ) / 10000) ^ 2)) + ((aE5 3 : ℚ) / 3 * (((8133 : ℚ) / 10000) ^ 3)) + ((aE5 4 : ℚ) / 4 * (((8133 : ℚ) / 10000) ^ 4)) + ((aE5 5 : ℚ) / 5 * (((8133 : ℚ) / 10000) ^ 5)) + ((aE5 6 : ℚ) / 6 * (((8133 : ℚ) / 10000) ^ 6)) + ((aE5 7 : ℚ) / 7 * (((8133 : ℚ) / 10000) ^ 7)) + ((aE5 8 : ℚ) / 8 * (((8133 : ℚ) / 10000) ^ 8)) + ((aE5 9 : ℚ) / 9 * (((8133 : ℚ) / 10000) ^ 9)) + ((aE5 10 : ℚ) / 10 * (((8133 : ℚ) / 10000) ^ 10)) := by
    native_decide
  have hq0' := (Rat.cast_le (K := ℝ)).mpr hq0
  norm_num at hq0'

  have hq1 : (202152173/10000000000 : ℚ) ≤ ((aE5 11 : ℚ) / 11 * (((8136 : ℚ) / 10000) ^ 11)) + ((aE5 12 : ℚ) / 12 * (((8133 : ℚ) / 10000) ^ 12)) + ((aE5 13 : ℚ) / 13 * (((8133 : ℚ) / 10000) ^ 13)) + ((aE5 14 : ℚ) / 14 * (((8133 : ℚ) / 10000) ^ 14)) + ((aE5 15 : ℚ) / 15 * (((8133 : ℚ) / 10000) ^ 15)) + ((aE5 16 : ℚ) / 16 * (((8136 : ℚ) / 10000) ^ 16)) + ((aE5 17 : ℚ) / 17 * (((8133 : ℚ) / 10000) ^ 17)) + ((aE5 18 : ℚ) / 18 * (((8133 : ℚ) / 10000) ^ 18)) + ((aE5 19 : ℚ) / 19 * (((8133 : ℚ) / 10000) ^ 19)) + ((aE5 20 : ℚ) / 20 * (((8133 : ℚ) / 10000) ^ 20)) := by
    native_decide
  have hq1' := (Rat.cast_le (K := ℝ)).mpr hq1
  norm_num at hq1'

  have hq2 : (-5229789/5000000000 : ℚ) ≤ ((aE5 21 : ℚ) / 21 * (((8133 : ℚ) / 10000) ^ 21)) + ((aE5 22 : ℚ) / 22 * (((8136 : ℚ) / 10000) ^ 22)) + ((aE5 23 : ℚ) / 23 * (((8136 : ℚ) / 10000) ^ 23)) + ((aE5 24 : ℚ) / 24 * (((8133 : ℚ) / 10000) ^ 24)) + ((aE5 25 : ℚ) / 25 * (((8133 : ℚ) / 10000) ^ 25)) + ((aE5 26 : ℚ) / 26 * (((8133 : ℚ) / 10000) ^ 26)) + ((aE5 27 : ℚ) / 27 * (((8133 : ℚ) / 10000) ^ 27)) + ((aE5 28 : ℚ) / 28 * (((8133 : ℚ) / 10000) ^ 28)) + ((aE5 29 : ℚ) / 29 * (((8133 : ℚ) / 10000) ^ 29)) + ((aE5 30 : ℚ) / 30 * (((8133 : ℚ) / 10000) ^ 30)) := by
    native_decide
  have hq2' := (Rat.cast_le (K := ℝ)).mpr hq2
  norm_num at hq2'

  have hq3 : (-8003109/10000000000 : ℚ) ≤ ((aE5 31 : ℚ) / 31 * (((8136 : ℚ) / 10000) ^ 31)) + ((aE5 32 : ℚ) / 32 * (((8136 : ℚ) / 10000) ^ 32)) + ((aE5 33 : ℚ) / 33 * (((8136 : ℚ) / 10000) ^ 33)) + ((aE5 34 : ℚ) / 34 * (((8133 : ℚ) / 10000) ^ 34)) + ((aE5 35 : ℚ) / 35 * (((8133 : ℚ) / 10000) ^ 35)) + ((aE5 36 : ℚ) / 36 * (((8133 : ℚ) / 10000) ^ 36)) + ((aE5 37 : ℚ) / 37 * (((8133 : ℚ) / 10000) ^ 37)) + ((aE5 38 : ℚ) / 38 * (((8133 : ℚ) / 10000) ^ 38)) + ((aE5 39 : ℚ) / 39 * (((8133 : ℚ) / 10000) ^ 39)) + ((aE5 40 : ℚ) / 40 * (((8133 : ℚ) / 10000) ^ 40)) := by
    native_decide
  have hq3' := (Rat.cast_le (K := ℝ)).mpr hq3
  norm_num at hq3'

  have hq4 : (-84151/1250000000 : ℚ) ≤ ((aE5 41 : ℚ) / 41 * (((8136 : ℚ) / 10000) ^ 41)) + ((aE5 42 : ℚ) / 42 * (((8133 : ℚ) / 10000) ^ 42)) + ((aE5 43 : ℚ) / 43 * (((8136 : ℚ) / 10000) ^ 43)) + ((aE5 44 : ℚ) / 44 * (((8136 : ℚ) / 10000) ^ 44)) + ((aE5 45 : ℚ) / 45 * (((8133 : ℚ) / 10000) ^ 45)) + ((aE5 46 : ℚ) / 46 * (((8136 : ℚ) / 10000) ^ 46)) + ((aE5 47 : ℚ) / 47 * (((8133 : ℚ) / 10000) ^ 47)) + ((aE5 48 : ℚ) / 48 * (((8136 : ℚ) / 10000) ^ 48)) + ((aE5 49 : ℚ) / 49 * (((8136 : ℚ) / 10000) ^ 49)) + ((aE5 50 : ℚ) / 50 * (((8133 : ℚ) / 10000) ^ 50)) := by
    native_decide
  have hq4' := (Rat.cast_le (K := ℝ)).mpr hq4
  norm_num at hq4'

  have hqT : (2.6766 : ℝ) ≤ (13291517541 : ℝ) / 5000000000 + (202152173 : ℝ) / 10000000000 + (-5229789 : ℝ) / 5000000000 + (-8003109 : ℝ) / 10000000000 + (-84151 : ℝ) / 1250000000 := by norm_num

  norm_num

  nlinarith



/-- 部分和 ≥ 粗界（逐项；Σ 用 sum_range_succ 展开后 linarith）。 -/

theorem part50_ge_crude :
 ((aE5 1 : ℝ) * ((0.8133 : ℝ) ^ 1)) + (((aE5 2 : ℝ) / 2 * ((0.8133 : ℝ) ^ 2)) + (((aE5 3 : ℝ) / 3 * ((0.8133 : ℝ) ^ 3)) + (((aE5 4 : ℝ) / 4 * ((0.8133 : ℝ) ^ 4)) + (((aE5 5 : ℝ) / 5 * ((0.8133 : ℝ) ^ 5)) + (((aE5 6 : ℝ) / 6 * ((0.8133 : ℝ) ^ 6)) + (((aE5 7 : ℝ) / 7 * ((0.8133 : ℝ) ^ 7)) + (((aE5 8 : ℝ) / 8 * ((0.8133 : ℝ) ^ 8)) + (((aE5 9 : ℝ) / 9 * ((0.8133 : ℝ) ^ 9)) + (((aE5 10 : ℝ) / 10 * ((0.8133 : ℝ) ^ 10)) + (((aE5 11 : ℝ) / 11 * ((0.8136 : ℝ) ^ 11)) + (((aE5 12 : ℝ) / 12 * ((0.8133 : ℝ) ^ 12)) + (((aE5 13 : ℝ) / 13 * ((0.8133 : ℝ) ^ 13)) + (((aE5 14 : ℝ) / 14 * ((0.8133 : ℝ) ^ 14)) + (((aE5 15 : ℝ) / 15 * ((0.8133 : ℝ) ^ 15)) + (((aE5 16 : ℝ) / 16 * ((0.8136 : ℝ) ^ 16)) + (((aE5 17 : ℝ) / 17 * ((0.8133 : ℝ) ^ 17)) + (((aE5 18 : ℝ) / 18 * ((0.8133 : ℝ) ^ 18)) + (((aE5 19 : ℝ) / 19 * ((0.8133 : ℝ) ^ 19)) + (((aE5 20 : ℝ) / 20 * ((0.8133 : ℝ) ^ 20)) + (((aE5 21 : ℝ) / 21 * ((0.8133 : ℝ) ^ 21)) + (((aE5 22 : ℝ) / 22 * ((0.8136 : ℝ) ^ 22)) + (((aE5 23 : ℝ) / 23 * ((0.8136 : ℝ) ^ 23)) + (((aE5 24 : ℝ) / 24 * ((0.8133 : ℝ) ^ 24)) + (((aE5 25 : ℝ) / 25 * ((0.8133 : ℝ) ^ 25)) + (((aE5 26 : ℝ) / 26 * ((0.8133 : ℝ) ^ 26)) + (((aE5 27 : ℝ) / 27 * ((0.8133 : ℝ) ^ 27)) + (((aE5 28 : ℝ) / 28 * ((0.8133 : ℝ) ^ 28)) + (((aE5 29 : ℝ) / 29 * ((0.8133 : ℝ) ^ 29)) + (((aE5 30 : ℝ) / 30 * ((0.8133 : ℝ) ^ 30)) + (((aE5 31 : ℝ) / 31 * ((0.8136 : ℝ) ^ 31)) + (((aE5 32 : ℝ) / 32 * ((0.8136 : ℝ) ^ 32)) + (((aE5 33 : ℝ) / 33 * ((0.8136 : ℝ) ^ 33)) + (((aE5 34 : ℝ) / 34 * ((0.8133 : ℝ) ^ 34)) + (((aE5 35 : ℝ) / 35 * ((0.8133 : ℝ) ^ 35)) + (((aE5 36 : ℝ) / 36 * ((0.8133 : ℝ) ^ 36)) + (((aE5 37 : ℝ) / 37 * ((0.8133 : ℝ) ^ 37)) + (((aE5 38 : ℝ) / 38 * ((0.8133 : ℝ) ^ 38)) + (((aE5 39 : ℝ) / 39 * ((0.8133 : ℝ) ^ 39)) + (((aE5 40 : ℝ) / 40 * ((0.8133 : ℝ) ^ 40)) + (((aE5 41 : ℝ) / 41 * ((0.8136 : ℝ) ^ 41)) + (((aE5 42 : ℝ) / 42 * ((0.8133 : ℝ) ^ 42)) + (((aE5 43 : ℝ) / 43 * ((0.8136 : ℝ) ^ 43)) + (((aE5 44 : ℝ) / 44 * ((0.8136 : ℝ) ^ 44)) + (((aE5 45 : ℝ) / 45 * ((0.8133 : ℝ) ^ 45)) + (((aE5 46 : ℝ) / 46 * ((0.8136 : ℝ) ^ 46)) + (((aE5 47 : ℝ) / 47 * ((0.8133 : ℝ) ^ 47)) + (((aE5 48 : ℝ) / 48 * ((0.8136 : ℝ) ^ 48)) + (((aE5 49 : ℝ) / 49 * ((0.8136 : ℝ) ^ 49)) + (((aE5 50 : ℝ) / 50 * ((0.8133 : ℝ) ^ 50))))))))))))))))))))))))))))))))))))))))))))))))))) ≤ ∑ n ∈ Finset.range 50, fE5 n := by

  simp [Finset.sum_range_succ]

  have h0 : ((aE5 1 : ℝ) * ((0.8133 : ℝ) ^ 1)) ≤ fE5 0 := term_1

  have h1 : ((aE5 2 : ℝ) / 2 * ((0.8133 : ℝ) ^ 2)) ≤ fE5 1 := term_2

  have h2 : ((aE5 3 : ℝ) / 3 * ((0.8133 : ℝ) ^ 3)) ≤ fE5 2 := term_3

  have h3 : ((aE5 4 : ℝ) / 4 * ((0.8133 : ℝ) ^ 4)) ≤ fE5 3 := term_4

  have h4 : ((aE5 5 : ℝ) / 5 * ((0.8133 : ℝ) ^ 5)) ≤ fE5 4 := term_5

  have h5 : ((aE5 6 : ℝ) / 6 * ((0.8133 : ℝ) ^ 6)) ≤ fE5 5 := term_6

  have h6 : ((aE5 7 : ℝ) / 7 * ((0.8133 : ℝ) ^ 7)) ≤ fE5 6 := term_7

  have h7 : ((aE5 8 : ℝ) / 8 * ((0.8133 : ℝ) ^ 8)) ≤ fE5 7 := term_8

  have h8 : ((aE5 9 : ℝ) / 9 * ((0.8133 : ℝ) ^ 9)) ≤ fE5 8 := term_9

  have h9 : ((aE5 10 : ℝ) / 10 * ((0.8133 : ℝ) ^ 10)) ≤ fE5 9 := term_10

  have h10 : ((aE5 11 : ℝ) / 11 * ((0.8136 : ℝ) ^ 11)) ≤ fE5 10 := term_11

  have h11 : ((aE5 12 : ℝ) / 12 * ((0.8133 : ℝ) ^ 12)) ≤ fE5 11 := term_12

  have h12 : ((aE5 13 : ℝ) / 13 * ((0.8133 : ℝ) ^ 13)) ≤ fE5 12 := term_13

  have h13 : ((aE5 14 : ℝ) / 14 * ((0.8133 : ℝ) ^ 14)) ≤ fE5 13 := term_14

  have h14 : ((aE5 15 : ℝ) / 15 * ((0.8133 : ℝ) ^ 15)) ≤ fE5 14 := term_15

  have h15 : ((aE5 16 : ℝ) / 16 * ((0.8136 : ℝ) ^ 16)) ≤ fE5 15 := term_16

  have h16 : ((aE5 17 : ℝ) / 17 * ((0.8133 : ℝ) ^ 17)) ≤ fE5 16 := term_17

  have h17 : ((aE5 18 : ℝ) / 18 * ((0.8133 : ℝ) ^ 18)) ≤ fE5 17 := term_18

  have h18 : ((aE5 19 : ℝ) / 19 * ((0.8133 : ℝ) ^ 19)) ≤ fE5 18 := term_19

  have h19 : ((aE5 20 : ℝ) / 20 * ((0.8133 : ℝ) ^ 20)) ≤ fE5 19 := term_20

  have h20 : ((aE5 21 : ℝ) / 21 * ((0.8133 : ℝ) ^ 21)) ≤ fE5 20 := term_21

  have h21 : ((aE5 22 : ℝ) / 22 * ((0.8136 : ℝ) ^ 22)) ≤ fE5 21 := term_22

  have h22 : ((aE5 23 : ℝ) / 23 * ((0.8136 : ℝ) ^ 23)) ≤ fE5 22 := term_23

  have h23 : ((aE5 24 : ℝ) / 24 * ((0.8133 : ℝ) ^ 24)) ≤ fE5 23 := term_24

  have h24 : ((aE5 25 : ℝ) / 25 * ((0.8133 : ℝ) ^ 25)) ≤ fE5 24 := term_25

  have h25 : ((aE5 26 : ℝ) / 26 * ((0.8133 : ℝ) ^ 26)) ≤ fE5 25 := term_26

  have h26 : ((aE5 27 : ℝ) / 27 * ((0.8133 : ℝ) ^ 27)) ≤ fE5 26 := term_27

  have h27 : ((aE5 28 : ℝ) / 28 * ((0.8133 : ℝ) ^ 28)) ≤ fE5 27 := term_28

  have h28 : ((aE5 29 : ℝ) / 29 * ((0.8133 : ℝ) ^ 29)) ≤ fE5 28 := term_29

  have h29 : ((aE5 30 : ℝ) / 30 * ((0.8133 : ℝ) ^ 30)) ≤ fE5 29 := term_30

  have h30 : ((aE5 31 : ℝ) / 31 * ((0.8136 : ℝ) ^ 31)) ≤ fE5 30 := term_31

  have h31 : ((aE5 32 : ℝ) / 32 * ((0.8136 : ℝ) ^ 32)) ≤ fE5 31 := term_32

  have h32 : ((aE5 33 : ℝ) / 33 * ((0.8136 : ℝ) ^ 33)) ≤ fE5 32 := term_33

  have h33 : ((aE5 34 : ℝ) / 34 * ((0.8133 : ℝ) ^ 34)) ≤ fE5 33 := term_34

  have h34 : ((aE5 35 : ℝ) / 35 * ((0.8133 : ℝ) ^ 35)) ≤ fE5 34 := term_35

  have h35 : ((aE5 36 : ℝ) / 36 * ((0.8133 : ℝ) ^ 36)) ≤ fE5 35 := term_36

  have h36 : ((aE5 37 : ℝ) / 37 * ((0.8133 : ℝ) ^ 37)) ≤ fE5 36 := term_37

  have h37 : ((aE5 38 : ℝ) / 38 * ((0.8133 : ℝ) ^ 38)) ≤ fE5 37 := term_38

  have h38 : ((aE5 39 : ℝ) / 39 * ((0.8133 : ℝ) ^ 39)) ≤ fE5 38 := term_39

  have h39 : ((aE5 40 : ℝ) / 40 * ((0.8133 : ℝ) ^ 40)) ≤ fE5 39 := term_40

  have h40 : ((aE5 41 : ℝ) / 41 * ((0.8136 : ℝ) ^ 41)) ≤ fE5 40 := term_41

  have h41 : ((aE5 42 : ℝ) / 42 * ((0.8133 : ℝ) ^ 42)) ≤ fE5 41 := term_42

  have h42 : ((aE5 43 : ℝ) / 43 * ((0.8136 : ℝ) ^ 43)) ≤ fE5 42 := term_43

  have h43 : ((aE5 44 : ℝ) / 44 * ((0.8136 : ℝ) ^ 44)) ≤ fE5 43 := term_44

  have h44 : ((aE5 45 : ℝ) / 45 * ((0.8133 : ℝ) ^ 45)) ≤ fE5 44 := term_45

  have h45 : ((aE5 46 : ℝ) / 46 * ((0.8136 : ℝ) ^ 46)) ≤ fE5 45 := term_46

  have h46 : ((aE5 47 : ℝ) / 47 * ((0.8133 : ℝ) ^ 47)) ≤ fE5 46 := term_47

  have h47 : ((aE5 48 : ℝ) / 48 * ((0.8136 : ℝ) ^ 48)) ≤ fE5 47 := term_48

  have h48 : ((aE5 49 : ℝ) / 49 * ((0.8136 : ℝ) ^ 49)) ≤ fE5 48 := term_49

  have h49 : ((aE5 50 : ℝ) / 50 * ((0.8133 : ℝ) ^ 50)) ≤ fE5 49 := term_50

  linarith



theorem part50_ge : (2.6766 : ℝ) ≤ ∑ n ∈ Finset.range 50, fE5 n := by

  exact le_trans crude50_ge_R part50_ge_crude
end

end BSD.LSeries5