import Mathlib.Data.Rat.Cast.Lemmas
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import BSD.LSeries5
import BSD.aE_table_43
import BSD.aE5_table_43

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# LSeries5_43 —— 43a1 (1,0) 实例的 E⁵ 侧闭证

E = 43a1 : y² + y = x³ + x²，N = 43；E⁵ = E ⊗ χ₅（模 5 二次扭），导子 N⁵ = 1075。
α = 2π/√1075 ≈ 0.1916；L(E⁵,1) ≈ 4.891（数值校准 calib43_float.py）。

结构（仿 LSeries5.lean 的 37a1 版；通用引理 import 复用，特化数值为本文件）：
  · 局部因子：ap_E_43 = 查表（aE_raw_43，200 项乘性表，素数处即 a_p）；
    ap5_43 在坏素 43 处乘性特判 +1（a₄₃(E) = −1 non-split，χ₅(43) = −1 ⟹ a₄₃(E⁵) = +1）；
  · 系数界：coefficient_bound_aE5_43（表版本 |aE5_43 n| ≤ 2n，native_decide 801 项）；
  · 收敛：summable_fE5_43（几何级数）；
  · 正性：L_E5_43_one_pos（部分和 ≥ 2.4 与尾界 2B < 1 组装），L_E5_43_one_ne_zero。
数学 axiom（设计口径同 37 版）：L_E5_series_split_43（Dokchitser 反射公式 N-截断）；
ramanujan_ap_E_43（Weil 界，Deligne 无条件但 mathlib 无椭圆曲线理论）。
-/

namespace BSD.LSeries5_43

open BSD.LSeries5

noncomputable section

/-! ## 1. 局部因子（代数层） -/

/-- a_p(E)（43a1 的 Hecke 系数，素数处）：直接查乘性表 aE_raw_43（200 项，点计数生成）。
    关键值：a₂ = −2, a₃ = −2, a₅ = −4, a₇ = 0, a₁₁ = 3, a₁₃ = −5, a₁₇ = −3,
    a₁₉ = −2, a₂₉ = −6, a₃₁ = −1, a₃₇ = 0, a₄₁ = 5, a₄₃ = −1, a₄₇ = 4, a₅₃ = −5, a₅₉ = −12。 -/
def ap_E_43 (p : ℕ) : ℤ := aE_raw_43 p

/-- a_p(E) 抽样值（表核验，native_decide）。 -/
theorem ap_E_values_43 :
    ap_E_43 2 = -2 ∧ ap_E_43 3 = -2 ∧ ap_E_43 5 = -4 ∧ ap_E_43 7 = 0 ∧
    ap_E_43 11 = 3 ∧ ap_E_43 13 = -5 ∧ ap_E_43 17 = -3 ∧ ap_E_43 19 = -2 ∧
    ap_E_43 29 = -6 ∧ ap_E_43 31 = -1 ∧ ap_E_43 37 = 0 ∧ ap_E_43 41 = 5 ∧
    ap_E_43 43 = -1 ∧ ap_E_43 47 = 4 ∧ ap_E_43 53 = -5 ∧ ap_E_43 59 = -12 := by
  native_decide

/-- Ramanujan 界：|a_p(E)| ≤ 2√p（Weil 猜想 d = 1 / Deligne，无条件）。
    待证明：有限域点计数 + Hasse 界（mathlib 无椭圆曲线理论）。 -/
axiom ramanujan_ap_E_43 (p : ℕ) : |ap_E_43 p| ≤ 2 * Real.sqrt (p : ℝ)

/-- a_p(E⁵)：5 处加性（a = 0）；43 处乘性（a = +1，χ₅(43)·a₄₃(E) = (−1)(−1)）；
    好素 p ∤ 1075 取 a_p(E⁵) = χ₅(p)·a_p(E)。 -/
def ap5_43 (p : ℕ) : ℤ :=
  if p % 5 = 0 then 0
  else if p = 43 then 1
  else chi5 p * ap_E_43 p

/-- 5 处加性：a₅(E⁵) = 0。 -/
theorem ap5_43_additive_at_5 : ap5_43 5 = 0 := by
  norm_num [ap5_43]

/-- 43 处乘性：a₄₃(E⁵) = +1。 -/
theorem ap5_43_multiplicative_at_43 : ap5_43 43 = 1 := by
  norm_num [ap5_43]

/-- 抽检（好素）：a₂(E⁵) = χ₅(2)·a₂(E) = (−1)(−2) = 2。 -/
theorem ap5_43_sample_2 : ap5_43 2 = 2 := by
  norm_num [ap5_43, chi5, ap_E_values_43]

/-- 抽检（好素）：a₁₁(E⁵) = χ₅(11)·a₁₁(E) = 1·3 = 3。 -/
theorem ap5_43_sample_11 : ap5_43 11 = 3 := by
  norm_num [ap5_43, chi5, ap_E_values_43]

/-! ## 2. L 函数与反射公式（声明层） -/

/-- χ₅(43) = −1（43 ≡ 3 mod 5）。 -/
theorem chi5_neg_at_43 : chi5 43 = -1 := by
  norm_num [chi5]

/-- α = 2π/√1075 的 Lean 名。 -/
def alphaE5_43 : ℝ := 2 * Real.pi / Real.sqrt 1075

/-- α > 0.1915：√1075 < 32.79 与 π > 3.1415（0.1915·32.79 = 6.2793 < 6.283 < 2π）。 -/
theorem alpha_gt_1915 : (0.1915 : ℝ) < 2 * Real.pi / Real.sqrt 1075 := by
  have hsqrt : Real.sqrt 1075 < (32.79 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 32.79)]
    norm_num
  have h1 : (0.1915 : ℝ) * Real.sqrt 1075 < (0.1915 * 32.79 : ℝ) := by
    exact mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 0.1915)
  have h2 : (0.1915 * 32.79 : ℝ) < 2 * Real.pi := by
    have h3 : (0.1915 * 32.79 : ℝ) < 2 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 2))
  have h3' : (0.1915 : ℝ) * Real.sqrt 1075 < 2 * Real.pi := lt_trans h1 h2
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1075))]
  simpa [mul_comm] using h3'

/-- α < 0.1917：√1075 > 32.78 与 π < 3.1416（6.2832 < 0.1917·32.78 = 6.2839）。 -/
theorem alpha_lt_1917 : 2 * Real.pi / Real.sqrt 1075 < (0.1917 : ℝ) := by
  have hsqrt : (32.78 : ℝ) < Real.sqrt 1075 := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 32.78)).2 (by norm_num)
  have h1 : (2 : ℝ) * (3.1416 : ℝ) < (0.1917 : ℝ) * 32.78 := by norm_num
  have h2 : (2 : ℝ) * Real.pi ≤ (2 : ℝ) * (3.1416 : ℝ) := by
    exact mul_le_mul_of_nonneg_left Real.pi_lt_d4.le (by norm_num : (0 : ℝ) ≤ 2)
  have h2' : (2 : ℝ) * Real.pi < (0.1917 : ℝ) * 32.78 := lt_of_le_of_lt h2 h1
  have h3 : (0.1917 : ℝ) * 32.78 < (0.1917 : ℝ) * Real.sqrt 1075 := by
    exact mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 0.1917)
  have h3' : (2 : ℝ) * Real.pi < (0.1917 : ℝ) * Real.sqrt 1075 := lt_trans h2' h3
  rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1075))]
  simpa [mul_comm] using h3'

/-- e^(−α) > 0.8254：α < 0.1917（exp 单调）；e^(0.1917) ≤ Σ₈ + B < 1/0.8254
    （`Real.exp_bound` n = 8 上界）⟹ e^(−0.1917) = 1/e^(0.1917) > 0.8254。 -/
theorem exp_neg_alpha_gt_8254 : (0.8254 : ℝ) < Real.exp (-alphaE5_43) := by
  have hmono : Real.exp (-(0.1917 : ℝ)) ≤ Real.exp (-alphaE5_43) := by
    dsimp [alphaE5_43]
    exact Real.exp_le_exp_of_le (by linarith [alpha_lt_1917])
  have hrecip : (0.8254 : ℝ) < Real.exp (-(0.1917 : ℝ)) := by
    rw [Real.exp_neg]
    have hexp : Real.exp (0.1917 : ℝ) < (1 / (0.8254 : ℝ)) := by
      have hsum : (∑ m ∈ Finset.range 8, (0.1917 : ℝ) ^ m / (m.factorial : ℝ)) =
          (1 : ℝ) + 0.1917 + (0.1917 : ℝ) ^ 2 / 2 + (0.1917 : ℝ) ^ 3 / 6 +
            (0.1917 : ℝ) ^ 4 / 24 + (0.1917 : ℝ) ^ 5 / 120 + (0.1917 : ℝ) ^ 6 / 720 +
              (0.1917 : ℝ) ^ 7 / 5040 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        norm_num
      have hb := Real.exp_bound (x := 0.1917) (n := 8) (by norm_num : |(0.1917 : ℝ)| ≤ 1) (by norm_num : 0 < 8)
      have hd : Real.exp (0.1917 : ℝ) - (∑ m ∈ Finset.range 8, (0.1917 : ℝ) ^ m / (m.factorial : ℝ))
          ≤ (0.1917 : ℝ) ^ 8 * ((9 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
        have h1 : Real.exp (0.1917 : ℝ) - (∑ m ∈ Finset.range 8, (0.1917 : ℝ) ^ m / (m.factorial : ℝ))
            ≤ |(0.1917 : ℝ)| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) :=
          le_trans (le_abs_self _) hb
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 0.1917)] using h1
      have hle' : Real.exp (0.1917 : ℝ) ≤
          (∑ m ∈ Finset.range 8, (0.1917 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.1917 : ℝ) ^ 8 * ((9 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
        linarith
      have hpartU : (∑ m ∈ Finset.range 8, (0.1917 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.1917 : ℝ) ^ 8 * ((9 : ℝ) / ((Nat.factorial 8 : ℝ) * 8))
          < 1 / (0.8254 : ℝ) := by
        norm_num [hsum]
      exact lt_of_le_of_lt hle' hpartU
    have htmp : 1 / (1 / (0.8254 : ℝ)) < 1 / Real.exp (0.1917 : ℝ) := by
      exact one_div_lt_one_div_of_lt (Real.exp_pos (0.1917 : ℝ)) hexp
    simpa using htmp
  exact lt_of_lt_of_le hrecip hmono

/-- e^(−α) < 0.8258：α > 0.1915（exp 单调）；1/0.8258 < Σ₆ − B ≤ e^(0.1915)
    （`Real.exp_bound` n = 6 下界）⟹ e^(−0.1915) = 1/e^(0.1915) < 0.8258。 -/
theorem exp_neg_alpha_lt_8258 : Real.exp (-alphaE5_43) < (0.8258 : ℝ) := by
  have hmono : Real.exp (-alphaE5_43) ≤ Real.exp (-(0.1915 : ℝ)) := by
    dsimp [alphaE5_43]
    exact Real.exp_le_exp_of_le (by linarith [alpha_gt_1915])
  have hrecip : Real.exp (-(0.1915 : ℝ)) < (0.8258 : ℝ) := by
    rw [Real.exp_neg]
    have hexp : (1 / (0.8258 : ℝ)) < Real.exp (0.1915 : ℝ) := by
      have hsum : (∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ)) =
          (1 : ℝ) + 0.1915 + (0.1915 : ℝ) ^ 2 / 2 + (0.1915 : ℝ) ^ 3 / 6 +
            (0.1915 : ℝ) ^ 4 / 24 + (0.1915 : ℝ) ^ 5 / 120 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ]
        norm_num
      have hb := Real.exp_bound (x := 0.1915) (n := 6) (by norm_num : |(0.1915 : ℝ)| ≤ 1) (by norm_num : 0 < 6)
      have hd : (∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ))
          - Real.exp (0.1915 : ℝ) ≤ (0.1915 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        have hb' : |(∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ)) - Real.exp (0.1915 : ℝ)| ≤
            (0.1915 : ℝ) ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
          simpa [abs_sub_comm, abs_of_pos (by norm_num : (0 : ℝ) < 0.1915)] using hb
        have h1 : (∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ))
            - Real.exp (0.1915 : ℝ) ≤
            |(∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ)) - Real.exp (0.1915 : ℝ)| :=
          le_abs_self _
        exact le_trans h1 hb'
      have hle' : (∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ))
          - (0.1915 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6))
          ≤ Real.exp (0.1915 : ℝ) := by
        linarith
      have hpartL : (1 / (0.8258 : ℝ)) <
          (∑ m ∈ Finset.range 6, (0.1915 : ℝ) ^ m / (m.factorial : ℝ))
          - (0.1915 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        norm_num [hsum]
      exact lt_of_lt_of_le hpartL hle'
    have htmp : 1 / Real.exp (0.1915 : ℝ) < 1 / (1 / (0.8258 : ℝ)) := by
      exact one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (1 / (0.8258 : ℝ))) hexp
    simpa using htmp
  exact lt_of_le_of_lt hmono hrecip

/-- 任意 n 的幂界（正项底）：0.8254^(n+1) ≤ e^(−α(n+1))。 -/
theorem powE_any_43 (n : ℕ) : ((0.8254 : ℝ) ^ (n + 1)) ≤ Real.exp (-alphaE5_43 * (n + 1)) := by
  have hpow : ((0.8254 : ℝ) ^ (n + 1)) ≤ (Real.exp (-alphaE5_43)) ^ (n + 1) := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (0.8254 : ℝ)) exp_neg_alpha_gt_8254.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- 任意 n 的幂界（负项底）：e^(−α(n+1)) ≤ 0.8258^(n+1)。 -/
theorem powE'_any_43 (n : ℕ) : Real.exp (-alphaE5_43 * (n + 1)) ≤ ((0.8258 : ℝ) ^ (n + 1)) := by
  have hpow : (Real.exp (-alphaE5_43)) ^ (n + 1) ≤ ((0.8258 : ℝ) ^ (n + 1)) := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos (-alphaE5_43))) exp_neg_alpha_lt_8258.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- e^(−α·51) < 10⁻³：e^(−α·51) = (e^(−α))^51 ≤ 0.8258^51（幂界）且 0.8258^51 ≈ 5.8×10⁻⁵ < 10⁻³。 -/
theorem exp_neg_alpha_51_lt_43 : Real.exp (-alphaE5_43 * (51 : ℕ)) < (1 : ℝ) / 10 ^ 3 := by
  have hpow : (Real.exp (-alphaE5_43)) ^ 51 = Real.exp (-alphaE5_43 * (51 : ℕ)) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hle : (Real.exp (-alphaE5_43)) ^ 51 ≤ ((0.8258 : ℝ) ^ 51) := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos (-alphaE5_43))) exp_neg_alpha_lt_8258.le 51
  have hnum : ((0.8258 : ℝ) ^ 51) < (1 : ℝ) / 10 ^ 3 := by norm_num
  rw [← hpow]
  exact lt_of_le_of_lt hle hnum

/-! ## 3. 反射级数 -/

/-- aE5_43 wrapper：有限表（0..800，表外 0）。 -/
def aE5_43 (n : ℕ) : ℤ :=
  if n ≤ 800 then aE5_raw_43 n else 0

/-- |a_n(E⁵)| ≤ 2n：表核验（native_decide 801 项）+ 表外平凡。 -/
theorem coefficient_bound_aE5_43 (n : ℕ) : |(aE5_43 n : ℝ)| ≤ 2 * (n : ℝ) := by
  by_cases hn : n ≤ 800
  · have h := (by native_decide : ∀ m ∈ Finset.range 801, |(aE5_43 m : ℤ)| ≤ 2 * m)
    have hn' : n ∈ Finset.range 801 := by simp [Finset.mem_range] ; omega
    have hz : |(aE5_43 n : ℤ)| ≤ 2 * n := h n hn'
    exact_mod_cast hz
  · have hn' : 801 ≤ n := by omega
    rw [aE5_43]
    have hn'' : ¬ n ≤ 800 := by omega
    rw [if_neg hn'']
    norm_num

/-- 反射公式第 n 项：fE5_43 n = a_{n+1}(E⁵)/(n+1) · e^(−α·(n+1))。 -/
noncomputable def fE5_43 : ℕ → ℝ := fun n =>
  (aE5_43 (n + 1) : ℝ) / (n + 1) * Real.exp (-alphaE5_43 * (n + 1))

axiom Lambda_E5_43 (s : ℝ) : ℝ

noncomputable def L_E5_43 (s : ℝ) : ℝ :=
  ((2 * Real.pi / Real.sqrt (1075 : ℝ)) ^ s) / Real.Gamma s * Lambda_E5_43 s

/-- Dokchitser 反射公式 s = 1 的 N-截断等式（axiom，设计口径同 37 版）。 -/
axiom L_E5_series_split_43 (N : ℕ) :
  L_E5_43 1 = 2 * (∑ n ∈ Finset.range N, fE5_43 n) + 2 * ∑' n : ℕ, fE5_43 (n + N)

/-- 反射级数绝对收敛：|fE5_43 n| ≤ 2·e^(−α(n+1))（系数界 + 除法界），
    Σ 2·e^(−α(n+1)) 为几何级数（e^(−α) < 1，α > 0）。 -/
theorem summable_fE5_43 : Summable fE5_43 := by
  have hterm : ∀ n : ℕ, |fE5_43 n| ≤ 2 * Real.exp (-alphaE5_43 * ((n : ℝ) + 1)) := by
    intro n
    unfold fE5_43
    rw [abs_mul]
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) := by positivity
    have hdiv : |(aE5_43 (n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)| ≤ 2 := by
      rw [abs_div]
      rw [abs_of_nonneg hnn]
      have hc : |(aE5_43 (n + 1 : ℕ) : ℝ)| ≤ 2 * ((n : ℝ) + 1) := by
        exact_mod_cast coefficient_bound_aE5_43 (n + 1)
      calc
        |(aE5_43 (n + 1 : ℕ) : ℝ)| / ((n : ℝ) + 1)
            ≤ (2 * ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
              exact div_le_div_of_nonneg_right hc hnn
        _ = 2 := by
          have hx : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hx]
    have he : |Real.exp (-alphaE5_43 * ((n : ℝ) + 1))| = Real.exp (-alphaE5_43 * ((n : ℝ) + 1)) := by
      rw [abs_of_pos (Real.exp_pos _)]
    rw [he]
    exact mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le
  have halpha : (0 : ℝ) < alphaE5_43 := by
    dsimp [alphaE5_43]
    positivity
  have hg : Summable (fun n : ℕ => (Real.exp (-alphaE5_43)) ^ n) := by
    refine summable_geometric_of_norm_lt_one ?_
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr halpha))
  have hg2 : Summable (fun n : ℕ => 2 * Real.exp (-alphaE5_43 * ((n : ℝ) + 1))) := by
    have hpoint : (fun n : ℕ => 2 * Real.exp (-alphaE5_43 * ((n : ℝ) + 1)))
        = (fun n : ℕ => (2 * Real.exp (-alphaE5_43)) * Real.exp (-alphaE5_43) ^ n) := by
      funext n
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      rw [show -alphaE5_43 * ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) * -alphaE5_43 by
        rw [hcast]
        ring]
      rw [Real.exp_nat_mul]
      rw [pow_succ]
      ring
    rw [hpoint]
    exact hg.mul_left (2 * Real.exp (-alphaE5_43))
  refine Summable.of_norm_bounded hg2 ?_
  intro n
  simpa [Real.norm_eq_abs] using hterm n

/-! ## 4. 部分和（crude 逐项下界） -/

/-- 逐项下界引理（i = 1..50；正系数项底 0.8254、负系数项底 0.8258、零项平凡）。 -/
theorem term_1_43 : ((1 : ℝ) / 1 * ((0.8254 : ℝ) ^ 1)) ≤ fE5_43 0 := by
  have heq : (1 : ℤ) = aE5_43 1 := by native_decide
  have hcast : (1 : ℝ) = (aE5_43 1 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (1 : ℝ) / 1 := by norm_num
  have hpow := powE_any_43 0
  have hpow2 : (0.8254 : ℝ) ^ 1 ≤ Real.exp (-alphaE5_43 * (1 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (1 : ℝ) / 1 * ((0.8254 : ℝ) ^ 1) ≤ (1 : ℝ) / 1 * Real.exp (-alphaE5_43 * (1 : ℝ)) := hm
    _ = (aE5_43 1 : ℝ) / 1 * Real.exp (-alphaE5_43 * (1 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 0 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_2_43 : ((2 : ℝ) / 2 * ((0.8254 : ℝ) ^ 2)) ≤ fE5_43 1 := by
  have heq : (2 : ℤ) = aE5_43 2 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 2 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 2 := by norm_num
  have hpow := powE_any_43 1
  have hpow2 : (0.8254 : ℝ) ^ 2 ≤ Real.exp (-alphaE5_43 * (2 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 2 * ((0.8254 : ℝ) ^ 2) ≤ (2 : ℝ) / 2 * Real.exp (-alphaE5_43 * (2 : ℝ)) := hm
    _ = (aE5_43 2 : ℝ) / 2 * Real.exp (-alphaE5_43 * (2 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 1 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_3_43 : ((2 : ℝ) / 3 * ((0.8254 : ℝ) ^ 3)) ≤ fE5_43 2 := by
  have heq : (2 : ℤ) = aE5_43 3 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 3 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 3 := by norm_num
  have hpow := powE_any_43 2
  have hpow2 : (0.8254 : ℝ) ^ 3 ≤ Real.exp (-alphaE5_43 * (3 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 3 * ((0.8254 : ℝ) ^ 3) ≤ (2 : ℝ) / 3 * Real.exp (-alphaE5_43 * (3 : ℝ)) := hm
    _ = (aE5_43 3 : ℝ) / 3 * Real.exp (-alphaE5_43 * (3 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 2 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_4_43 : ((2 : ℝ) / 4 * ((0.8254 : ℝ) ^ 4)) ≤ fE5_43 3 := by
  have heq : (2 : ℤ) = aE5_43 4 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 4 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 4 := by norm_num
  have hpow := powE_any_43 3
  have hpow2 : (0.8254 : ℝ) ^ 4 ≤ Real.exp (-alphaE5_43 * (4 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 4 * ((0.8254 : ℝ) ^ 4) ≤ (2 : ℝ) / 4 * Real.exp (-alphaE5_43 * (4 : ℝ)) := hm
    _ = (aE5_43 4 : ℝ) / 4 * Real.exp (-alphaE5_43 * (4 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 3 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_5_43 : ((0 : ℝ) / 5 * ((0.8254 : ℝ) ^ 5)) ≤ fE5_43 4 := by
  have hz : aE5_43 5 = 0 := by native_decide
  have hzr : (aE5_43 5 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 5 * ((0.8254 : ℝ) ^ 5) = 0 := by norm_num
    _ ≤ fE5_43 4 := by
      rw [show fE5_43 4 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_6_43 : ((4 : ℝ) / 6 * ((0.8254 : ℝ) ^ 6)) ≤ fE5_43 5 := by
  have heq : (4 : ℤ) = aE5_43 6 := by native_decide
  have hcast : (4 : ℝ) = (aE5_43 6 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (4 : ℝ) / 6 := by norm_num
  have hpow := powE_any_43 5
  have hpow2 : (0.8254 : ℝ) ^ 6 ≤ Real.exp (-alphaE5_43 * (6 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (4 : ℝ) / 6 * ((0.8254 : ℝ) ^ 6) ≤ (4 : ℝ) / 6 * Real.exp (-alphaE5_43 * (6 : ℝ)) := hm
    _ = (aE5_43 6 : ℝ) / 6 * Real.exp (-alphaE5_43 * (6 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 5 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_7_43 : ((0 : ℝ) / 7 * ((0.8254 : ℝ) ^ 7)) ≤ fE5_43 6 := by
  have hz : aE5_43 7 = 0 := by native_decide
  have hzr : (aE5_43 7 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 7 * ((0.8254 : ℝ) ^ 7) = 0 := by norm_num
    _ ≤ fE5_43 6 := by
      rw [show fE5_43 6 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_8_43 : ((0 : ℝ) / 8 * ((0.8254 : ℝ) ^ 8)) ≤ fE5_43 7 := by
  have hz : aE5_43 8 = 0 := by native_decide
  have hzr : (aE5_43 8 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 8 * ((0.8254 : ℝ) ^ 8) = 0 := by norm_num
    _ ≤ fE5_43 7 := by
      rw [show fE5_43 7 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_9_43 : ((1 : ℝ) / 9 * ((0.8254 : ℝ) ^ 9)) ≤ fE5_43 8 := by
  have heq : (1 : ℤ) = aE5_43 9 := by native_decide
  have hcast : (1 : ℝ) = (aE5_43 9 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (1 : ℝ) / 9 := by norm_num
  have hpow := powE_any_43 8
  have hpow2 : (0.8254 : ℝ) ^ 9 ≤ Real.exp (-alphaE5_43 * (9 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (1 : ℝ) / 9 * ((0.8254 : ℝ) ^ 9) ≤ (1 : ℝ) / 9 * Real.exp (-alphaE5_43 * (9 : ℝ)) := hm
    _ = (aE5_43 9 : ℝ) / 9 * Real.exp (-alphaE5_43 * (9 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 8 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_10_43 : ((0 : ℝ) / 10 * ((0.8254 : ℝ) ^ 10)) ≤ fE5_43 9 := by
  have hz : aE5_43 10 = 0 := by native_decide
  have hzr : (aE5_43 10 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 10 * ((0.8254 : ℝ) ^ 10) = 0 := by norm_num
    _ ≤ fE5_43 9 := by
      rw [show fE5_43 9 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_11_43 : ((3 : ℝ) / 11 * ((0.8254 : ℝ) ^ 11)) ≤ fE5_43 10 := by
  have heq : (3 : ℤ) = aE5_43 11 := by native_decide
  have hcast : (3 : ℝ) = (aE5_43 11 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (3 : ℝ) / 11 := by norm_num
  have hpow := powE_any_43 10
  have hpow2 : (0.8254 : ℝ) ^ 11 ≤ Real.exp (-alphaE5_43 * (11 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (3 : ℝ) / 11 * ((0.8254 : ℝ) ^ 11) ≤ (3 : ℝ) / 11 * Real.exp (-alphaE5_43 * (11 : ℝ)) := hm
    _ = (aE5_43 11 : ℝ) / 11 * Real.exp (-alphaE5_43 * (11 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 10 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_12_43 : ((4 : ℝ) / 12 * ((0.8254 : ℝ) ^ 12)) ≤ fE5_43 11 := by
  have heq : (4 : ℤ) = aE5_43 12 := by native_decide
  have hcast : (4 : ℝ) = (aE5_43 12 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (4 : ℝ) / 12 := by norm_num
  have hpow := powE_any_43 11
  have hpow2 : (0.8254 : ℝ) ^ 12 ≤ Real.exp (-alphaE5_43 * (12 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (4 : ℝ) / 12 * ((0.8254 : ℝ) ^ 12) ≤ (4 : ℝ) / 12 * Real.exp (-alphaE5_43 * (12 : ℝ)) := hm
    _ = (aE5_43 12 : ℝ) / 12 * Real.exp (-alphaE5_43 * (12 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 11 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_13_43 : ((5 : ℝ) / 13 * ((0.8254 : ℝ) ^ 13)) ≤ fE5_43 12 := by
  have heq : (5 : ℤ) = aE5_43 13 := by native_decide
  have hcast : (5 : ℝ) = (aE5_43 13 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (5 : ℝ) / 13 := by norm_num
  have hpow := powE_any_43 12
  have hpow2 : (0.8254 : ℝ) ^ 13 ≤ Real.exp (-alphaE5_43 * (13 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (5 : ℝ) / 13 * ((0.8254 : ℝ) ^ 13) ≤ (5 : ℝ) / 13 * Real.exp (-alphaE5_43 * (13 : ℝ)) := hm
    _ = (aE5_43 13 : ℝ) / 13 * Real.exp (-alphaE5_43 * (13 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 12 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_14_43 : ((0 : ℝ) / 14 * ((0.8254 : ℝ) ^ 14)) ≤ fE5_43 13 := by
  have hz : aE5_43 14 = 0 := by native_decide
  have hzr : (aE5_43 14 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 14 * ((0.8254 : ℝ) ^ 14) = 0 := by norm_num
    _ ≤ fE5_43 13 := by
      rw [show fE5_43 13 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_15_43 : ((0 : ℝ) / 15 * ((0.8254 : ℝ) ^ 15)) ≤ fE5_43 14 := by
  have hz : aE5_43 15 = 0 := by native_decide
  have hzr : (aE5_43 15 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 15 * ((0.8254 : ℝ) ^ 15) = 0 := by norm_num
    _ ≤ fE5_43 14 := by
      rw [show fE5_43 14 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_16_43 : ((-4 : ℝ) / 16 * ((0.8258 : ℝ) ^ 16)) ≤ fE5_43 15 := by
  have heq : (-4 : ℤ) = aE5_43 16 := by native_decide
  have hcast : (-4 : ℝ) = (aE5_43 16 : ℝ) := by exact_mod_cast heq
  have hcoef : (-4 : ℝ) / 16 ≤ 0 := by norm_num
  have hpow := powE'_any_43 15
  have hpow2 : Real.exp (-alphaE5_43 * (16 : ℝ)) ≤ (0.8258 : ℝ) ^ 16 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-4 : ℝ) / 16 * ((0.8258 : ℝ) ^ 16) ≤ (-4 : ℝ) / 16 * Real.exp (-alphaE5_43 * (16 : ℝ)) := hm
    _ = (aE5_43 16 : ℝ) / 16 * Real.exp (-alphaE5_43 * (16 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 15 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_17_43 : ((3 : ℝ) / 17 * ((0.8254 : ℝ) ^ 17)) ≤ fE5_43 16 := by
  have heq : (3 : ℤ) = aE5_43 17 := by native_decide
  have hcast : (3 : ℝ) = (aE5_43 17 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (3 : ℝ) / 17 := by norm_num
  have hpow := powE_any_43 16
  have hpow2 : (0.8254 : ℝ) ^ 17 ≤ Real.exp (-alphaE5_43 * (17 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (3 : ℝ) / 17 * ((0.8254 : ℝ) ^ 17) ≤ (3 : ℝ) / 17 * Real.exp (-alphaE5_43 * (17 : ℝ)) := hm
    _ = (aE5_43 17 : ℝ) / 17 * Real.exp (-alphaE5_43 * (17 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 16 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_18_43 : ((2 : ℝ) / 18 * ((0.8254 : ℝ) ^ 18)) ≤ fE5_43 17 := by
  have heq : (2 : ℤ) = aE5_43 18 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 18 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 18 := by norm_num
  have hpow := powE_any_43 17
  have hpow2 : (0.8254 : ℝ) ^ 18 ≤ Real.exp (-alphaE5_43 * (18 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 18 * ((0.8254 : ℝ) ^ 18) ≤ (2 : ℝ) / 18 * Real.exp (-alphaE5_43 * (18 : ℝ)) := hm
    _ = (aE5_43 18 : ℝ) / 18 * Real.exp (-alphaE5_43 * (18 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 17 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_19_43 : ((-2 : ℝ) / 19 * ((0.8258 : ℝ) ^ 19)) ≤ fE5_43 18 := by
  have heq : (-2 : ℤ) = aE5_43 19 := by native_decide
  have hcast : (-2 : ℝ) = (aE5_43 19 : ℝ) := by exact_mod_cast heq
  have hcoef : (-2 : ℝ) / 19 ≤ 0 := by norm_num
  have hpow := powE'_any_43 18
  have hpow2 : Real.exp (-alphaE5_43 * (19 : ℝ)) ≤ (0.8258 : ℝ) ^ 19 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-2 : ℝ) / 19 * ((0.8258 : ℝ) ^ 19) ≤ (-2 : ℝ) / 19 * Real.exp (-alphaE5_43 * (19 : ℝ)) := hm
    _ = (aE5_43 19 : ℝ) / 19 * Real.exp (-alphaE5_43 * (19 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 18 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_20_43 : ((0 : ℝ) / 20 * ((0.8254 : ℝ) ^ 20)) ≤ fE5_43 19 := by
  have hz : aE5_43 20 = 0 := by native_decide
  have hzr : (aE5_43 20 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 20 * ((0.8254 : ℝ) ^ 20) = 0 := by norm_num
    _ ≤ fE5_43 19 := by
      rw [show fE5_43 19 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_21_43 : ((0 : ℝ) / 21 * ((0.8254 : ℝ) ^ 21)) ≤ fE5_43 20 := by
  have hz : aE5_43 21 = 0 := by native_decide
  have hzr : (aE5_43 21 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 21 * ((0.8254 : ℝ) ^ 21) = 0 := by norm_num
    _ ≤ fE5_43 20 := by
      rw [show fE5_43 20 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_22_43 : ((6 : ℝ) / 22 * ((0.8254 : ℝ) ^ 22)) ≤ fE5_43 21 := by
  have heq : (6 : ℤ) = aE5_43 22 := by native_decide
  have hcast : (6 : ℝ) = (aE5_43 22 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (6 : ℝ) / 22 := by norm_num
  have hpow := powE_any_43 21
  have hpow2 : (0.8254 : ℝ) ^ 22 ≤ Real.exp (-alphaE5_43 * (22 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (6 : ℝ) / 22 * ((0.8254 : ℝ) ^ 22) ≤ (6 : ℝ) / 22 * Real.exp (-alphaE5_43 * (22 : ℝ)) := hm
    _ = (aE5_43 22 : ℝ) / 22 * Real.exp (-alphaE5_43 * (22 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 21 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_23_43 : ((1 : ℝ) / 23 * ((0.8254 : ℝ) ^ 23)) ≤ fE5_43 22 := by
  have heq : (1 : ℤ) = aE5_43 23 := by native_decide
  have hcast : (1 : ℝ) = (aE5_43 23 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (1 : ℝ) / 23 := by norm_num
  have hpow := powE_any_43 22
  have hpow2 : (0.8254 : ℝ) ^ 23 ≤ Real.exp (-alphaE5_43 * (23 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (1 : ℝ) / 23 * ((0.8254 : ℝ) ^ 23) ≤ (1 : ℝ) / 23 * Real.exp (-alphaE5_43 * (23 : ℝ)) := hm
    _ = (aE5_43 23 : ℝ) / 23 * Real.exp (-alphaE5_43 * (23 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 22 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_24_43 : ((0 : ℝ) / 24 * ((0.8254 : ℝ) ^ 24)) ≤ fE5_43 23 := by
  have hz : aE5_43 24 = 0 := by native_decide
  have hzr : (aE5_43 24 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 24 * ((0.8254 : ℝ) ^ 24) = 0 := by norm_num
    _ ≤ fE5_43 23 := by
      rw [show fE5_43 23 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_25_43 : ((0 : ℝ) / 25 * ((0.8254 : ℝ) ^ 25)) ≤ fE5_43 24 := by
  have hz : aE5_43 25 = 0 := by native_decide
  have hzr : (aE5_43 25 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 25 * ((0.8254 : ℝ) ^ 25) = 0 := by norm_num
    _ ≤ fE5_43 24 := by
      rw [show fE5_43 24 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_26_43 : ((10 : ℝ) / 26 * ((0.8254 : ℝ) ^ 26)) ≤ fE5_43 25 := by
  have heq : (10 : ℤ) = aE5_43 26 := by native_decide
  have hcast : (10 : ℝ) = (aE5_43 26 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (10 : ℝ) / 26 := by norm_num
  have hpow := powE_any_43 25
  have hpow2 : (0.8254 : ℝ) ^ 26 ≤ Real.exp (-alphaE5_43 * (26 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (10 : ℝ) / 26 * ((0.8254 : ℝ) ^ 26) ≤ (10 : ℝ) / 26 * Real.exp (-alphaE5_43 * (26 : ℝ)) := hm
    _ = (aE5_43 26 : ℝ) / 26 * Real.exp (-alphaE5_43 * (26 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 25 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_27_43 : ((-4 : ℝ) / 27 * ((0.8258 : ℝ) ^ 27)) ≤ fE5_43 26 := by
  have heq : (-4 : ℤ) = aE5_43 27 := by native_decide
  have hcast : (-4 : ℝ) = (aE5_43 27 : ℝ) := by exact_mod_cast heq
  have hcoef : (-4 : ℝ) / 27 ≤ 0 := by norm_num
  have hpow := powE'_any_43 26
  have hpow2 : Real.exp (-alphaE5_43 * (27 : ℝ)) ≤ (0.8258 : ℝ) ^ 27 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-4 : ℝ) / 27 * ((0.8258 : ℝ) ^ 27) ≤ (-4 : ℝ) / 27 * Real.exp (-alphaE5_43 * (27 : ℝ)) := hm
    _ = (aE5_43 27 : ℝ) / 27 * Real.exp (-alphaE5_43 * (27 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 26 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_28_43 : ((0 : ℝ) / 28 * ((0.8254 : ℝ) ^ 28)) ≤ fE5_43 27 := by
  have hz : aE5_43 28 = 0 := by native_decide
  have hzr : (aE5_43 28 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 28 * ((0.8254 : ℝ) ^ 28) = 0 := by norm_num
    _ ≤ fE5_43 27 := by
      rw [show fE5_43 27 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_29_43 : ((-6 : ℝ) / 29 * ((0.8258 : ℝ) ^ 29)) ≤ fE5_43 28 := by
  have heq : (-6 : ℤ) = aE5_43 29 := by native_decide
  have hcast : (-6 : ℝ) = (aE5_43 29 : ℝ) := by exact_mod_cast heq
  have hcoef : (-6 : ℝ) / 29 ≤ 0 := by norm_num
  have hpow := powE'_any_43 28
  have hpow2 : Real.exp (-alphaE5_43 * (29 : ℝ)) ≤ (0.8258 : ℝ) ^ 29 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-6 : ℝ) / 29 * ((0.8258 : ℝ) ^ 29) ≤ (-6 : ℝ) / 29 * Real.exp (-alphaE5_43 * (29 : ℝ)) := hm
    _ = (aE5_43 29 : ℝ) / 29 * Real.exp (-alphaE5_43 * (29 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 28 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_30_43 : ((0 : ℝ) / 30 * ((0.8254 : ℝ) ^ 30)) ≤ fE5_43 29 := by
  have hz : aE5_43 30 = 0 := by native_decide
  have hzr : (aE5_43 30 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 30 * ((0.8254 : ℝ) ^ 30) = 0 := by norm_num
    _ ≤ fE5_43 29 := by
      rw [show fE5_43 29 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_31_43 : ((-1 : ℝ) / 31 * ((0.8258 : ℝ) ^ 31)) ≤ fE5_43 30 := by
  have heq : (-1 : ℤ) = aE5_43 31 := by native_decide
  have hcast : (-1 : ℝ) = (aE5_43 31 : ℝ) := by exact_mod_cast heq
  have hcoef : (-1 : ℝ) / 31 ≤ 0 := by norm_num
  have hpow := powE'_any_43 30
  have hpow2 : Real.exp (-alphaE5_43 * (31 : ℝ)) ≤ (0.8258 : ℝ) ^ 31 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-1 : ℝ) / 31 * ((0.8258 : ℝ) ^ 31) ≤ (-1 : ℝ) / 31 * Real.exp (-alphaE5_43 * (31 : ℝ)) := hm
    _ = (aE5_43 31 : ℝ) / 31 * Real.exp (-alphaE5_43 * (31 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 30 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_32_43 : ((-8 : ℝ) / 32 * ((0.8258 : ℝ) ^ 32)) ≤ fE5_43 31 := by
  have heq : (-8 : ℤ) = aE5_43 32 := by native_decide
  have hcast : (-8 : ℝ) = (aE5_43 32 : ℝ) := by exact_mod_cast heq
  have hcoef : (-8 : ℝ) / 32 ≤ 0 := by norm_num
  have hpow := powE'_any_43 31
  have hpow2 : Real.exp (-alphaE5_43 * (32 : ℝ)) ≤ (0.8258 : ℝ) ^ 32 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-8 : ℝ) / 32 * ((0.8258 : ℝ) ^ 32) ≤ (-8 : ℝ) / 32 * Real.exp (-alphaE5_43 * (32 : ℝ)) := hm
    _ = (aE5_43 32 : ℝ) / 32 * Real.exp (-alphaE5_43 * (32 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 31 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_33_43 : ((6 : ℝ) / 33 * ((0.8254 : ℝ) ^ 33)) ≤ fE5_43 32 := by
  have heq : (6 : ℤ) = aE5_43 33 := by native_decide
  have hcast : (6 : ℝ) = (aE5_43 33 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (6 : ℝ) / 33 := by norm_num
  have hpow := powE_any_43 32
  have hpow2 : (0.8254 : ℝ) ^ 33 ≤ Real.exp (-alphaE5_43 * (33 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (6 : ℝ) / 33 * ((0.8254 : ℝ) ^ 33) ≤ (6 : ℝ) / 33 * Real.exp (-alphaE5_43 * (33 : ℝ)) := hm
    _ = (aE5_43 33 : ℝ) / 33 * Real.exp (-alphaE5_43 * (33 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 32 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_34_43 : ((6 : ℝ) / 34 * ((0.8254 : ℝ) ^ 34)) ≤ fE5_43 33 := by
  have heq : (6 : ℤ) = aE5_43 34 := by native_decide
  have hcast : (6 : ℝ) = (aE5_43 34 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (6 : ℝ) / 34 := by norm_num
  have hpow := powE_any_43 33
  have hpow2 : (0.8254 : ℝ) ^ 34 ≤ Real.exp (-alphaE5_43 * (34 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (6 : ℝ) / 34 * ((0.8254 : ℝ) ^ 34) ≤ (6 : ℝ) / 34 * Real.exp (-alphaE5_43 * (34 : ℝ)) := hm
    _ = (aE5_43 34 : ℝ) / 34 * Real.exp (-alphaE5_43 * (34 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 33 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_35_43 : ((0 : ℝ) / 35 * ((0.8254 : ℝ) ^ 35)) ≤ fE5_43 34 := by
  have hz : aE5_43 35 = 0 := by native_decide
  have hzr : (aE5_43 35 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 35 * ((0.8254 : ℝ) ^ 35) = 0 := by norm_num
    _ ≤ fE5_43 34 := by
      rw [show fE5_43 34 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_36_43 : ((2 : ℝ) / 36 * ((0.8254 : ℝ) ^ 36)) ≤ fE5_43 35 := by
  have heq : (2 : ℤ) = aE5_43 36 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 36 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 36 := by norm_num
  have hpow := powE_any_43 35
  have hpow2 : (0.8254 : ℝ) ^ 36 ≤ Real.exp (-alphaE5_43 * (36 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 36 * ((0.8254 : ℝ) ^ 36) ≤ (2 : ℝ) / 36 * Real.exp (-alphaE5_43 * (36 : ℝ)) := hm
    _ = (aE5_43 36 : ℝ) / 36 * Real.exp (-alphaE5_43 * (36 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 35 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_37_43 : ((0 : ℝ) / 37 * ((0.8254 : ℝ) ^ 37)) ≤ fE5_43 36 := by
  have hz : aE5_43 37 = 0 := by native_decide
  have hzr : (aE5_43 37 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 37 * ((0.8254 : ℝ) ^ 37) = 0 := by norm_num
    _ ≤ fE5_43 36 := by
      rw [show fE5_43 36 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_38_43 : ((-4 : ℝ) / 38 * ((0.8258 : ℝ) ^ 38)) ≤ fE5_43 37 := by
  have heq : (-4 : ℤ) = aE5_43 38 := by native_decide
  have hcast : (-4 : ℝ) = (aE5_43 38 : ℝ) := by exact_mod_cast heq
  have hcoef : (-4 : ℝ) / 38 ≤ 0 := by norm_num
  have hpow := powE'_any_43 37
  have hpow2 : Real.exp (-alphaE5_43 * (38 : ℝ)) ≤ (0.8258 : ℝ) ^ 38 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-4 : ℝ) / 38 * ((0.8258 : ℝ) ^ 38) ≤ (-4 : ℝ) / 38 * Real.exp (-alphaE5_43 * (38 : ℝ)) := hm
    _ = (aE5_43 38 : ℝ) / 38 * Real.exp (-alphaE5_43 * (38 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 37 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_39_43 : ((10 : ℝ) / 39 * ((0.8254 : ℝ) ^ 39)) ≤ fE5_43 38 := by
  have heq : (10 : ℤ) = aE5_43 39 := by native_decide
  have hcast : (10 : ℝ) = (aE5_43 39 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (10 : ℝ) / 39 := by norm_num
  have hpow := powE_any_43 38
  have hpow2 : (0.8254 : ℝ) ^ 39 ≤ Real.exp (-alphaE5_43 * (39 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (10 : ℝ) / 39 * ((0.8254 : ℝ) ^ 39) ≤ (10 : ℝ) / 39 * Real.exp (-alphaE5_43 * (39 : ℝ)) := hm
    _ = (aE5_43 39 : ℝ) / 39 * Real.exp (-alphaE5_43 * (39 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 38 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_40_43 : ((0 : ℝ) / 40 * ((0.8254 : ℝ) ^ 40)) ≤ fE5_43 39 := by
  have hz : aE5_43 40 = 0 := by native_decide
  have hzr : (aE5_43 40 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 40 * ((0.8254 : ℝ) ^ 40) = 0 := by norm_num
    _ ≤ fE5_43 39 := by
      rw [show fE5_43 39 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_41_43 : ((5 : ℝ) / 41 * ((0.8254 : ℝ) ^ 41)) ≤ fE5_43 40 := by
  have heq : (5 : ℤ) = aE5_43 41 := by native_decide
  have hcast : (5 : ℝ) = (aE5_43 41 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (5 : ℝ) / 41 := by norm_num
  have hpow := powE_any_43 40
  have hpow2 : (0.8254 : ℝ) ^ 41 ≤ Real.exp (-alphaE5_43 * (41 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (5 : ℝ) / 41 * ((0.8254 : ℝ) ^ 41) ≤ (5 : ℝ) / 41 * Real.exp (-alphaE5_43 * (41 : ℝ)) := hm
    _ = (aE5_43 41 : ℝ) / 41 * Real.exp (-alphaE5_43 * (41 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 40 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_42_43 : ((0 : ℝ) / 42 * ((0.8254 : ℝ) ^ 42)) ≤ fE5_43 41 := by
  have hz : aE5_43 42 = 0 := by native_decide
  have hzr : (aE5_43 42 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 42 * ((0.8254 : ℝ) ^ 42) = 0 := by norm_num
    _ ≤ fE5_43 41 := by
      rw [show fE5_43 41 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_43_43 : ((1 : ℝ) / 43 * ((0.8254 : ℝ) ^ 43)) ≤ fE5_43 42 := by
  have heq : (1 : ℤ) = aE5_43 43 := by native_decide
  have hcast : (1 : ℝ) = (aE5_43 43 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (1 : ℝ) / 43 := by norm_num
  have hpow := powE_any_43 42
  have hpow2 : (0.8254 : ℝ) ^ 43 ≤ Real.exp (-alphaE5_43 * (43 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (1 : ℝ) / 43 * ((0.8254 : ℝ) ^ 43) ≤ (1 : ℝ) / 43 * Real.exp (-alphaE5_43 * (43 : ℝ)) := hm
    _ = (aE5_43 43 : ℝ) / 43 * Real.exp (-alphaE5_43 * (43 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 42 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_44_43 : ((6 : ℝ) / 44 * ((0.8254 : ℝ) ^ 44)) ≤ fE5_43 43 := by
  have heq : (6 : ℤ) = aE5_43 44 := by native_decide
  have hcast : (6 : ℝ) = (aE5_43 44 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (6 : ℝ) / 44 := by norm_num
  have hpow := powE_any_43 43
  have hpow2 : (0.8254 : ℝ) ^ 44 ≤ Real.exp (-alphaE5_43 * (44 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (6 : ℝ) / 44 * ((0.8254 : ℝ) ^ 44) ≤ (6 : ℝ) / 44 * Real.exp (-alphaE5_43 * (44 : ℝ)) := hm
    _ = (aE5_43 44 : ℝ) / 44 * Real.exp (-alphaE5_43 * (44 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 43 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_45_43 : ((0 : ℝ) / 45 * ((0.8254 : ℝ) ^ 45)) ≤ fE5_43 44 := by
  have hz : aE5_43 45 = 0 := by native_decide
  have hzr : (aE5_43 45 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 45 * ((0.8254 : ℝ) ^ 45) = 0 := by norm_num
    _ ≤ fE5_43 44 := by
      rw [show fE5_43 44 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

theorem term_46_43 : ((2 : ℝ) / 46 * ((0.8254 : ℝ) ^ 46)) ≤ fE5_43 45 := by
  have heq : (2 : ℤ) = aE5_43 46 := by native_decide
  have hcast : (2 : ℝ) = (aE5_43 46 : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) / 46 := by norm_num
  have hpow := powE_any_43 45
  have hpow2 : (0.8254 : ℝ) ^ 46 ≤ Real.exp (-alphaE5_43 * (46 : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    (2 : ℝ) / 46 * ((0.8254 : ℝ) ^ 46) ≤ (2 : ℝ) / 46 * Real.exp (-alphaE5_43 * (46 : ℝ)) := hm
    _ = (aE5_43 46 : ℝ) / 46 * Real.exp (-alphaE5_43 * (46 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 45 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_47_43 : ((-4 : ℝ) / 47 * ((0.8258 : ℝ) ^ 47)) ≤ fE5_43 46 := by
  have heq : (-4 : ℤ) = aE5_43 47 := by native_decide
  have hcast : (-4 : ℝ) = (aE5_43 47 : ℝ) := by exact_mod_cast heq
  have hcoef : (-4 : ℝ) / 47 ≤ 0 := by norm_num
  have hpow := powE'_any_43 46
  have hpow2 : Real.exp (-alphaE5_43 * (47 : ℝ)) ≤ (0.8258 : ℝ) ^ 47 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-4 : ℝ) / 47 * ((0.8258 : ℝ) ^ 47) ≤ (-4 : ℝ) / 47 * Real.exp (-alphaE5_43 * (47 : ℝ)) := hm
    _ = (aE5_43 47 : ℝ) / 47 * Real.exp (-alphaE5_43 * (47 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 46 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_48_43 : ((-8 : ℝ) / 48 * ((0.8258 : ℝ) ^ 48)) ≤ fE5_43 47 := by
  have heq : (-8 : ℤ) = aE5_43 48 := by native_decide
  have hcast : (-8 : ℝ) = (aE5_43 48 : ℝ) := by exact_mod_cast heq
  have hcoef : (-8 : ℝ) / 48 ≤ 0 := by norm_num
  have hpow := powE'_any_43 47
  have hpow2 : Real.exp (-alphaE5_43 * (48 : ℝ)) ≤ (0.8258 : ℝ) ^ 48 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-8 : ℝ) / 48 * ((0.8258 : ℝ) ^ 48) ≤ (-8 : ℝ) / 48 * Real.exp (-alphaE5_43 * (48 : ℝ)) := hm
    _ = (aE5_43 48 : ℝ) / 48 * Real.exp (-alphaE5_43 * (48 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 47 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_49_43 : ((-7 : ℝ) / 49 * ((0.8258 : ℝ) ^ 49)) ≤ fE5_43 48 := by
  have heq : (-7 : ℤ) = aE5_43 49 := by native_decide
  have hcast : (-7 : ℝ) = (aE5_43 49 : ℝ) := by exact_mod_cast heq
  have hcoef : (-7 : ℝ) / 49 ≤ 0 := by norm_num
  have hpow := powE'_any_43 48
  have hpow2 : Real.exp (-alphaE5_43 * (49 : ℝ)) ≤ (0.8258 : ℝ) ^ 49 := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    (-7 : ℝ) / 49 * ((0.8258 : ℝ) ^ 49) ≤ (-7 : ℝ) / 49 * Real.exp (-alphaE5_43 * (49 : ℝ)) := hm
    _ = (aE5_43 49 : ℝ) / 49 * Real.exp (-alphaE5_43 * (49 : ℝ)) := by
      rw [hcast]
    _ = fE5_43 48 := by
      norm_num [fE5_43, alphaE5_43]

theorem term_50_43 : ((0 : ℝ) / 50 * ((0.8254 : ℝ) ^ 50)) ≤ fE5_43 49 := by
  have hz : aE5_43 50 = 0 := by native_decide
  have hzr : (aE5_43 50 : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / 50 * ((0.8254 : ℝ) ^ 50) = 0 := by norm_num
    _ ≤ fE5_43 49 := by
      rw [show fE5_43 49 = 0 by norm_num [fE5_43, alphaE5_43, hzr]]

/-- 粗界逐项函数（ℝ，数值化——aE5 值直接代入，符号驱动选底）。 -/
def crude_n_R_43 : ℕ → ℝ
  | 0 => (1 : ℝ) / 1 * ((0.8254 : ℝ) ^ 1)
  | 1 => (2 : ℝ) / 2 * ((0.8254 : ℝ) ^ 2)
  | 2 => (2 : ℝ) / 3 * ((0.8254 : ℝ) ^ 3)
  | 3 => (2 : ℝ) / 4 * ((0.8254 : ℝ) ^ 4)
  | 4 => (0 : ℝ) / 5 * ((0.8254 : ℝ) ^ 5)
  | 5 => (4 : ℝ) / 6 * ((0.8254 : ℝ) ^ 6)
  | 6 => (0 : ℝ) / 7 * ((0.8254 : ℝ) ^ 7)
  | 7 => (0 : ℝ) / 8 * ((0.8254 : ℝ) ^ 8)
  | 8 => (1 : ℝ) / 9 * ((0.8254 : ℝ) ^ 9)
  | 9 => (0 : ℝ) / 10 * ((0.8254 : ℝ) ^ 10)
  | 10 => (3 : ℝ) / 11 * ((0.8254 : ℝ) ^ 11)
  | 11 => (4 : ℝ) / 12 * ((0.8254 : ℝ) ^ 12)
  | 12 => (5 : ℝ) / 13 * ((0.8254 : ℝ) ^ 13)
  | 13 => (0 : ℝ) / 14 * ((0.8254 : ℝ) ^ 14)
  | 14 => (0 : ℝ) / 15 * ((0.8254 : ℝ) ^ 15)
  | 15 => (-4 : ℝ) / 16 * ((0.8258 : ℝ) ^ 16)
  | 16 => (3 : ℝ) / 17 * ((0.8254 : ℝ) ^ 17)
  | 17 => (2 : ℝ) / 18 * ((0.8254 : ℝ) ^ 18)
  | 18 => (-2 : ℝ) / 19 * ((0.8258 : ℝ) ^ 19)
  | 19 => (0 : ℝ) / 20 * ((0.8254 : ℝ) ^ 20)
  | 20 => (0 : ℝ) / 21 * ((0.8254 : ℝ) ^ 21)
  | 21 => (6 : ℝ) / 22 * ((0.8254 : ℝ) ^ 22)
  | 22 => (1 : ℝ) / 23 * ((0.8254 : ℝ) ^ 23)
  | 23 => (0 : ℝ) / 24 * ((0.8254 : ℝ) ^ 24)
  | 24 => (0 : ℝ) / 25 * ((0.8254 : ℝ) ^ 25)
  | 25 => (10 : ℝ) / 26 * ((0.8254 : ℝ) ^ 26)
  | 26 => (-4 : ℝ) / 27 * ((0.8258 : ℝ) ^ 27)
  | 27 => (0 : ℝ) / 28 * ((0.8254 : ℝ) ^ 28)
  | 28 => (-6 : ℝ) / 29 * ((0.8258 : ℝ) ^ 29)
  | 29 => (0 : ℝ) / 30 * ((0.8254 : ℝ) ^ 30)
  | 30 => (-1 : ℝ) / 31 * ((0.8258 : ℝ) ^ 31)
  | 31 => (-8 : ℝ) / 32 * ((0.8258 : ℝ) ^ 32)
  | 32 => (6 : ℝ) / 33 * ((0.8254 : ℝ) ^ 33)
  | 33 => (6 : ℝ) / 34 * ((0.8254 : ℝ) ^ 34)
  | 34 => (0 : ℝ) / 35 * ((0.8254 : ℝ) ^ 35)
  | 35 => (2 : ℝ) / 36 * ((0.8254 : ℝ) ^ 36)
  | 36 => (0 : ℝ) / 37 * ((0.8254 : ℝ) ^ 37)
  | 37 => (-4 : ℝ) / 38 * ((0.8258 : ℝ) ^ 38)
  | 38 => (10 : ℝ) / 39 * ((0.8254 : ℝ) ^ 39)
  | 39 => (0 : ℝ) / 40 * ((0.8254 : ℝ) ^ 40)
  | 40 => (5 : ℝ) / 41 * ((0.8254 : ℝ) ^ 41)
  | 41 => (0 : ℝ) / 42 * ((0.8254 : ℝ) ^ 42)
  | 42 => (1 : ℝ) / 43 * ((0.8254 : ℝ) ^ 43)
  | 43 => (6 : ℝ) / 44 * ((0.8254 : ℝ) ^ 44)
  | 44 => (0 : ℝ) / 45 * ((0.8254 : ℝ) ^ 45)
  | 45 => (2 : ℝ) / 46 * ((0.8254 : ℝ) ^ 46)
  | 46 => (-4 : ℝ) / 47 * ((0.8258 : ℝ) ^ 47)
  | 47 => (-8 : ℝ) / 48 * ((0.8258 : ℝ) ^ 48)
  | 48 => (-7 : ℝ) / 49 * ((0.8258 : ℝ) ^ 49)
  | 49 => (0 : ℝ) / 50 * ((0.8254 : ℝ) ^ 50)
  | _ => 0

/-- 部分和粗界（ℝ）：2.4 ≤ Σ_False crude_n_R_43 i。
    分块 ℚ 精确值 native_decide（纯数值）+ cast 桥 + linarith 拼和。
    块值（精确 ℚ）：块0 ≈ 2.3442182640436284，块1 ≈ 0.09392300233131758，
    块2 ≈ 0.005501631468829098，块3 ≈ 7.65e-5，块4 ≈ 4.89e-5；总和 ≈ 2.443918 > 2.4。 -/
theorem crude50_ge_R_43 : (2.4 : ℝ) ≤ ∑ i ∈ Finset.range 50, crude_n_R_43 i := by
  have hq0 : (41206961672641908238719569017113887/17578125000000000000000000000000000 : ℚ) ≤ ((((((((((1 : ℚ) / 1 * (((8254 : ℚ) / 10000) ^ 1) + ((2 : ℚ) / 2 * (((8254 : ℚ) / 10000) ^ 2))) + ((2 : ℚ) / 3 * (((8254 : ℚ) / 10000) ^ 3))) + ((2 : ℚ) / 4 * (((8254 : ℚ) / 10000) ^ 4))) + ((0 : ℚ) / 5 * (((8254 : ℚ) / 10000) ^ 5))) + ((4 : ℚ) / 6 * (((8254 : ℚ) / 10000) ^ 6))) + ((0 : ℚ) / 7 * (((8254 : ℚ) / 10000) ^ 7))) + ((0 : ℚ) / 8 * (((8254 : ℚ) / 10000) ^ 8))) + ((1 : ℚ) / 9 * (((8254 : ℚ) / 10000) ^ 9))) + ((0 : ℚ) / 10 * (((8254 : ℚ) / 10000) ^ 10))) := by
    native_decide
  have hq0' := (Rat.cast_le (K := ℝ)).mpr hq0
  norm_num at hq0'
  have hq1 : (372351512833891239401830664306905160105022595459693223424806784684830604349/3964433670043945312500000000000000000000000000000000000000000000000000000000 : ℚ) ≤ ((((((((((3 : ℚ) / 11 * (((8254 : ℚ) / 10000) ^ 11) + ((4 : ℚ) / 12 * (((8254 : ℚ) / 10000) ^ 12))) + ((5 : ℚ) / 13 * (((8254 : ℚ) / 10000) ^ 13))) + ((0 : ℚ) / 14 * (((8254 : ℚ) / 10000) ^ 14))) + ((0 : ℚ) / 15 * (((8254 : ℚ) / 10000) ^ 15))) + ((-4 : ℚ) / 16 * (((8258 : ℚ) / 10000) ^ 16))) + ((3 : ℚ) / 17 * (((8254 : ℚ) / 10000) ^ 17))) + ((2 : ℚ) / 18 * (((8254 : ℚ) / 10000) ^ 18))) + ((-2 : ℚ) / 19 * (((8258 : ℚ) / 10000) ^ 19))) + ((0 : ℚ) / 20 * (((8254 : ℚ) / 10000) ^ 20))) := by
    native_decide
  have hq1' := (Rat.cast_le (K := ℝ)).mpr hq1
  norm_num at hq1'
  have hq2 : (1319523900790742385291188368054433513120893395228110217807155330695661404610609026742764062230365526500493281079/239842291921377182006835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) ≤ ((((((((((0 : ℚ) / 21 * (((8254 : ℚ) / 10000) ^ 21) + ((6 : ℚ) / 22 * (((8254 : ℚ) / 10000) ^ 22))) + ((1 : ℚ) / 23 * (((8254 : ℚ) / 10000) ^ 23))) + ((0 : ℚ) / 24 * (((8254 : ℚ) / 10000) ^ 24))) + ((0 : ℚ) / 25 * (((8254 : ℚ) / 10000) ^ 25))) + ((10 : ℚ) / 26 * (((8254 : ℚ) / 10000) ^ 26))) + ((-4 : ℚ) / 27 * (((8258 : ℚ) / 10000) ^ 27))) + ((0 : ℚ) / 28 * (((8254 : ℚ) / 10000) ^ 28))) + ((-6 : ℚ) / 29 * (((8258 : ℚ) / 10000) ^ 29))) + ((0 : ℚ) / 30 * (((8254 : ℚ) / 10000) ^ 30))) := by
    native_decide
  have hq2' := (Rat.cast_le (K := ℝ)).mpr hq2
  norm_num at hq2'
  have hq3 : (179385317975353493136169439664042929108934119831702401311513439044263839182538769273083024528018549448258060666035995787969172550036593579225144827/2344082713534589856863021850585937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) ≤ ((((((((((-1 : ℚ) / 31 * (((8258 : ℚ) / 10000) ^ 31) + ((-8 : ℚ) / 32 * (((8258 : ℚ) / 10000) ^ 32))) + ((6 : ℚ) / 33 * (((8254 : ℚ) / 10000) ^ 33))) + ((6 : ℚ) / 34 * (((8254 : ℚ) / 10000) ^ 34))) + ((0 : ℚ) / 35 * (((8254 : ℚ) / 10000) ^ 35))) + ((2 : ℚ) / 36 * (((8254 : ℚ) / 10000) ^ 36))) + ((0 : ℚ) / 37 * (((8254 : ℚ) / 10000) ^ 37))) + ((-4 : ℚ) / 38 * (((8258 : ℚ) / 10000) ^ 38))) + ((10 : ℚ) / 39 * (((8254 : ℚ) / 10000) ^ 39))) + ((0 : ℚ) / 40 * (((8254 : ℚ) / 10000) ^ 40))) := by
    native_decide
  have hq3' := (Rat.cast_le (K := ℝ)).mpr hq3
  norm_num at hq3'
  have hq4 : (382104577778531503518413171515328826098383493832324855453151346843984013372511026384878894190012312616445683923528569497497221305842899382583525160737434845127693468859275283257231014969/7820242107214880888932384550571441650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) ≤ ((((((((((5 : ℚ) / 41 * (((8254 : ℚ) / 10000) ^ 41) + ((0 : ℚ) / 42 * (((8254 : ℚ) / 10000) ^ 42))) + ((1 : ℚ) / 43 * (((8254 : ℚ) / 10000) ^ 43))) + ((6 : ℚ) / 44 * (((8254 : ℚ) / 10000) ^ 44))) + ((0 : ℚ) / 45 * (((8254 : ℚ) / 10000) ^ 45))) + ((2 : ℚ) / 46 * (((8254 : ℚ) / 10000) ^ 46))) + ((-4 : ℚ) / 47 * (((8258 : ℚ) / 10000) ^ 47))) + ((-8 : ℚ) / 48 * (((8258 : ℚ) / 10000) ^ 48))) + ((-7 : ℚ) / 49 * (((8258 : ℚ) / 10000) ^ 49))) + ((0 : ℚ) / 50 * (((8254 : ℚ) / 10000) ^ 50))) := by
    native_decide
  have hq4' := (Rat.cast_le (K := ℝ)).mpr hq4
  norm_num at hq4'
  have hsum : (41206961672641908238719569017113887/17578125000000000000000000000000000 : ℝ) + (372351512833891239401830664306905160105022595459693223424806784684830604349/3964433670043945312500000000000000000000000000000000000000000000000000000000 : ℝ) + (1319523900790742385291188368054433513120893395228110217807155330695661404610609026742764062230365526500493281079/239842291921377182006835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      + (179385317975353493136169439664042929108934119831702401311513439044263839182538769273083024528018549448258060666035995787969172550036593579225144827/2344082713534589856863021850585937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + (382104577778531503518413171515328826098383493832324855453151346843984013372511026384878894190012312616445683923528569497497221305842899382583525160737434845127693468859275283257231014969/7820242107214880888932384550571441650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ ∑ i ∈ Finset.range 50, crude_n_R_43 i := by
    simp [Finset.sum_range_succ, crude_n_R_43]
    linarith
  have htot : (2.4 : ℝ) ≤ (41206961672641908238719569017113887/17578125000000000000000000000000000 : ℝ) + (372351512833891239401830664306905160105022595459693223424806784684830604349/3964433670043945312500000000000000000000000000000000000000000000000000000000 : ℝ) + (1319523900790742385291188368054433513120893395228110217807155330695661404610609026742764062230365526500493281079/239842291921377182006835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      + (179385317975353493136169439664042929108934119831702401311513439044263839182538769273083024528018549448258060666035995787969172550036593579225144827/2344082713534589856863021850585937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + (382104577778531503518413171515328826098383493832324855453151346843984013372511026384878894190012312616445683923528569497497221305842899382583525160737434845127693468859275283257231014969/7820242107214880888932384550571441650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    norm_num
  linarith

/-- 粗界 ≤ 真部分和（逐项 term_i + linarith）。 -/
theorem part50_ge_crude_43 :
    ∑ i ∈ Finset.range 50, crude_n_R_43 i ≤ ∑ n ∈ Finset.range 50, fE5_43 n := by
  simp [Finset.sum_range_succ, crude_n_R_43]
  have h0 : (1 : ℝ) / 1 * ((0.8254 : ℝ) ^ 1) ≤ fE5_43 0 := term_1_43
  have h1 : (2 : ℝ) / 2 * ((0.8254 : ℝ) ^ 2) ≤ fE5_43 1 := term_2_43
  have h2 : (2 : ℝ) / 3 * ((0.8254 : ℝ) ^ 3) ≤ fE5_43 2 := term_3_43
  have h3 : (2 : ℝ) / 4 * ((0.8254 : ℝ) ^ 4) ≤ fE5_43 3 := term_4_43
  have h4 : (0 : ℝ) / 5 * ((0.8254 : ℝ) ^ 5) ≤ fE5_43 4 := term_5_43
  have h5 : (4 : ℝ) / 6 * ((0.8254 : ℝ) ^ 6) ≤ fE5_43 5 := term_6_43
  have h6 : (0 : ℝ) / 7 * ((0.8254 : ℝ) ^ 7) ≤ fE5_43 6 := term_7_43
  have h7 : (0 : ℝ) / 8 * ((0.8254 : ℝ) ^ 8) ≤ fE5_43 7 := term_8_43
  have h8 : (1 : ℝ) / 9 * ((0.8254 : ℝ) ^ 9) ≤ fE5_43 8 := term_9_43
  have h9 : (0 : ℝ) / 10 * ((0.8254 : ℝ) ^ 10) ≤ fE5_43 9 := term_10_43
  have h10 : (3 : ℝ) / 11 * ((0.8254 : ℝ) ^ 11) ≤ fE5_43 10 := term_11_43
  have h11 : (4 : ℝ) / 12 * ((0.8254 : ℝ) ^ 12) ≤ fE5_43 11 := term_12_43
  have h12 : (5 : ℝ) / 13 * ((0.8254 : ℝ) ^ 13) ≤ fE5_43 12 := term_13_43
  have h13 : (0 : ℝ) / 14 * ((0.8254 : ℝ) ^ 14) ≤ fE5_43 13 := term_14_43
  have h14 : (0 : ℝ) / 15 * ((0.8254 : ℝ) ^ 15) ≤ fE5_43 14 := term_15_43
  have h15 : (-4 : ℝ) / 16 * ((0.8258 : ℝ) ^ 16) ≤ fE5_43 15 := term_16_43
  have h16 : (3 : ℝ) / 17 * ((0.8254 : ℝ) ^ 17) ≤ fE5_43 16 := term_17_43
  have h17 : (2 : ℝ) / 18 * ((0.8254 : ℝ) ^ 18) ≤ fE5_43 17 := term_18_43
  have h18 : (-2 : ℝ) / 19 * ((0.8258 : ℝ) ^ 19) ≤ fE5_43 18 := term_19_43
  have h19 : (0 : ℝ) / 20 * ((0.8254 : ℝ) ^ 20) ≤ fE5_43 19 := term_20_43
  have h20 : (0 : ℝ) / 21 * ((0.8254 : ℝ) ^ 21) ≤ fE5_43 20 := term_21_43
  have h21 : (6 : ℝ) / 22 * ((0.8254 : ℝ) ^ 22) ≤ fE5_43 21 := term_22_43
  have h22 : (1 : ℝ) / 23 * ((0.8254 : ℝ) ^ 23) ≤ fE5_43 22 := term_23_43
  have h23 : (0 : ℝ) / 24 * ((0.8254 : ℝ) ^ 24) ≤ fE5_43 23 := term_24_43
  have h24 : (0 : ℝ) / 25 * ((0.8254 : ℝ) ^ 25) ≤ fE5_43 24 := term_25_43
  have h25 : (10 : ℝ) / 26 * ((0.8254 : ℝ) ^ 26) ≤ fE5_43 25 := term_26_43
  have h26 : (-4 : ℝ) / 27 * ((0.8258 : ℝ) ^ 27) ≤ fE5_43 26 := term_27_43
  have h27 : (0 : ℝ) / 28 * ((0.8254 : ℝ) ^ 28) ≤ fE5_43 27 := term_28_43
  have h28 : (-6 : ℝ) / 29 * ((0.8258 : ℝ) ^ 29) ≤ fE5_43 28 := term_29_43
  have h29 : (0 : ℝ) / 30 * ((0.8254 : ℝ) ^ 30) ≤ fE5_43 29 := term_30_43
  have h30 : (-1 : ℝ) / 31 * ((0.8258 : ℝ) ^ 31) ≤ fE5_43 30 := term_31_43
  have h31 : (-8 : ℝ) / 32 * ((0.8258 : ℝ) ^ 32) ≤ fE5_43 31 := term_32_43
  have h32 : (6 : ℝ) / 33 * ((0.8254 : ℝ) ^ 33) ≤ fE5_43 32 := term_33_43
  have h33 : (6 : ℝ) / 34 * ((0.8254 : ℝ) ^ 34) ≤ fE5_43 33 := term_34_43
  have h34 : (0 : ℝ) / 35 * ((0.8254 : ℝ) ^ 35) ≤ fE5_43 34 := term_35_43
  have h35 : (2 : ℝ) / 36 * ((0.8254 : ℝ) ^ 36) ≤ fE5_43 35 := term_36_43
  have h36 : (0 : ℝ) / 37 * ((0.8254 : ℝ) ^ 37) ≤ fE5_43 36 := term_37_43
  have h37 : (-4 : ℝ) / 38 * ((0.8258 : ℝ) ^ 38) ≤ fE5_43 37 := term_38_43
  have h38 : (10 : ℝ) / 39 * ((0.8254 : ℝ) ^ 39) ≤ fE5_43 38 := term_39_43
  have h39 : (0 : ℝ) / 40 * ((0.8254 : ℝ) ^ 40) ≤ fE5_43 39 := term_40_43
  have h40 : (5 : ℝ) / 41 * ((0.8254 : ℝ) ^ 41) ≤ fE5_43 40 := term_41_43
  have h41 : (0 : ℝ) / 42 * ((0.8254 : ℝ) ^ 42) ≤ fE5_43 41 := term_42_43
  have h42 : (1 : ℝ) / 43 * ((0.8254 : ℝ) ^ 43) ≤ fE5_43 42 := term_43_43
  have h43 : (6 : ℝ) / 44 * ((0.8254 : ℝ) ^ 44) ≤ fE5_43 43 := term_44_43
  have h44 : (0 : ℝ) / 45 * ((0.8254 : ℝ) ^ 45) ≤ fE5_43 44 := term_45_43
  have h45 : (2 : ℝ) / 46 * ((0.8254 : ℝ) ^ 46) ≤ fE5_43 45 := term_46_43
  have h46 : (-4 : ℝ) / 47 * ((0.8258 : ℝ) ^ 47) ≤ fE5_43 46 := term_47_43
  have h47 : (-8 : ℝ) / 48 * ((0.8258 : ℝ) ^ 48) ≤ fE5_43 47 := term_48_43
  have h48 : (-7 : ℝ) / 49 * ((0.8258 : ℝ) ^ 49) ≤ fE5_43 48 := term_49_43
  have h49 : (0 : ℝ) / 50 * ((0.8254 : ℝ) ^ 50) ≤ fE5_43 49 := term_50_43
  set_option trace.linarith true in
  linarith

/-- 部分和 ≥ 2.4（crude 链）。 -/
theorem part50_ge_43 : (2.4 : ℝ) ≤ ∑ n ∈ Finset.range 50, fE5_43 n := by
  exact le_trans crude50_ge_R_43 part50_ge_crude_43

/-! ## 5. 尾界与 L(E⁵,1) ≠ 0 -/

/-- 尾上界：4·e^(−α·51)/(1−e^(−α)) < 1。
    由 e^(−α·51) < 10⁻³（`exp_neg_alpha_51_lt_43`）、1/(1−e^(−α)) ≤ 1/0.1742
    （`exp_neg_alpha_lt_8258` ⟹ 1−e^(−α) > 0.1742）与数值乘法界拼装。 -/
theorem tail51_bound_43 : (4 : ℝ) * Real.exp (-alphaE5_43 * (51 : ℕ))
    / (1 - Real.exp (-alphaE5_43)) < (1 : ℝ) := by
  have h1 : (0.1742 : ℝ) < 1 - Real.exp (-alphaE5_43) := by
    linarith [exp_neg_alpha_lt_8258]
  have h2 : (4 : ℝ) * Real.exp (-alphaE5_43 * (51 : ℕ)) ≤ (4 : ℝ) * ((1 : ℝ) / 10 ^ 3) := by
    exact mul_le_mul_of_nonneg_left exp_neg_alpha_51_lt_43.le (by norm_num : (0 : ℝ) ≤ 4)
  have h3 : 1 / (1 - Real.exp (-alphaE5_43)) ≤ 1 / (0.1742 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 0.1742) h1.le
  have he1 : Real.exp (-alphaE5_43) < 1 := by
    dsimp [alphaE5_43]
    exact lt_trans exp_neg_alpha_lt_8258 (by norm_num : (0.8258 : ℝ) < 1)
  have hc0 : (0 : ℝ) ≤ 1 / (1 - Real.exp (-alphaE5_43)) := by
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt (sub_pos.2 he1))
  have hb0 : (0 : ℝ) ≤ (4 : ℝ) * ((1 : ℝ) / 10 ^ 3) := by positivity
  have h4 : (4 : ℝ) * Real.exp (-alphaE5_43 * (51 : ℕ))
      * (1 / (1 - Real.exp (-alphaE5_43))) ≤
      (4 : ℝ) * ((1 : ℝ) / 10 ^ 3) * (1 / (0.1742 : ℝ)) := by
    exact mul_le_mul h2 h3 hc0 hb0
  have h5 : (4 : ℝ) * ((1 : ℝ) / 10 ^ 3) * (1 / (0.1742 : ℝ)) < (1 : ℝ) := by
    norm_num
  simpa [div_eq_mul_inv] using (lt_of_le_of_lt h4 h5)

/-- 尾绝对值界：|Σ'_{n≥0} fE5_43(n+50)| ≤ 2·e^(−α·51)/(1−e^(−α))。
    逐项 |fE5_43(n+50)| ≤ 2·e^(−α(n+51))（`coefficient_bound_aE5_43` + exp 衰减），
    `tsum_le_tsum` + `norm_tsum_le_tsum_norm` 后，和值由
    `hasSum_geometric_of_norm_lt_one`（r = e^(−α) < 1）+ 指标移位闭合。 -/
theorem tail_abs_le_43 :
    |∑' n : ℕ, fE5_43 (n + 50)| ≤ 2 * Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43)) := by
  have hα_pos : (0 : ℝ) < alphaE5_43 := by
    dsimp [alphaE5_43]
    exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1075))
  have hα' : ‖Real.exp (-alphaE5_43)‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    linarith
  have hb := hasSum_geometric_of_norm_lt_one hα'
  have hg0 : HasSum (fun n : ℕ ↦ (Real.exp (-alphaE5_43)) ^ 51 * (Real.exp (-alphaE5_43)) ^ n)
      ((Real.exp (-alphaE5_43)) ^ 51 * (1 - Real.exp (-alphaE5_43))⁻¹) := by
    exact hb.mul_left ((Real.exp (-alphaE5_43)) ^ 51)
  have hp : ∀ n : ℕ, (Real.exp (-alphaE5_43)) ^ 51 * (Real.exp (-alphaE5_43)) ^ n =
      Real.exp (-alphaE5_43 * (n + 51 : ℕ)) := by
    intro n
    rw [← pow_add]
    have hswap : 51 + n = n + 51 := by omega
    rw [hswap]
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hg' : HasSum (fun n : ℕ ↦ Real.exp (-alphaE5_43 * (n + 51 : ℕ)))
      ((Real.exp (-alphaE5_43)) ^ 51 * (1 - Real.exp (-alphaE5_43))⁻¹) := by
    exact hg0.congr_fun (fun n : ℕ ↦ (hp n).symm)
  have hg : HasSum (fun n : ℕ ↦ Real.exp (-alphaE5_43 * (n + 51 : ℕ)))
      ((Real.exp (-alphaE5_43)) ^ 51 / (1 - Real.exp (-alphaE5_43))) := by
    simpa [div_eq_mul_inv] using hg'
  have hgs : Summable (fun n : ℕ ↦ Real.exp (-alphaE5_43 * (n + 51 : ℕ))) := by
    exact ⟨_, hg⟩
  have hg_sum : Summable (fun n : ℕ ↦ 2 * Real.exp (-alphaE5_43 * (n + 51 : ℕ))) := by
    exact hgs.mul_left 2
  have hg_value : (∑' n : ℕ, Real.exp (-alphaE5_43 * (n + 51 : ℕ))) =
      Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43)) := by
    have hval : (Real.exp (-alphaE5_43)) ^ 51 / (1 - Real.exp (-alphaE5_43)) =
        Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43)) := by
      have hp51 : (Real.exp (-alphaE5_43)) ^ 51 = Real.exp (-alphaE5_43 * (51 : ℕ)) := by
        rw [← Real.exp_nat_mul]
        apply congrArg Real.exp
        ring
      rw [hp51]
    simpa [hval] using hg.tsum_eq
  have hterm : ∀ n : ℕ, |fE5_43 (n + 50)| ≤ 2 * Real.exp (-alphaE5_43 * (n + 51 : ℕ)) := by
    intro n
    have hk : (n + 50 + 1 : ℕ) = n + 51 := by omega
    have hcast : (↑(n + 50) + 1 : ℝ) = ↑(n + 51) := by
      calc
        (↑(n + 50) + 1 : ℝ) = ↑((n + 50) + 1) := by
          rw [show (1 : ℝ) = ↑(1 : ℕ) by norm_num]
          rw [← Nat.cast_add]
        _ = ↑(n + 51) := by simp [hk]
    unfold fE5_43
    rw [abs_mul]
    rw [hk, hcast]
    have hnn : (0 : ℝ) ≤ ((n + 51 : ℕ) : ℝ) := by positivity
    have hdiv : |(aE5_43 (n + 51 : ℕ) : ℝ) / ((n + 51 : ℕ) : ℝ)| ≤ 2 := by
      rw [abs_div]
      rw [abs_of_nonneg hnn]
      have hc : |(aE5_43 (n + 51 : ℕ) : ℝ)| ≤ 2 * ((n + 51 : ℕ) : ℝ) := by
        exact_mod_cast coefficient_bound_aE5_43 (n + 51)
      calc
        |(aE5_43 (n + 51 : ℕ) : ℝ)| / ((n + 51 : ℕ) : ℝ)
            ≤ (2 * ((n + 51 : ℕ) : ℝ)) / ((n + 51 : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right hc hnn
        _ = 2 := by
          have hx : ((n + 51 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hx]
    have he : |Real.exp (-alphaE5_43 * (n + 51 : ℕ))| = Real.exp (-alphaE5_43 * (n + 51 : ℕ)) := by
      rw [abs_of_pos (Real.exp_pos _)]
    rw [he]
    exact mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le
  have hf_abs_sum : Summable (fun n : ℕ ↦ |fE5_43 (n + 50)|) := by
    have hinj : Function.Injective (fun n : ℕ ↦ n + 50) := by
      intro a b h
      dsimp at h
      omega
    have hs : Summable (fun n : ℕ ↦ fE5_43 (n + 50)) := summable_fE5_43.comp_injective hinj
    exact hs.norm
  have hsum_le : (∑' n : ℕ, |fE5_43 (n + 50)|) ≤
      ∑' n : ℕ, 2 * Real.exp (-alphaE5_43 * (n + 51 : ℕ)) := by
    exact hf_abs_sum.tsum_le_tsum hterm hg_sum
  have habs : |∑' n : ℕ, fE5_43 (n + 50)| ≤ ∑' n : ℕ, |fE5_43 (n + 50)| := by
    have hnorm : ‖∑' n : ℕ, fE5_43 (n + 50)‖ ≤ ∑' n : ℕ, ‖fE5_43 (n + 50)‖ :=
      norm_tsum_le_tsum_norm hf_abs_sum
    simpa [Real.norm_eq_abs] using hnorm
  calc
    |∑' n : ℕ, fE5_43 (n + 50)| ≤ ∑' n : ℕ, |fE5_43 (n + 50)| := habs
    _ ≤ ∑' n : ℕ, 2 * Real.exp (-alphaE5_43 * (n + 51 : ℕ)) := hsum_le
    _ = 2 * (Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43))) := by
      rw [tsum_mul_left, hg_value]
    _ = 2 * Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43)) := by ring

/-- L(E⁵,1) > 0：部分和下界（`part50_ge_43`，2×2.4 = 4.8）
    + 尾下界（`tail_abs_le_43` 与 `tail51_bound_43` 给出 |Σ'| 上界 ⟹ 2Σ' ≥ −2B，2B < 1）。
    合成：L(E⁵,1) ≥ 4.8 − 2B > 4.8 − 1 = 3.8 > 0。 -/
theorem L_E5_43_one_pos : 0 < L_E5_43 1 := by
  let B : ℝ := 2 * Real.exp (-alphaE5_43 * (51 : ℕ)) / (1 - Real.exp (-alphaE5_43))
  have hS : (2 : ℝ) * (2.4 : ℝ) ≤ 2 * (∑ n ∈ Finset.range 50, fE5_43 n) := by
    exact mul_le_mul_of_nonneg_left part50_ge_43 (by norm_num : (0 : ℝ) ≤ 2)
  have hS' : -(2 * B) ≤ 2 * (∑' n : ℕ, fE5_43 (n + 50)) := by
    have hneg : -(2 * |∑' n : ℕ, fE5_43 (n + 50)|) ≤ 2 * (∑' n : ℕ, fE5_43 (n + 50)) := by
      have h1 : -(|∑' n : ℕ, fE5_43 (n + 50)|) ≤ ∑' n : ℕ, fE5_43 (n + 50) := by
        have hx : -(∑' n : ℕ, fE5_43 (n + 50)) ≤ |∑' n : ℕ, fE5_43 (n + 50)| := by
          simpa [abs_neg] using le_abs_self (-(∑' n : ℕ, fE5_43 (n + 50)))
        simpa using neg_le_neg hx
      have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
      simpa [mul_neg, mul_comm] using h2
    have hb1 : 2 * |∑' n : ℕ, fE5_43 (n + 50)| ≤ 2 * B := by
      exact mul_le_mul_of_nonneg_left tail_abs_le_43 (by norm_num : (0 : ℝ) ≤ 2)
    have hb2 : -(2 * B) ≤ -(2 * |∑' n : ℕ, fE5_43 (n + 50)|) := by
      linarith
    exact le_trans hb2 hneg
  have hlb : (2 : ℝ) * (2.4 : ℝ) + -(2 * B) ≤ L_E5_43 1 := by
    have hsplit := L_E5_series_split_43 50
    rw [hsplit]
    exact add_le_add hS hS'
  have hbase : (0 : ℝ) < (2 : ℝ) * (2.4 : ℝ) - 2 * B := by
    have hBlt : 2 * B < (1 : ℝ) := by
      dsimp [B]
      convert tail51_bound_43 using 1
      ring
    have h55 : (1 : ℝ) < (2 : ℝ) * (2.4 : ℝ) := by norm_num
    linarith
  linarith

/-- L(E⁵,1) ≠ 0：`L_E5_43_one_pos` 直接推论。 -/
theorem L_E5_43_one_ne_zero : L_E5_43 1 ≠ 0 := by
  exact ne_of_gt L_E5_43_one_pos

end

end BSD.LSeries5_43
