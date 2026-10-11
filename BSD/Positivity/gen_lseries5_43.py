# gen_lseries5_43.py - 生成 LSeries5_43.lean (43a1 E^5 侧闭证)
# 数值口径：alpha=2*pi/sqrt(1075), qneg=0.8254(正项底), qpos=0.8258(负项底)
# crude 部分和 >= 2.4, e^{-alpha*51} < 1e-3, tail51: 4*.../(1-...) < 1
# 关键策略：crude 表达式全部数值化（python 预读表），避免跨文件表 def 展开
import re
from fractions import Fraction as F

# ---- 读 aE5 表前 50 项 ----
aE5 = {}
with open(r"C:\proj2\BSD\aE5_table_43.lean") as f:
    for line in f:
        m = re.match(r"^\|\s*(\d+)\s*=>\s*(-?\d+)", line)
        if m:
            aE5[int(m.group(1))] = int(m.group(2))

assert len(aE5) >= 50, f"table too small: {len(aE5)}"

def qbase(i):
    return "0.8254" if aE5[i] >= 0 else "0.8258"

def qbaseQ(i):
    return "8254" if aE5[i] >= 0 else "8258"

# ---- 数值化 crude 项（ℝ def 行）----
crude_def_lines = []
for i in range(50):
    v = aE5[i + 1]
    crude_def_lines.append(
        f"  | {i} => ({v} : ℝ) / {i + 1} * (({qbase(i + 1)} : ℝ) ^ {i + 1})")
crude_defs = "\n".join(crude_def_lines)

# ---- 数值化 ℚ 块表达式 + 精确块值 ----
qQ = F(8254, 10000)
qQp = F(8258, 10000)
block_q_exprs = []
block_bounds = []
for b in range(5):
    items = []
    s = F(0)
    for i in range(10 * b + 1, 10 * b + 11):
        v = aE5[i]
        base = qbaseQ(i)
        items.append(f"({v} : ℚ) / {i} * ((({base} : ℚ) / 10000) ^ {i})")
        s += F(v) / i * (qQ if v >= 0 else qQp) ** i
    qe = items[0]
    for e in items[1:]:
        qe = f"({qe} + ({e}))"
    block_q_exprs.append(qe)
    block_bounds.append(f"{s.numerator}/{s.denominator}")

# 精确块值（python 显示用）
block_vals_float = []
for b in range(5):
    s = F(0)
    for i in range(10 * b + 1, 10 * b + 11):
        v = aE5[i]
        s += F(v) / i * (qQ if v >= 0 else qQp) ** i
    block_vals_float.append(float(s))
print("block values:", block_vals_float, "sum:", sum(block_vals_float))

# ---- term_i 引理（LHS 数值化）----
terms = []
for i in range(1, 51):
    a = aE5[i]
    base = qbase(i)
    if a > 0:
        terms.append(f"""theorem term_{i}_43 : (({a} : ℝ) / {i} * (({base} : ℝ) ^ {i})) ≤ fE5_43 {i - 1} := by
  have heq : ({a} : ℤ) = aE5_43 {i} := by native_decide
  have hcast : ({a} : ℝ) = (aE5_43 {i} : ℝ) := by exact_mod_cast heq
  have hcoef : (0 : ℝ) ≤ ({a} : ℝ) / {i} := by norm_num
  have hpow := powE_any_43 {i - 1}
  have hpow2 : ({base} : ℝ) ^ {i} ≤ Real.exp (-alphaE5_43 * ({i} : ℝ)) := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hpow2 hcoef
  calc
    ({a} : ℝ) / {i} * (({base} : ℝ) ^ {i}) ≤ ({a} : ℝ) / {i} * Real.exp (-alphaE5_43 * ({i} : ℝ)) := hm
    _ = (aE5_43 {i} : ℝ) / {i} * Real.exp (-alphaE5_43 * ({i} : ℝ)) := by
      rw [hcast]
    _ = fE5_43 {i - 1} := by
      norm_num [fE5_43, alphaE5_43]""")
    elif a < 0:
        terms.append(f"""theorem term_{i}_43 : (({a} : ℝ) / {i} * (({base} : ℝ) ^ {i})) ≤ fE5_43 {i - 1} := by
  have heq : ({a} : ℤ) = aE5_43 {i} := by native_decide
  have hcast : ({a} : ℝ) = (aE5_43 {i} : ℝ) := by exact_mod_cast heq
  have hcoef : ({a} : ℝ) / {i} ≤ 0 := by norm_num
  have hpow := powE'_any_43 {i - 1}
  have hpow2 : Real.exp (-alphaE5_43 * ({i} : ℝ)) ≤ ({base} : ℝ) ^ {i} := by
    convert hpow using 1 <;> norm_num
  have hm := mul_le_mul_of_nonpos_left hpow2 hcoef
  calc
    ({a} : ℝ) / {i} * (({base} : ℝ) ^ {i}) ≤ ({a} : ℝ) / {i} * Real.exp (-alphaE5_43 * ({i} : ℝ)) := hm
    _ = (aE5_43 {i} : ℝ) / {i} * Real.exp (-alphaE5_43 * ({i} : ℝ)) := by
      rw [hcast]
    _ = fE5_43 {i - 1} := by
      norm_num [fE5_43, alphaE5_43]""")
    else:
        terms.append(f"""theorem term_{i}_43 : ((0 : ℝ) / {i} * (({base} : ℝ) ^ {i})) ≤ fE5_43 {i - 1} := by
  have hz : aE5_43 {i} = 0 := by native_decide
  have hzr : (aE5_43 {i} : ℝ) = 0 := by exact_mod_cast hz
  calc
    0 / {i} * (({base} : ℝ) ^ {i}) = 0 := by norm_num
    _ ≤ fE5_43 {i - 1} := by
      rw [show fE5_43 {i - 1} = 0 by norm_num [fE5_43, alphaE5_43, hzr]]""")
terms_txt = "\n\n".join(terms)

# ---- crude50_ge_R_43 分块（数值化）----
block_havess = []
for b in range(5):
    block_havess.append(f"""  have hq{b} : ({block_bounds[b]} : ℚ) ≤ {block_q_exprs[b]} := by
    native_decide
  have hq{b}' := (Rat.cast_le (K := ℝ)).mpr hq{b}
  norm_num at hq{b}'""")
blocks_txt = "\n".join(block_havess)

# ---- part50_ge_crude_43 的 term have ----
term_haves = "\n".join(
    f"  have h{i - 1} : ({aE5[i]} : ℝ) / {i} * (({qbase(i)} : ℝ) ^ {i}) ≤ fE5_43 {i - 1} := term_{i}_43"
    for i in range(1, 51))

content = f"""import Mathlib.Data.Rat.Cast.Lemmas
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

/-- 反射公式第 n 项：fE5_43 n = a_{{n+1}}(E⁵)/(n+1) · e^(−α·(n+1))。 -/
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
{terms_txt}

/-- 粗界逐项函数（ℝ，数值化——aE5 值直接代入，符号驱动选底）。 -/
def crude_n_R_43 : ℕ → ℝ
{crude_defs}
  | _ => 0

/-- 部分和粗界（ℝ）：2.4 ≤ Σ_{i<50} crude_n_R_43 i。
    分块 ℚ 精确值 native_decide（纯数值）+ cast 桥 + linarith 拼和。
    块值（精确 ℚ）：块0 ≈ 2.3442182640436284，块1 ≈ 0.09392300233131758，
    块2 ≈ 0.005501631468829098，块3 ≈ 7.65e-5，块4 ≈ 4.89e-5；总和 ≈ 2.443918 > 2.4。 -/
theorem crude50_ge_R_43 : (2.4 : ℝ) ≤ ∑ i ∈ Finset.range 50, crude_n_R_43 i := by
{blocks_txt}
  have hsum : ({block_bounds[0]} : ℝ) + ({block_bounds[1]} : ℝ) + ({block_bounds[2]} : ℝ)
      + ({block_bounds[3]} : ℝ) + ({block_bounds[4]} : ℝ) ≤ ∑ i ∈ Finset.range 50, crude_n_R_43 i := by
    simp [Finset.sum_range_succ, crude_n_R_43]
    linarith
  have htot : (2.4 : ℝ) ≤ ({block_bounds[0]} : ℝ) + ({block_bounds[1]} : ℝ) + ({block_bounds[2]} : ℝ)
      + ({block_bounds[3]} : ℝ) + ({block_bounds[4]} : ℝ) := by
    norm_num
  linarith

/-- 粗界 ≤ 真部分和（逐项 term_i + linarith）。 -/
theorem part50_ge_crude_43 :
    ∑ i ∈ Finset.range 50, crude_n_R_43 i ≤ ∑ n ∈ Finset.range 50, fE5_43 n := by
  simp [Finset.sum_range_succ, crude_n_R_43]
{term_haves}
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

/-- 尾绝对值界：|Σ'_{{n≥0}} fE5_43(n+50)| ≤ 2·e^(−α·51)/(1−e^(−α))。
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
"""

with open(r"C:\proj2\BSD\LSeries5_43.lean", "w", encoding="utf-8") as f:
    f.write(content)
print("written LSeries5_43.lean,", len(content), "chars")
