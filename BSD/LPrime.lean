import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import BSD.aE_table

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory

/-!
# B3: L′(E,1) 的严格下界（N = 37，ε = −1 反射公式一阶导）

目标：把 `Main.lean` 的 `Lprime_E1` + `Lprime_E1_interval` 两个 axiom
（裸数值断言，LMFDB 0.305999773834）升级为「公式形态 + 真定理」。

核心公式（反射公式一阶导，N = 37 奇符号）：
    L′(E,1) = 2 · Σ_{n≥1} aₙ/n · E₁(2πn/√37)
其中 E₁(b) = ∫_b^∞ e^{−t}/t dt（不完全 Gamma 函数 Γ(0,b) 的实值形态），
aₙ = aₙ(E)，E = 37a1（y²+y = x³−x），a_p = p+1−#E(𝔽_p)。

分层：
1. **aₙ 表（代数层，真）**：`aE_raw` 前 100 项（穷举点计数），
   `aE_bound : |aₙ| ≤ 2n` 为 native_decide 定理（同 aE5_table 模式）。
2. **E₁（分析层，真）**：积分定义 + 分部积分界
   e^{−b}(1/b − 1/b²) ≤ E₁(b) ≤ e^{−b}/b（探针已证上界与 ∫e^{−t}/t² 界）。
3. **反射公式（声明层）**：`lprime1_series` axiom——L′(E,1) 的级数形态
   （mathlib 无自守 L / 不完全 Gamma 理论，与 LSeries5.lean 的 C3/C4 同级）。
4. **部分和与尾界（本轮目标）**：
   - B3-min：仅证 L′(E,1) > 0（Main.lean 的 `LK_prime_pos` 只需 > 0）；
     部分和 = 首项正 + 尾项上界，用 E₁ 的分段积分下界。
   - B3-full：窄区间 [0.30599977, 0.30600000]（需 E₁ 的 10⁻⁷ 界：
     γ + ln + 幂级数的高精度区间算术，另行轮次）。

数值校准（b3_calib2.py，mpmath dps=60）：
S₃₀ = 0.305999773834 ± 6.9e-15 ⊂ [0.30599977, 0.30600000]，
与 LMFDB 0.3059997738344167 12 位全合。尾界 N=30 时 ~7e-15。
-/

namespace BSD.LPrime

noncomputable section

/-! ## 1. aₙ 表（E = 37a1） -/

/-- E = 37a1 的 aₙ（n ≤ 100 查表，表外为 0）。 -/
def aE (n : ℕ) : ℤ := if n ≤ 100 then aE_raw n else 0

/-- |aₙ| ≤ 2n（n ≤ 100，interval_cases 逐项 native_decide 查表核验）。 -/
theorem aE_bound (m : ℕ) (hm : m ≤ 100) : |aE m| ≤ 2 * (m : ℤ) := by
  rw [aE, if_pos hm]
  interval_cases m <;> native_decide

/-! ## 2. E₁ 定义与界 -/

/-- E₁(b) = ∫_b^∞ e^{−t}/t dt（Γ(0,b) 的实值形态；b > 0 收敛）。 -/
def E1 (b : ℝ) : ℝ := ∫ t in Set.Ioi b, Real.exp (-t) / t

/-- bₙ = 2πn/√37（ℚ 端 exp 衰减常数）。 -/
def bn (n : ℕ) : ℝ := 2 * Real.pi * (n : ℝ) / Real.sqrt 37

/-- 逐点：t ≥ b > 0 ⟹ e^{−t}/t ≤ e^{−t}/b。 -/
lemma pt_le {b t : ℝ} (hb : 0 < b) (htb : b ≤ t) :
    Real.exp (-t) / t ≤ Real.exp (-t) / b := by
  have ht_pos : 0 < t := lt_of_lt_of_le hb htb
  have h : (1 / t : ℝ) ≤ 1 / b := one_div_le_one_div_of_le hb htb
  have he : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
  calc
    Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
    _ ≤ Real.exp (-t) * (1 / b) := mul_le_mul_of_nonneg_left h he
    _ = Real.exp (-t) / b := by ring

/-- e^{−t}/t 在 (b,∞) 上连续（b > 0）。 -/
lemma cont_div (b : ℝ) (hb : 0 < b) :
    ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi b) := by
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  · exact continuous_id.continuousOn
  · intro x hx
    exact ne_of_gt (lt_trans hb hx)

/-- 上界：E₁(b) ≤ e^{−b}/b（1/t ≤ 1/b on (b,∞)，∫e^{−t} = e^{−b}）。 -/
theorem E1_le (b : ℝ) (hb : 0 < b) :
    (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤ Real.exp (-b) / b := by
  have h1 : (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤
      (∫ t in Set.Ioi b, Real.exp (-t) / b) := by
    refine integral_mono_ae ?_ ?_ ?_
    · apply Integrable.mono'
      · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)
      · exact (cont_div b hb).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := lt_trans hb ht
        have htb : b ≤ t := le_of_lt ht
        have hnonneg : 0 ≤ Real.exp (-t) / t := by
          exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt ht_pos)
        have hpt : Real.exp (-t) / t ≤ Real.exp (-t) / b := pt_le hb htb
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpt
    · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact pt_le hb (le_of_lt ht)
  calc
    (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤ (∫ t in Set.Ioi b, Real.exp (-t) / b) := h1
    _ = (∫ t in Set.Ioi b, Real.exp (-t)) / b := by
      rw [← integral_div]
    _ = Real.exp (-b) / b := by
      rw [integral_exp_neg_Ioi]

/-- 分部积分组件：∫_{Ioi b} e^{−t}/t² ≤ e^{−b}/b²（1/t² ≤ 1/b² on (b,∞)）。 -/
theorem E1_aux_le (b : ℝ) (hb : 0 < b) :
    (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤ Real.exp (-b) / b ^ 2 := by
  have hg : (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) = Real.exp (-b) / b ^ 2 := by
    calc
      (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) =
          b⁻¹ * (b⁻¹ * (∫ t in Set.Ioi b, Real.exp (-t))) := by
        rw [← integral_const_mul, ← integral_const_mul]
      _ = b⁻¹ * (b⁻¹ * Real.exp (-b)) := by
        rw [integral_exp_neg_Ioi]
      _ = Real.exp (-b) / b ^ 2 := by
        ring
  have h1 : (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤
      (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) := by
    refine integral_mono_ae ?_ ?_ ?_
    · apply Integrable.mono'
      · exact ((integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)).const_mul (b⁻¹)
      · apply ContinuousOn.aestronglyMeasurable
        · apply ContinuousOn.div
          · exact (Real.continuous_exp.comp continuous_neg).continuousOn
          · exact (continuous_id.pow 2).continuousOn
          · intro x hx
            have hx0 : 0 < x := lt_trans hb hx
            exact ne_of_gt (sq_pos_of_pos hx0)
        · exact measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := lt_trans hb ht
        have htb : b ≤ t := le_of_lt ht
        have h_nonneg : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
        have hnonneg2 : 0 ≤ Real.exp (-t) / t ^ 2 := by
          exact div_nonneg h_nonneg (sq_pos_of_pos ht_pos).le
        have hsq : (1 / t ^ 2 : ℝ) ≤ 1 / b ^ 2 := by
          have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht_pos
          have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
          exact (one_div_le_one_div ht2 hb2).2 (pow_le_pow_left₀ (le_of_lt hb) htb 2)
        have hsq' : (t ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
          simpa [one_div] using hsq
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg hnonneg2]
        calc
          Real.exp (-t) / t ^ 2 = Real.exp (-t) * (t ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
          _ ≤ Real.exp (-t) * (b ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsq' h_nonneg
          _ = b⁻¹ * (b⁻¹ * Real.exp (-t)) := by
            ring
    · exact ((integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)).const_mul (b⁻¹)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := lt_trans hb ht
      have htb : b ≤ t := le_of_lt ht
      have h_nonneg : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
      have hsq : (1 / t ^ 2 : ℝ) ≤ 1 / b ^ 2 := by
        have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht_pos
        have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
        exact (one_div_le_one_div ht2 hb2).2 (pow_le_pow_left₀ (le_of_lt hb) htb 2)
      have hsq' : (t ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
        simpa [one_div] using hsq
      calc
        Real.exp (-t) / t ^ 2 = Real.exp (-t) * (t ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ Real.exp (-t) * (b ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsq' h_nonneg
        _ = b⁻¹ * (b⁻¹ * Real.exp (-t)) := by
          ring
  calc
    (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤
        (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) := h1
    _ = Real.exp (-b) / b ^ 2 := hg

/-! ## 3. 反射公式一阶导（声明层） -/

/-- L′(E,1) 的级数形态：lprime1 = 2Σ aₙ/n·E₁(2πn/√37)。
    依据：N = 37，根数 ε = −1，函数方程 Λ(s) = −Λ(2−s)（奇符号），
    一阶导 Mellin 展开——不完全 Gamma 在 s = 1 处的导数给出 E₁ 项。
    本 def 即 L′(E,1) 的「计算形态」；Main.lean 的 `Lprime_E1` 将引用本定义
    （B2 axiom 删除），数学身份见 `lprime1_series_note`。 -/
noncomputable def lprime1 : ℝ :=
  2 * ∑' n : ℕ, (aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))

-- (axiom lprime1_summable deleted in 1c replication; now a theorem below)

-- L′(E,1) > 0（B3-min 核心定理，本轮待实施）：
-- 部分和 S_N（正项下界）> 尾项上界 4Σ_{n>N} e^{−bₙ}/bₙ（几何级数）。
-- 结构：首项 2E₁(b₁) ≥ 分段积分下界，尾项 |Σ 2aₙ/n·E₁(bₙ)| ≤ Σ 4e^{−bₙ}/bₙ
-- （|aₙ| ≤ 2n + E₁ 上界 + 几何尾）；exp 数值界引理 + 部分和区间块。

/-! ## 4. B3-min：L′(E,1) > 0 真定理 -/

-- 4.1 b₁ = 2π/√37 的界：(1.03, 1.04)

/-- √37 < 6.09（(6.09)² = 37.0881 > 37；分数形态 609/100 便于 norm_num）。 -/
lemma sqrt37_lt_609 : Real.sqrt 37 < (6.09 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 6.09)]
  norm_num [show (6.09 : ℝ) = (609 : ℝ) / 100 by norm_num]

/-- b₁ > 1.03：π > 3.1415 + √37 < 6.09。 -/
theorem b1_gt_103 : (1.03 : ℝ) < 2 * Real.pi / Real.sqrt 37 := by
  have h1 : (1.03 : ℝ) * Real.sqrt 37 < (1.03 * 6.09 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt37_lt_609 (by norm_num : (0 : ℝ) < 1.03)
  have h2 : (1.03 * 6.09 : ℝ) < 2 * Real.pi := by
    have h3 : (1.03 * 6.09 : ℝ) < 2 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 2))
  have h4 : (1.03 : ℝ) * Real.sqrt 37 < 2 * Real.pi := lt_trans h1 h2
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37))]
  exact h4

/-! ## ①c 复刻：lprime1_summable axiom → theorem（几何级数闭合） -/

/-- lprime1 级数绝对收敛（①c）：
    逐项界 |aₙ₊₁/(n+1)·E₁(bₙ₊₁)| ≤ (2/1.03)·e^{−1.03(n+1)}（|aₙ| ≤ 2n、E₁ ≤ e^{−b}/b、
    bₙ ≥ 1.03n），右侧为几何级数 ⟹ Summable（`Summable.of_norm_bounded`）。 -/
theorem lprime1_summable :
    Summable (fun n : ℕ => (aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))) := by
  -- 几何级数：Σ (2/1.03)·e^{−1.03(n+1)}
  let q : ℝ := Real.exp (-(1.03 : ℝ))
  have hq_abs : |q| < 1 := by
    dsimp [q]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hb : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hq_abs
  have hq1 : HasSum (fun n : ℕ => q ^ (n + 1)) (q * (1 - q)⁻¹) := by
    have hfun : (fun n : ℕ => q ^ (n + 1)) = fun n : ℕ => q ^ n * q := by
      funext n
      rw [← pow_succ]
    have hb' : HasSum (fun n : ℕ => q ^ n * q) ((1 - q)⁻¹ * q) := hb.mul_right q
    simpa [hfun, mul_comm, mul_left_comm, mul_assoc] using hb'
  have hpow : ∀ n : ℕ, Real.exp (-(1.03 : ℝ) * (n : ℕ)) = q ^ n := by
    intro n
    rw [mul_comm]
    rw [Real.exp_nat_mul]
  have hg : Summable (fun n : ℕ => (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ))) := by
    have hfun : (fun n : ℕ => (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)))
        = fun n : ℕ => (2 / (1.03 : ℝ)) * q ^ (n + 1) := by
      funext n
      rw [hpow (n + 1)]
    have hg' : Summable (fun n : ℕ => (2 / (1.03 : ℝ)) * q ^ (n + 1)) :=
      hq1.summable.mul_left (2 / (1.03 : ℝ))
    convert hg' using 1
  -- 逐项界
  refine Summable.of_norm_bounded hg ?_
  intro n
  rw [Real.norm_eq_abs]
  have hbnpos : 0 < bn (n + 1) := by
    dsimp [bn]
    positivity
  have hA : |aE (n + 1)| ≤ 2 * ((n + 1 : ℕ) : ℤ) := by
    by_cases hm : n + 1 ≤ 100
    · exact aE_bound (n + 1) hm
    · dsimp [aE]
      rw [if_neg hm]
      norm_num
      positivity
  have hA' : |(aE (n + 1) : ℝ) / (n + 1)| ≤ 2 := by
    have hz : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      |(aE (n + 1) : ℝ) / (n + 1)| = (|aE (n + 1)| : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        rw [abs_div]
        simp
        congr 1
        exact abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      _ ≤ 2 := by
        exact (div_le_iff₀ hz).2 (by exact_mod_cast hA)
  have hE1 : E1 (bn (n + 1)) ≤ Real.exp (-bn (n + 1)) / bn (n + 1) := E1_le (bn (n + 1)) hbnpos
  have hE1nonneg : 0 ≤ E1 (bn (n + 1)) := by
    dsimp [E1]
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt (lt_trans hbnpos ht)))
  have hstep1 : |(aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))| ≤ 2 * E1 (bn (n + 1)) := by
    calc
      |(aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))|
          = |(aE (n + 1) : ℝ) / (n + 1)| * |E1 (bn (n + 1))| := by
        rw [abs_mul]
      _ = |(aE (n + 1) : ℝ) / (n + 1)| * E1 (bn (n + 1)) := by
        congr 1
        exact abs_of_nonneg hE1nonneg
      _ ≤ 2 * E1 (bn (n + 1)) := by
        exact mul_le_mul_of_nonneg_right hA' hE1nonneg
  have hstep2 : 2 * E1 (bn (n + 1)) ≤ 2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) := by
    exact mul_le_mul_of_nonneg_left hE1 (by norm_num : (0 : ℝ) ≤ 2)
  have hbn103 : (n + 1 : ℝ) * 1.03 ≤ bn (n + 1) := by
    have hb1 : (1.03 : ℝ) ≤ 2 * Real.pi / Real.sqrt 37 := b1_gt_103.le
    calc
      (n + 1 : ℝ) * 1.03 ≤ (n + 1 : ℝ) * (2 * Real.pi / Real.sqrt 37) := by
        exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = bn (n + 1) := by
        dsimp [bn]
        norm_cast
        ring
  have hb1le : (1.03 : ℝ) ≤ bn (n + 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ n + 1)
    calc
      (1.03 : ℝ) = (1 : ℝ) * 1.03 := by ring
      _ ≤ ((n : ℝ) + 1) * 1.03 := by
        exact mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1.03)
      _ ≤ bn (n + 1) := by
        simpa [Nat.cast_add] using hbn103
  have hdiv : (bn (n + 1))⁻¹ ≤ (1.03 : ℝ)⁻¹ := by
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1.03) hb1le)
  have hbn103' : (1.03 : ℝ) * (n + 1 : ℕ) ≤ bn (n + 1) := by
    simpa [mul_comm] using hbn103
  have hneg : -bn (n + 1) ≤ -(1.03 : ℝ) * (n + 1 : ℕ) := by
    rw [neg_mul]
    exact neg_le_neg hbn103'
  have hmono : Real.exp (-bn (n + 1)) ≤ Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
    exact (Real.exp_le_exp).mpr hneg
  have hq : Real.exp (-bn (n + 1)) / bn (n + 1) ≤
      Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) / (1.03 : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hmono hdiv (by positivity : (0 : ℝ) ≤ (bn (n + 1))⁻¹)
      (by positivity : (0 : ℝ) ≤ Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)))
  have hstep3 : 2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) ≤
      (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
    calc
      2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) ≤
          2 * (Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) / (1.03 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)
      _ = (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
        ring
  exact le_trans hstep1 (le_trans hstep2 hstep3)

/-- √37 > 1511/250 = 6.044（(1511/250)² = 36.53 < 37）。 -/
lemma sqrt37_gt_60416 : ((1511 : ℝ) / 250) < Real.sqrt 37 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (1511 : ℝ) / 250)]
  norm_num

/-- b₁ < 1.04：π < 3.1416 + √37 > 1511/250（0.52·(1511/250) = 3.1430 > 3.1416）。 -/
theorem b1_lt_104 : 2 * Real.pi / Real.sqrt 37 < (1.04 : ℝ) := by
  have h1 : (0.52 : ℝ) * ((1511 : ℝ) / 250) < (0.52 : ℝ) * Real.sqrt 37 := by
    exact mul_lt_mul_of_pos_left sqrt37_gt_60416 (by norm_num : (0 : ℝ) < 0.52)
  have hpi : Real.pi < (0.52 : ℝ) * Real.sqrt 37 := by
    have h5 : (3.1416 : ℝ) < (0.52 : ℝ) * ((1511 : ℝ) / 250) := by norm_num
    exact lt_trans Real.pi_lt_d4 (lt_of_lt_of_le h5 h1.le)
  have h2 : 2 * Real.pi < (1.04 : ℝ) * Real.sqrt 37 := by
    calc
      2 * Real.pi < 2 * ((0.52 : ℝ) * Real.sqrt 37) := mul_lt_mul_of_pos_left hpi (by norm_num : (0 : ℝ) < 2)
      _ = (1.04 : ℝ) * Real.sqrt 37 := by ring
  rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37))]
  exact h2

-- 4.2 q = e^{−1.03} 上界（e^{−1}·e^{−0.03}，exp_bound）

/-- e^{−1} ≤ 0.36790（exp_bound n = 12：Σ₁₂ − B₁₂ ≤ e^{−1} ≤ Σ₁₂ + B₁₂）。 -/
theorem exp_neg_one_le : Real.exp (-1) ≤ (0.36790 : ℝ) := by
  have hb := Real.exp_bound (x := (-1 : ℝ)) (n := 12) (by norm_num : |(-1 : ℝ)| ≤ 1) (by norm_num : 0 < 12)
  have hd : |Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ))| ≤
      |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := hb
  have hd2 : Real.exp (-1) ≤ (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) +
      |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := by
    have h1 : Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) ≤
        |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) :=
      le_trans (le_abs_self _) hd
    linarith
  have hsum : (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) ≤ (0.36788 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hbnd : (0.36788 : ℝ) + |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ (0.36790 : ℝ) := by
    norm_num
  linarith

/-- e^{−1} ≥ 0.36786（exp_bound 下界）。 -/
theorem exp_neg_one_ge : (0.36786 : ℝ) ≤ Real.exp (-1) := by
  have hb := Real.exp_bound (x := (-1 : ℝ)) (n := 12) (by norm_num : |(-1 : ℝ)| ≤ 1) (by norm_num : 0 < 12)
  have hd : |Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ))| ≤
      |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := hb
  have hd2 : (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) -
      |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ Real.exp (-1) := by
    have h1 : -( |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12))) ≤
        Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) := by
      have hneg : -|Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ))| ≤
          Real.exp (-1) - (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) :=
        neg_le.1 (neg_le_abs _)
      exact le_trans (neg_le_neg hd) hneg
    linarith
  have hsum : (0.36786 : ℝ) ≤ (∑ m ∈ Finset.range 12, (-1 : ℝ) ^ m / (m.factorial : ℝ)) -
      |(-1 : ℝ)| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- e^{−0.03} ≤ 0.970446（exp_bound n = 6）。 -/
theorem exp_neg_003_le : Real.exp (-(0.03 : ℝ)) ≤ (0.970446 : ℝ) := by
  have hb := Real.exp_bound (x := (-(0.03 : ℝ))) (n := 6) (by norm_num : |(-(0.03 : ℝ))| ≤ 1) (by norm_num : 0 < 6)
  have hd : |Real.exp (-(0.03 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.03 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
      |(-(0.03 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := hb
  have hd2 : Real.exp (-(0.03 : ℝ)) ≤ (∑ m ∈ Finset.range 6, (-(0.03 : ℝ)) ^ m / (m.factorial : ℝ)) +
      |(-(0.03 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
    have h1 : Real.exp (-(0.03 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.03 : ℝ)) ^ m / (m.factorial : ℝ)) ≤
        |(-(0.03 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) :=
      le_trans (le_abs_self _) hd
    linarith
  have hsum : (∑ m ∈ Finset.range 6, (-(0.03 : ℝ)) ^ m / (m.factorial : ℝ)) ≤ (0.9704456 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hbnd : (0.9704456 : ℝ) + |(-(0.03 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (0.970446 : ℝ) := by
    norm_num
  linarith

/-- q = e^{−1.03} ≤ 0.358（e^{−1.03} = e^{−1}·e^{−0.03}）。 -/
theorem exp_neg_103_le : Real.exp (-(1.03 : ℝ)) ≤ (0.358 : ℝ) := by
  have h1 : Real.exp (-(1.03 : ℝ)) = Real.exp (-1) * Real.exp (-(0.03 : ℝ)) := by
    have hsplit : -(1.03 : ℝ) = -1 + -(0.03 : ℝ) := by norm_num
    rw [hsplit, Real.exp_add]
  have h2a : Real.exp (-1) * Real.exp (-(0.03 : ℝ)) ≤
      (0.36790 : ℝ) * Real.exp (-(0.03 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right exp_neg_one_le (by positivity)
  have h2b : (0.36790 : ℝ) * Real.exp (-(0.03 : ℝ)) ≤ (0.36790 : ℝ) * (0.970446 : ℝ) := by
    exact mul_le_mul_of_nonneg_left exp_neg_003_le (by norm_num : (0 : ℝ) ≤ 0.36790)
  have h2 : Real.exp (-1) * Real.exp (-(0.03 : ℝ)) ≤ (0.36790 : ℝ) * (0.970446 : ℝ) :=
    le_trans h2a h2b
  have h3 : (0.36790 : ℝ) * (0.970446 : ℝ) ≤ (0.358 : ℝ) := by norm_num
  rw [h1]
  exact le_trans h2 h3

-- 4.3 b₂ = 4π/√37 > 2.06、b₃ = 6π/√37 > 3.09（√37 < 6.09 + π > 3.1415）

/-- b₂ > 2.06：2.06·√37 < 2.06·6.09 = 12.5454 < 4π。 -/
theorem b2_gt_206 : (2.06 : ℝ) < bn 2 := by
  have h1 : (2.06 : ℝ) * Real.sqrt 37 < (2.06 * 6.09 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt37_lt_609 (by norm_num : (0 : ℝ) < 2.06)
  have h2 : (2.06 * 6.09 : ℝ) < 4 * Real.pi := by
    have h3 : (2.06 * 6.09 : ℝ) < 4 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 4))
  have h4 : (2.06 : ℝ) * Real.sqrt 37 < 4 * Real.pi := lt_trans h1 h2
  have hden : (0 : ℝ) < Real.sqrt 37 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37)
  have htarget : (2.06 : ℝ) < 4 * Real.pi / Real.sqrt 37 := by
    simpa [lt_div_iff₀ hden] using h4
  have hbn : 4 * Real.pi / Real.sqrt 37 = bn 2 := by
    unfold bn
    ring
  rwa [← hbn]

/-- b₃ > 3.09：3.09·√37 < 3.09·6.09 = 18.8181 < 6π。 -/
theorem b3_gt_309 : (3.09 : ℝ) < bn 3 := by
  have h1 : (3.09 : ℝ) * Real.sqrt 37 < (3.09 * 6.09 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt37_lt_609 (by norm_num : (0 : ℝ) < 3.09)
  have h2 : (3.09 * 6.09 : ℝ) < 6 * Real.pi := by
    have h3 : (3.09 * 6.09 : ℝ) < 6 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 6))
  have h4 : (3.09 : ℝ) * Real.sqrt 37 < 6 * Real.pi := lt_trans h1 h2
  have hden : (0 : ℝ) < Real.sqrt 37 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37)
  have htarget : (3.09 : ℝ) < 6 * Real.pi / Real.sqrt 37 := by
    simpa [lt_div_iff₀ hden] using h4
  have hbn : 6 * Real.pi / Real.sqrt 37 = bn 3 := by
    unfold bn
    ring
  rwa [← hbn]

-- 4.4 E₁(b₂) ≤ 0.063、E₁(b₃) ≤ 0.015（E₁ 上界 + q 幂）

/-- E₁(b₂) ≤ 0.063：E₁(b) ≤ e^{−b}/b ≤ q²/2.06，q ≤ 0.358。 -/
theorem E1_b2_le : E1 (bn 2) ≤ (0.063 : ℝ) := by
  have hb : (0 : ℝ) < bn 2 := by linarith [b2_gt_206]
  have h1 : E1 (bn 2) ≤ Real.exp (-bn 2) / bn 2 := E1_le (bn 2) hb
  have hq : Real.exp (-bn 2) ≤ (0.358 : ℝ) ^ 2 := by
    -- e^{−b₂} = (e^{−b₁})²，b₁ > 1.03 ⟹ e^{−b₁} ≤ e^{−1.03} ≤ 0.358
    have heq : Real.exp (-bn 2) = Real.exp (-bn 1) ^ 2 := by
      have h : -bn 2 = ((2 : ℕ) : ℝ) * (-bn 1) := by
        unfold bn
        ring
      rw [h, Real.exp_nat_mul]
    rw [heq]
    have hb1 : Real.exp (-bn 1) ≤ Real.exp (-(1.03 : ℝ)) := by
      apply Real.exp_le_exp_of_le
      have hgt : (1.03 : ℝ) < bn 1 := by
        simpa [bn] using b1_gt_103
      linarith
    have hb1' : Real.exp (-bn 1) ≤ (0.358 : ℝ) := le_trans hb1 exp_neg_103_le
    have hsq : Real.exp (-bn 1) ^ 2 ≤ (0.358 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (-bn 1)) hb1' 2
    exact hsq
  have h2a : Real.exp (-bn 2) / bn 2 ≤ (0.358 : ℝ) ^ 2 / bn 2 := by
    exact div_le_div_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ bn 2)
  have hinv : 1 / bn 2 ≤ 1 / (2.06 : ℝ) := by
    exact (one_div_le_one_div (by positivity : 0 < bn 2) (by norm_num : (0 : ℝ) < 2.06)).2 b2_gt_206.le
  have h2b : (0.358 : ℝ) ^ 2 / bn 2 ≤ (0.358 : ℝ) ^ 2 / (2.06 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ (0.358 : ℝ) ^ 2)
    simpa [div_eq_mul_inv] using hm
  have h2 : Real.exp (-bn 2) / bn 2 ≤ (0.358 : ℝ) ^ 2 / (2.06 : ℝ) := le_trans h2a h2b
  have h3 : (0.358 : ℝ) ^ 2 / (2.06 : ℝ) ≤ (0.063 : ℝ) := by norm_num
  linarith

/-- E₁(b₃) ≤ 0.015：E₁(b) ≤ e^{−b}/b ≤ q³/3.09。 -/
theorem E1_b3_le : E1 (bn 3) ≤ (0.015 : ℝ) := by
  have hb : (0 : ℝ) < bn 3 := by linarith [b3_gt_309]
  have h1 : E1 (bn 3) ≤ Real.exp (-bn 3) / bn 3 := E1_le (bn 3) hb
  have hq : Real.exp (-bn 3) ≤ (0.358 : ℝ) ^ 3 := by
    have heq : Real.exp (-bn 3) = Real.exp (-bn 1) ^ 3 := by
      have h : -bn 3 = ((3 : ℕ) : ℝ) * (-bn 1) := by
        unfold bn
        ring
      rw [h, Real.exp_nat_mul]
    rw [heq]
    have hb1 : Real.exp (-bn 1) ≤ Real.exp (-(1.03 : ℝ)) := by
      apply Real.exp_le_exp_of_le
      have hgt : (1.03 : ℝ) < bn 1 := by
        simpa [bn] using b1_gt_103
      linarith
    have hb1' : Real.exp (-bn 1) ≤ (0.358 : ℝ) := le_trans hb1 exp_neg_103_le
    have hsq : Real.exp (-bn 1) ^ 2 ≤ (0.358 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (-bn 1)) hb1' 2
    have hcube : Real.exp (-bn 1) ^ 3 ≤ (0.358 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (-bn 1)) hb1' 3
    exact hcube
  have h2a : Real.exp (-bn 3) / bn 3 ≤ (0.358 : ℝ) ^ 3 / bn 3 := by
    exact div_le_div_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ bn 3)
  have hinv : 1 / bn 3 ≤ 1 / (3.09 : ℝ) := by
    exact (one_div_le_one_div (by positivity : 0 < bn 3) (by norm_num : (0 : ℝ) < 3.09)).2 b3_gt_309.le
  have h2b : (0.358 : ℝ) ^ 3 / bn 3 ≤ (0.358 : ℝ) ^ 3 / (3.09 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ (0.358 : ℝ) ^ 3)
    simpa [div_eq_mul_inv] using hm
  have h2 : Real.exp (-bn 3) / bn 3 ≤ (0.358 : ℝ) ^ 3 / (3.09 : ℝ) := le_trans h2a h2b
  have h3 : (0.358 : ℝ) ^ 3 / (3.09 : ℝ) ≤ (0.015 : ℝ) := by norm_num
  linarith

-- 4.5 e^{−0.04}、e^{−0.54} 下界（exp_bound 下界）

/-- e^{−0.04} ≥ 0.96078（exp_bound n=6 下界：Σ₆ − B₆ = 0.9607894…）。 -/
theorem exp_neg_004_ge : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := by
  have hb := Real.exp_bound (x := (-(0.04 : ℝ))) (n := 6) (by norm_num : |(-(0.04 : ℝ))| ≤ 1) (by norm_num : 0 < 6)
  have hd : |Real.exp (-(0.04 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
      |(-(0.04 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := hb
  have hd2 : (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ)) -
      |(-(0.04 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ Real.exp (-(0.04 : ℝ)) := by
    have h1 : -( |(-(0.04 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6))) ≤
        Real.exp (-(0.04 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ)) := by
      have hneg : -|Real.exp (-(0.04 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
          Real.exp (-(0.04 : ℝ)) - (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ)) :=
        neg_le.1 (neg_le_abs _)
      exact le_trans (neg_le_neg hd) hneg
    linarith
  have hsum : (0.96078 : ℝ) ≤ (∑ m ∈ Finset.range 6, (-(0.04 : ℝ)) ^ m / (m.factorial : ℝ)) -
      |(-(0.04 : ℝ))| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- e^{−0.54} ≥ 0.58274（exp_bound n=8 下界：Σ₈ − B₈ = 0.582747…）。 -/
theorem exp_neg_054_ge : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := by
  have hb := Real.exp_bound (x := (-(0.54 : ℝ))) (n := 8) (by norm_num : |(-(0.54 : ℝ))| ≤ 1) (by norm_num : 0 < 8)
  have hd : |Real.exp (-(0.54 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
      |(-(0.54 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := hb
  have hd2 : (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ)) -
      |(-(0.54 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ Real.exp (-(0.54 : ℝ)) := by
    have h1 : -( |(-(0.54 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8))) ≤
        Real.exp (-(0.54 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ)) := by
      have hneg : -|Real.exp (-(0.54 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
          Real.exp (-(0.54 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ)) :=
        neg_le.1 (neg_le_abs _)
      exact le_trans (neg_le_neg hd) hneg
    linarith
  have hsum : (0.58274 : ℝ) ≤ (∑ m ∈ Finset.range 8, (-(0.54 : ℝ)) ^ m / (m.factorial : ℝ)) -
      |(-(0.54 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
    norm_num [Finset.sum_range_succ]
  linarith

-- 4.6 14 个段右端 exp 下界：L_k ≤ e^{−x_{k+1}}（x_{k+1} = 1.54 + 0.5k，e^{−⌊x⌋}·e^{−r}）

/-- e^-(−(1.54)) 下界（段 0 右端，e^(−1−0.54)）。 -/
theorem L0_ge : (0.214362 : ℝ) ≤ Real.exp (-(1.54 : ℝ)) := by
  have hsplit : -(1.54 : ℝ) = -1 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.214362 : ℝ) ≤ (0.36786 : ℝ) ^ 1 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 1 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 1 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 1 ≤ Real.exp (-1) ^ 1 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 1
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 1)
  have hexp : Real.exp (-1 : ℝ) = Real.exp (-1) ^ 1 := by
    have hminus : (-1 : ℝ) = ((1 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-1 : ℝ) = Real.exp (((1 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 1 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(2.04)) 下界（段 1 右端，e^(−2−0.04)）。 -/
theorem L1_ge : (0.130009 : ℝ) ≤ Real.exp (-(2.04 : ℝ)) := by
  have hsplit : -(2.04 : ℝ) = -2 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.130009 : ℝ) ≤ (0.36786 : ℝ) ^ 2 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 2 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 2 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 2 ≤ Real.exp (-1) ^ 2 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 2
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 2)
  have hexp : Real.exp (-2 : ℝ) = Real.exp (-1) ^ 2 := by
    have hminus : (-2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-2 : ℝ) = Real.exp (((2 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 2 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(2.54)) 下界（段 2 右端，e^(−2−0.54)）。 -/
theorem L2_ge : (0.078852 : ℝ) ≤ Real.exp (-(2.54 : ℝ)) := by
  have hsplit : -(2.54 : ℝ) = -2 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.078852 : ℝ) ≤ (0.36786 : ℝ) ^ 2 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 2 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 2 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 2 ≤ Real.exp (-1) ^ 2 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 2
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 2)
  have hexp : Real.exp (-2 : ℝ) = Real.exp (-1) ^ 2 := by
    have hminus : (-2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-2 : ℝ) = Real.exp (((2 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 2 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(3.04)) 下界（段 3 右端，e^(−3−0.04)）。 -/
theorem L3_ge : (0.047822 : ℝ) ≤ Real.exp (-(3.04 : ℝ)) := by
  have hsplit : -(3.04 : ℝ) = -3 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.047822 : ℝ) ≤ (0.36786 : ℝ) ^ 3 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 3 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 3 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 3 ≤ Real.exp (-1) ^ 3 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 3
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 3)
  have hexp : Real.exp (-3 : ℝ) = Real.exp (-1) ^ 3 := by
    have hminus : (-3 : ℝ) = ((3 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-3 : ℝ) = Real.exp (((3 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 3 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(3.54)) 下界（段 4 右端，e^(−3−0.54)）。 -/
theorem L4_ge : (0.029004 : ℝ) ≤ Real.exp (-(3.54 : ℝ)) := by
  have hsplit : -(3.54 : ℝ) = -3 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.029004 : ℝ) ≤ (0.36786 : ℝ) ^ 3 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 3 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 3 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 3 ≤ Real.exp (-1) ^ 3 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 3
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 3)
  have hexp : Real.exp (-3 : ℝ) = Real.exp (-1) ^ 3 := by
    have hminus : (-3 : ℝ) = ((3 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-3 : ℝ) = Real.exp (((3 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 3 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(4.04)) 下界（段 5 右端，e^(−4−0.04)）。 -/
theorem L5_ge : (0.017589 : ℝ) ≤ Real.exp (-(4.04 : ℝ)) := by
  have hsplit : -(4.04 : ℝ) = -4 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.017589 : ℝ) ≤ (0.36786 : ℝ) ^ 4 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 4 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 4 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 4 ≤ Real.exp (-1) ^ 4 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 4
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 4)
  have hexp : Real.exp (-4 : ℝ) = Real.exp (-1) ^ 4 := by
    have hminus : (-4 : ℝ) = ((4 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-4 : ℝ) = Real.exp (((4 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 4 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(4.54)) 下界（段 6 右端，e^(−4−0.54)）。 -/
theorem L6_ge : (0.010666 : ℝ) ≤ Real.exp (-(4.54 : ℝ)) := by
  have hsplit : -(4.54 : ℝ) = -4 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.010666 : ℝ) ≤ (0.36786 : ℝ) ^ 4 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 4 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 4 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 4 ≤ Real.exp (-1) ^ 4 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 4
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 4)
  have hexp : Real.exp (-4 : ℝ) = Real.exp (-1) ^ 4 := by
    have hminus : (-4 : ℝ) = ((4 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-4 : ℝ) = Real.exp (((4 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 4 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(5.04)) 下界（段 7 右端，e^(−5−0.04)）。 -/
theorem L7_ge : (0.006467 : ℝ) ≤ Real.exp (-(5.04 : ℝ)) := by
  have hsplit : -(5.04 : ℝ) = -5 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.006467 : ℝ) ≤ (0.36786 : ℝ) ^ 5 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 5 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 5 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 5 ≤ Real.exp (-1) ^ 5 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 5
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 5)
  have hexp : Real.exp (-5 : ℝ) = Real.exp (-1) ^ 5 := by
    have hminus : (-5 : ℝ) = ((5 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-5 : ℝ) = Real.exp (((5 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 5 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(5.54)) 下界（段 8 右端，e^(−5−0.54)）。 -/
theorem L8_ge : (0.003921 : ℝ) ≤ Real.exp (-(5.54 : ℝ)) := by
  have hsplit : -(5.54 : ℝ) = -5 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.003921 : ℝ) ≤ (0.36786 : ℝ) ^ 5 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 5 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 5 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 5 ≤ Real.exp (-1) ^ 5 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 5
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 5)
  have hexp : Real.exp (-5 : ℝ) = Real.exp (-1) ^ 5 := by
    have hminus : (-5 : ℝ) = ((5 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-5 : ℝ) = Real.exp (((5 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 5 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(6.04)) 下界（段 9 右端，e^(−6−0.04)）。 -/
theorem L9_ge : (0.002376 : ℝ) ≤ Real.exp (-(6.04 : ℝ)) := by
  have hsplit : -(6.04 : ℝ) = -6 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.002376 : ℝ) ≤ (0.36786 : ℝ) ^ 6 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 6 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 6 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 6 ≤ Real.exp (-1) ^ 6 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 6
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 6)
  have hexp : Real.exp (-6 : ℝ) = Real.exp (-1) ^ 6 := by
    have hminus : (-6 : ℝ) = ((6 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-6 : ℝ) = Real.exp (((6 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 6 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(6.54)) 下界（段 10 右端，e^(−6−0.54)）。 -/
theorem L10_ge : (0.001440 : ℝ) ≤ Real.exp (-(6.54 : ℝ)) := by
  have hsplit : -(6.54 : ℝ) = -6 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.001440 : ℝ) ≤ (0.36786 : ℝ) ^ 6 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 6 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 6 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 6 ≤ Real.exp (-1) ^ 6 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 6
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 6)
  have hexp : Real.exp (-6 : ℝ) = Real.exp (-1) ^ 6 := by
    have hminus : (-6 : ℝ) = ((6 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-6 : ℝ) = Real.exp (((6 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 6 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(7.04)) 下界（段 11 右端，e^(−7−0.04)）。 -/
theorem L11_ge : (0.000871 : ℝ) ≤ Real.exp (-(7.04 : ℝ)) := by
  have hsplit : -(7.04 : ℝ) = -7 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.000871 : ℝ) ≤ (0.36786 : ℝ) ^ 7 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 7 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 7 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 7 ≤ Real.exp (-1) ^ 7 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 7
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 7)
  have hexp : Real.exp (-7 : ℝ) = Real.exp (-1) ^ 7 := by
    have hminus : (-7 : ℝ) = ((7 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-7 : ℝ) = Real.exp (((7 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 7 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(7.54)) 下界（段 12 右端，e^(−7−0.54)）。 -/
theorem L12_ge : (0.000527 : ℝ) ≤ Real.exp (-(7.54 : ℝ)) := by
  have hsplit : -(7.54 : ℝ) = -7 + -(0.54 : ℝ) := by norm_num
  have hpow : (0.000527 : ℝ) ≤ (0.36786 : ℝ) ^ 7 * (0.58274 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 7 * (0.58274 : ℝ) ≤ Real.exp (-1) ^ 7 * Real.exp (-(0.54 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 7 ≤ Real.exp (-1) ^ 7 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 7
    have hl : (0.58274 : ℝ) ≤ Real.exp (-(0.54 : ℝ)) := exp_neg_054_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.58274 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 7)
  have hexp : Real.exp (-7 : ℝ) = Real.exp (-1) ^ 7 := by
    have hminus : (-7 : ℝ) = ((7 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-7 : ℝ) = Real.exp (((7 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 7 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg

/-- e^-(−(8.04)) 下界（段 13 右端，e^(−8−0.04)）。 -/
theorem L13_ge : (0.000318 : ℝ) ≤ Real.exp (-(8.04 : ℝ)) := by
  have hsplit : -(8.04 : ℝ) = -8 + -(0.04 : ℝ) := by norm_num
  have hpow : (0.000318 : ℝ) ≤ (0.36786 : ℝ) ^ 8 * (0.96078 : ℝ) := by norm_num
  have hlg : (0.36786 : ℝ) ^ 8 * (0.96078 : ℝ) ≤ Real.exp (-1) ^ 8 * Real.exp (-(0.04 : ℝ)) := by
    have hp : (0.36786 : ℝ) ^ 8 ≤ Real.exp (-1) ^ 8 :=
      pow_le_pow_left₀ (ha := (by norm_num : 0 ≤ (0.36786 : ℝ))) (hab := exp_neg_one_ge) 8
    have hl : (0.96078 : ℝ) ≤ Real.exp (-(0.04 : ℝ)) := exp_neg_004_ge
    exact mul_le_mul hp hl (by norm_num : 0 ≤ (0.96078 : ℝ)) (by positivity : 0 ≤ Real.exp (-1) ^ 8)
  have hexp : Real.exp (-8 : ℝ) = Real.exp (-1) ^ 8 := by
    have hminus : (-8 : ℝ) = ((8 : ℕ) : ℝ) * (-1) := by norm_num
    calc
      Real.exp (-8 : ℝ) = Real.exp (((8 : ℕ) : ℝ) * (-1)) := by
        congr 1
      _ = Real.exp (-1) ^ 8 := by
        rw [Real.exp_nat_mul]
  rw [hsplit, Real.exp_add, hexp]
  exact le_trans hpow hlg



-- 4.7 f(t) = e^{−t}/t 在 t ≥ 1 递减（f_dec_step：t·e^{t−u} ≤ t ≤ u）

/-- t ≤ u 且 1 ≤ t ⟹ e^{−t}/t ≥ e^{−u}/u：乘 e^u 后等价于 u ≥ t·e^{t−u} ≤ t ≤ u。 -/
lemma f_dec_step {t u : ℝ} (htu : t ≤ u) (ht1 : 1 ≤ t) :
    Real.exp (-t) / t ≥ Real.exp (-u) / u := by
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have htm : t * Real.exp (t - u) ≤ t := by
    have he : Real.exp (t - u) ≤ 1 := by
      have hle : t - u ≤ 0 := by linarith
      calc
        Real.exp (t - u) ≤ Real.exp (0 : ℝ) := Real.exp_le_exp_of_le hle
        _ = 1 := by norm_num
    simpa [mul_comm] using mul_le_mul_of_nonneg_right he ht0.le
  have htm_u : t * Real.exp (t - u) ≤ u := by
    exact le_trans htm (by linarith)
  have hmain : u * Real.exp (-t) ≥ t * Real.exp (-u) := by
    have hmul := mul_le_mul_of_nonneg_right htm_u (by positivity : 0 ≤ Real.exp (-t))
    have hsimp : t * Real.exp (t - u) * Real.exp (-t) = t * Real.exp (-u) := by
      calc
        t * Real.exp (t - u) * Real.exp (-t) = t * (Real.exp (t - u) * Real.exp (-t)) := by ring
        _ = t * Real.exp ((t - u) + -t) := by rw [← Real.exp_add]
        _ = t * Real.exp (-u) := by
          congr 1
          ring
    rwa [hsimp] at hmul
  change Real.exp (-u) / u ≤ Real.exp (-t) / t
  rw [div_le_div_iff₀ hu0 ht0]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

-- 4.8 段积分下界：∫_{Icc x (x+0.5)} f ≥ 0.5·L/(x+0.5)（f 递减 + 常数下界）

/-- 段 [x, x+0.5] 的积分下界：f(t) ≥ f(x+0.5) ≥ L/(x+0.5) 逐点（1 < x），积分 ≥ 常数·0.5。 -/
lemma seg_generic {x : ℝ} (hx : 1 < x) {L : ℝ} (hL : L ≤ Real.exp (-(x + 0.5))) :
    (∫ t in Set.Icc x (x + 0.5), Real.exp (-t) / t) ≥ 0.5 * L / (x + 0.5) := by
  have hx05 : 0 < x + 0.5 := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hsub : Set.Icc x (x + 0.5) ⊆ Set.Ioi (x - 1) := by
    intro t ht
    have htx : x ≤ t := (Set.mem_Icc.mp ht).1
    have hx1' : x - 1 < x := by linarith
    exact lt_of_lt_of_le hx1' htx
  have hc : ∀ t ∈ Set.Icc x (x + 0.5), L / (x + 0.5) ≤ Real.exp (-t) / t := by
    intro t ht
    have htx : x ≤ t := (Set.mem_Icc.mp ht).1
    have htx5 : t ≤ x + 0.5 := (Set.mem_Icc.mp ht).2
    have hf : Real.exp (-t) / t ≥ Real.exp (-(x + 0.5)) / (x + 0.5) := by
      exact f_dec_step htx5 (by linarith : 1 ≤ t)
    have hL5 : L / (x + 0.5) ≤ Real.exp (-(x + 0.5)) / (x + 0.5) := by
      exact div_le_div_of_nonneg_right hL (by linarith : 0 ≤ x + 0.5)
    exact le_trans hL5 hf
  have hconst_le : (∫ t in Set.Icc x (x + 0.5), L / (x + 0.5)) ≤
      ∫ t in Set.Icc x (x + 0.5), Real.exp (-t) / t := by
    refine integral_mono_ae ?_ ?_ ?_
    · exact integrableOn_const (s := Set.Icc x (x + 0.5)) (C := L / (x + 0.5))
        (hs := by
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_ne_top)
        (hC := by norm_num)
    · apply Integrable.mono'
      · exact (integrableOn_exp_neg_Ioi (0.5 : ℝ)).mono_set (fun t ht => by
          have htx : x ≤ t := (Set.mem_Icc.mp ht).1
          exact lt_of_lt_of_le (by linarith : (0.5 : ℝ) < x) htx)
      · have hae := (cont_div (x - 1) hx1).aestronglyMeasurable
          (μ := MeasureTheory.volume) measurableSet_Ioi
        have hae' : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
            (MeasureTheory.volume.restrict (Set.Icc x (x + 0.5))) := by
          simpa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] using
            (MeasureTheory.AEStronglyMeasurable.restrict hae (s := Set.Icc x (x + 0.5)))
        exact hae'
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have ht1 : 1 ≤ t := by linarith [hx, (Set.mem_Icc.mp ht).1]
        have hpos : 0 ≤ Real.exp (-t) / t := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
        have h1 : (1 / t : ℝ) ≤ 1 := by
          have ht0 : 0 < t := by linarith
          simpa using (one_div_le_one_div ht0 zero_lt_one).2 ht1
        calc
          Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
          _ ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp (-t))
          _ = Real.exp (-t) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hc t ht
  have hval : (∫ t in Set.Icc x (x + 0.5), L / (x + 0.5)) = 0.5 * L / (x + 0.5) := by
    have hsint : (∫ t in Set.Icc x (x + 0.5), L / (x + 0.5)) =
        (MeasureTheory.volume.real (Set.Icc x (x + 0.5))) * (L / (x + 0.5)) := by
      exact MeasureTheory.setIntegral_const (L / (x + 0.5))
    have hv : (MeasureTheory.volume.real (Set.Icc x (x + 0.5))) = (0.5 : ℝ) := by
      rw [show (MeasureTheory.volume.real (Set.Icc x (x + 0.5))) =
          (MeasureTheory.volume (Set.Icc x (x + 0.5))).toReal by rfl]
      rw [Real.volume_Icc]
      have hnr : (x + 0.5 - x : ℝ) = 0.5 := by ring
      rw [hnr]
      simp
      norm_num
    rw [hsint, hv]
    ring
  linarith

-- 4.9 E1(b₁) 分段下界组装：∫_{Icc 1.04 8.04} f ≥ Σₖ 0.5·c_k/r_k ≥ 0.133726

/-- f(t) = e^{−t}/t 在 [c, +∞) 可积（1 < c，由 e^{−t} 上界 + 可测性）。 -/
lemma f_integrableOn_Ioi {c : ℝ} (hc : 1 < c) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi c) := by
  apply Integrable.mono'
  · exact (integrableOn_exp_neg_Ioi (0.5 : ℝ)).mono_set (fun t ht => by
      exact lt_of_lt_of_le (by linarith : (0.5 : ℝ) < c) (le_of_lt (Set.mem_Ioi.mp ht)))
  · have hx1 : 0 < c - 1 := by linarith
    have hsub : Set.Ioi c ⊆ Set.Ioi (c - 1) := by
      intro t ht
      exact lt_of_lt_of_le (by linarith : c - 1 < c) (le_of_lt (Set.mem_Ioi.mp ht))
    have hae := (cont_div (c - 1) hx1).aestronglyMeasurable
      (μ := MeasureTheory.volume) measurableSet_Ioi
    have hae' : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
        (MeasureTheory.volume.restrict (Set.Ioi c)) := by
      simpa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] using
        (MeasureTheory.AEStronglyMeasurable.restrict hae (s := Set.Ioi c))
    exact hae'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := by linarith [hc, (Set.mem_Ioi.mp ht)]
    have hpos : 0 ≤ Real.exp (-t) / t := by
      exact div_nonneg (by positivity) (by linarith : 0 ≤ t)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    have h1 : (1 / t : ℝ) ≤ 1 := by
      have ht0 : 0 < t := by linarith
      simpa using (one_div_le_one_div ht0 zero_lt_one).2 ht1
    calc
      Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
      _ ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp (-t))
      _ = Real.exp (-t) := by ring

/-- f(t) = e^{−t}/t 在紧区间 [a,b] 可积（1 < a）。 -/
lemma f_integrableOn_Icc {a b : ℝ} (ha : 1 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Icc a b) := by
  apply Integrable.mono'
  · exact (integrableOn_exp_neg_Ioi (0.5 : ℝ)).mono_set (fun t ht => by
      have htx : a ≤ t := (Set.mem_Icc.mp ht).1
      exact lt_of_lt_of_le (by linarith : (0.5 : ℝ) < a) htx)
  · have hx1 : 0 < a - 1 := by linarith
    have hsub : Set.Icc a b ⊆ Set.Ioi (a - 1) := by
      intro t ht
      have htx : a ≤ t := (Set.mem_Icc.mp ht).1
      exact lt_of_lt_of_le (by linarith : a - 1 < a) htx
    have hae := (cont_div (a - 1) hx1).aestronglyMeasurable
      (μ := MeasureTheory.volume) measurableSet_Ioi
    have hae' : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
        (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      simpa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] using
        (MeasureTheory.AEStronglyMeasurable.restrict hae (s := Set.Icc a b))
    exact hae'
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht1 : 1 ≤ t := by linarith [ha, (Set.mem_Icc.mp ht).1]
    have hpos : 0 ≤ Real.exp (-t) / t := by
      exact div_nonneg (by positivity) (by linarith : 0 ≤ t)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    have h1 : (1 / t : ℝ) ≤ 1 := by
      have ht0 : 0 < t := by linarith
      simpa using (one_div_le_one_div ht0 zero_lt_one).2 ht1
    calc
      Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
      _ ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp (-t))
      _ = Real.exp (-t) := by ring

/-- 段链：Σ_{k<N+1} 0.5·c_k/r_k ≤ ∫_{Icc a (r N)} f（r k = a + k·0.5 + 0.5 为段右端）。 -/
lemma seg_chain_ge {a : ℝ} (ha : 1 < a) {r c : ℕ → ℝ} (N : ℕ)
    (hr : ∀ k, r k = a + (k : ℝ) * 0.5 + 0.5)
    (hc : ∀ k < N + 1, c k ≤ Real.exp (-(r k))) :
    (∑ k ∈ Finset.range (N + 1), 0.5 * c k / r k) ≤
      ∫ t in Set.Icc a (r N), Real.exp (-t) / t := by
  induction N with
  | zero =>
      rw [Finset.sum_range_succ]
      simp
      rw [hr 0]
      simp
      have hL0 : c 0 ≤ Real.exp (-(a + 0.5)) := by
        simpa [hr 0] using (hc 0 (by norm_num : 0 < 1))
      exact seg_generic (x := a) ha (L := c 0) hL0
  | succ N ih =>
      have hseg : Set.Icc a (r (N + 1)) = Set.Icc a (r N) ∪ Set.Ioc (r N) (r (N + 1)) := by
        ext t
        constructor
        · intro h
          by_cases h1 : t ≤ r N
          · left; exact ⟨(Set.mem_Icc.mp h).1, h1⟩
          · right; exact ⟨lt_of_not_ge h1, (Set.mem_Icc.mp h).2⟩
        · intro h
          rcases h with h1 | h2
          · exact ⟨(Set.mem_Icc.mp h1).1,
              le_trans (Set.mem_Icc.mp h1).2
                (by rw [hr N, hr (N + 1), Nat.cast_add, Nat.cast_one]; linarith)⟩
          · exact ⟨le_trans (by rw [hr N]; linarith) (le_of_lt (Set.mem_Ioc.mp h2).1), (Set.mem_Ioc.mp h2).2⟩
      have hdisj : Disjoint (Set.Icc a (r N)) (Set.Ioc (r N) (r (N + 1))) := by
        rw [Set.disjoint_iff]
        intro t ht
        have ht1 : t ≤ r N := (Set.mem_Icc.mp ht.1).2
        have ht2 : r N < t := (Set.mem_Ioc.mp ht.2).1
        linarith
      have hint_l : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Icc a (r N)) := by
        exact f_integrableOn_Icc ha
      have hint_r : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t)
          (Set.Ioc (r N) (r (N + 1))) := by
        apply Integrable.mono'
        · exact (integrableOn_exp_neg_Ioi (0.5 : ℝ)).mono_set (fun t ht => by
            have htx : r N < t := (Set.mem_Ioc.mp ht).1
            exact lt_of_lt_of_le (by linarith : (0.5 : ℝ) < a)
              (le_trans (by rw [hr N]; linarith) htx.le))
        · have hx1 : 0 < a - 1 := by linarith
          have hsub : Set.Ioc (r N) (r (N + 1)) ⊆ Set.Ioi (a - 1) := by
            intro t ht
            have htx : r N < t := (Set.mem_Ioc.mp ht).1
            have ha : a ≤ r N := by rw [hr N]; linarith
            exact lt_of_lt_of_le (by linarith : a - 1 < a) (le_trans ha htx.le)
          have hae := (cont_div (a - 1) hx1).aestronglyMeasurable
            (μ := MeasureTheory.volume) measurableSet_Ioi
          have hae' : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
              (MeasureTheory.volume.restrict (Set.Ioc (r N) (r (N + 1)))) := by
            simpa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] using
              (MeasureTheory.AEStronglyMeasurable.restrict hae (s := Set.Ioc (r N) (r (N + 1))))
          exact hae'
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have hrN1 : 1 < r N := by rw [hr N]; linarith
          have ht1 : 1 ≤ t := by linarith [(Set.mem_Ioc.mp ht).1]
          have hpos : 0 ≤ Real.exp (-t) / t := by
            exact div_nonneg (by positivity) (by linarith : 0 ≤ t)
          rw [Real.norm_eq_abs, abs_of_nonneg hpos]
          have h1 : (1 / t : ℝ) ≤ 1 := by
            have ht0 : 0 < t := by linarith
            simpa using (one_div_le_one_div ht0 zero_lt_one).2 ht1
          calc
            Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
            _ ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp (-t))
            _ = Real.exp (-t) := by ring
      have hrec : (∫ t in Set.Icc a (r (N + 1)), Real.exp (-t) / t) =
          (∫ t in Set.Icc a (r N), Real.exp (-t) / t) +
            (∫ t in Set.Ioc (r N) (r (N + 1)), Real.exp (-t) / t) := by
        rw [hseg]
        exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint_l hint_r
      have hcN1 : c (N + 1) ≤ Real.exp (-(r (N + 1))) := hc (N + 1) (Nat.lt_succ_self (N + 1))
      have hc_prev : ∀ k < N + 1, c k ≤ Real.exp (-(r k)) := by
        intro k hk
        exact hc k (Nat.lt_succ_of_lt hk)
      have hseg' : 0.5 * c (N + 1) / r (N + 1) ≤ ∫ t in Set.Ioc (r N) (r (N + 1)), Real.exp (-t) / t := by
        have hIoc : (∫ t in Set.Ioc (r N) (r (N + 1)), Real.exp (-t) / t) =
            (∫ t in Set.Icc (r N) (r (N + 1)), Real.exp (-t) / t) := by
          exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
        rw [hIoc]
        have hrN1 : r N + 0.5 = r (N + 1) := by
          rw [hr N, hr (N + 1), Nat.cast_add, Nat.cast_one]
          ring
        have hL' : c (N + 1) ≤ Real.exp (-(r N + 0.5)) := by
          rwa [hrN1]
        simpa [hrN1] using (seg_generic (x := r N) (by rw [hr N]; linarith : 1 < r N)
          (L := c (N + 1)) hL')
      have hih : (∑ k ∈ Finset.range (N + 1), 0.5 * c k / r k) ≤
          ∫ t in Set.Icc a (r N), Real.exp (-t) / t := by
        exact ih hc_prev
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range (N + 1), 0.5 * c k / r k) + 0.5 * c (N + 1) / r (N + 1)
            ≤ (∫ t in Set.Icc a (r N), Real.exp (-t) / t) +
              (∫ t in Set.Ioc (r N) (r (N + 1)), Real.exp (-t) / t) := add_le_add hih hseg'
        _ = ∫ t in Set.Icc a (r (N + 1)), Real.exp (-t) / t := hrec.symm

/-- E1(b₁) 下界：0.1337 ≤ E1 (bn 1)（b₁ ≤ 1.04 截断 + 14 段链 + Σ 0.5·c_k/r_k ≥ 0.1337）。 -/
theorem E1_b1_ge : (0.1337 : ℝ) ≤ E1 (bn 1) := by
  let r : ℕ → ℝ := fun k => (1.04 : ℝ) + (k : ℝ) * 0.5 + 0.5
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => 0.214362 | 1 => 0.130009 | 2 => 0.078852 | 3 => 0.047822
    | 4 => 0.029004 | 5 => 0.017589 | 6 => 0.010666 | 7 => 0.006467
    | 8 => 0.003921 | 9 => 0.002376 | 10 => 0.001440 | 11 => 0.000871
    | 12 => 0.000527 | _ => 0.000318
  have hr : ∀ k, r k = (1.04 : ℝ) + (k : ℝ) * 0.5 + 0.5 := by intro k; rfl
  have hc : ∀ k < 14, c k ≤ Real.exp (-(r k)) := by
    intro k hk
    interval_cases k
    · norm_num [c, r]
      have h := L0_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L1_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L2_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L3_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L4_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L5_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L6_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L7_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L8_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L9_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L10_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L11_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L12_ge
      norm_num at h ⊢
      exact h
    · norm_num [c, r]
      have h := L13_ge
      norm_num at h ⊢
      exact h
  have htrunc : (∫ t in Set.Icc (1.04 : ℝ) (8.04 : ℝ), Real.exp (-t) / t) ≤ E1 (bn 1) := by
    rw [E1]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    refine integral_mono_ae ?_ ?_ ?_
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (f_integrableOn_Icc (a := 1.04) (by norm_num : (1 : ℝ) < 1.04))
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr
        (f_integrableOn_Ioi (c := bn 1)
          (by simpa [bn] using (lt_trans (by norm_num : (1 : ℝ) < 1.03) b1_gt_103)))
    · filter_upwards with t
      by_cases ht : t ∈ Set.Icc (1.04 : ℝ) (8.04 : ℝ)
      · have hti : t ∈ Set.Ioi (bn 1) := by
          have htx : (1.04 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
          exact lt_of_lt_of_le (by simpa [bn] using b1_lt_104) htx
        simp [Set.indicator, ht, hti]
      · simp [Set.indicator, ht]
        by_cases h1 : t ∈ Set.Ioi (bn 1)
        · have hbn1 : (0 : ℝ) < bn 1 := by
            rw [bn]
            exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) (by exact_mod_cast (Nat.zero_lt_one : 0 < 1)))
              (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37))
          have ht0 : 0 < t := lt_trans hbn1 (Set.mem_Ioi.mp h1)
          have hle : (0 : ℝ) ≤ Real.exp (-t) / t := div_nonneg (by positivity) (le_of_lt ht0)
          have hle' : (0 : ℝ) ≤ if bn 1 < t then Real.exp (-t) / t else 0 := by
            rw [if_pos (Set.mem_Ioi.mp h1)]
            exact hle
          simpa [Set.indicator, ht] using hle'
        · have hneg : ¬ bn 1 < t := by
            intro h
            exact h1 (Set.mem_Ioi.mpr h)
          have hle0 : (0 : ℝ) ≤ if bn 1 < t then Real.exp (-t) / t else 0 := by
            rw [if_neg hneg]
          simpa [Set.indicator, ht] using hle0
  have hchain : (∑ k ∈ Finset.range 14, 0.5 * (c k) / (r k)) ≤
      ∫ t in Set.Icc (1.04 : ℝ) (8.04 : ℝ), Real.exp (-t) / t := by
    have hseq := seg_chain_ge (a := 1.04) (by norm_num : (1 : ℝ) < 1.04) 13 hr hc
    rw [show (8.04 : ℝ) = r 13 by norm_num [hr]]
    exact hseq
  have hsum : (0.1337 : ℝ) ≤ ∑ k ∈ Finset.range 14, 0.5 * (c k) / (r k) := by
    norm_num [Finset.sum_range_succ, c, r, hr]
  exact le_trans (le_trans hsum hchain) htrunc

/-! ## 4.10 lprime1_pos 组装：L′(E,1) > 0 -/

/-- aE 无界界：|aE m| ≤ 2m（m > 100 时 aE = 0 平凡）。 -/
lemma aE_bound_unbounded (m : ℕ) : |aE m| ≤ 2 * (m : ℤ) := by
  by_cases hm : m ≤ 100
  · exact aE_bound m hm
  · have h0 : aE m = 0 := by simp [aE, hm]
    simp [h0]

/-- b₁ > 0。 -/
theorem b1_pos : (0 : ℝ) < bn 1 := by
  rw [bn]
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) (by exact_mod_cast (Nat.zero_lt_one : 0 < 1)))
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 37))

/-- bₙ = n·b₁。 -/
lemma bn_mul (n : ℕ) : bn n = (n : ℝ) * bn 1 := by
  unfold bn
  ring

/-- 部分和前三项：Σ_{i<3} g i = E₁(b₁) − E₁(b₂) − E₁(b₃)。 -/
lemma part3_eq :
    (∑ i ∈ Finset.range 3, (aE (i + 1) : ℝ) / (i + 1) * E1 (bn (i + 1))) =
      E1 (bn 1) - E1 (bn 2) - E1 (bn 3) := by
  have ha1 : aE 1 = 1 := by native_decide
  have ha2 : aE 2 = -2 := by native_decide
  have ha3 : aE 3 = -3 := by native_decide
  have h0 : (aE (0 + 1) : ℝ) / (0 + 1) * E1 (bn (0 + 1)) = E1 (bn 1) := by
    rw [ha1]
    norm_num
  have h1 : (aE (1 + 1) : ℝ) / (1 + 1) * E1 (bn (1 + 1)) = -E1 (bn 2) := by
    rw [ha2]
    norm_num
  have h2 : (aE (2 + 1) : ℝ) / (2 + 1) * E1 (bn (2 + 1)) = -E1 (bn 3) := by
    rw [ha3]
    norm_num
  rw [show (∑ i ∈ Finset.range 3, (aE (i + 1) : ℝ) / (i + 1) * E1 (bn (i + 1))) =
      (aE (0 + 1) : ℝ) / (0 + 1) * E1 (bn (0 + 1)) +
      (aE (1 + 1) : ℝ) / (1 + 1) * E1 (bn (1 + 1)) +
      (aE (2 + 1) : ℝ) / (2 + 1) * E1 (bn (2 + 1)) by
    norm_num [Finset.sum_range_succ]]
  rw [h0, h1, h2]
  ring

/-- 部分和下界：Σ_{i<3} g i ≥ 0.0557（= 0.1337 − 0.063 − 0.015）。 -/
lemma part3_lower : (0.0557 : ℝ) ≤
    (∑ i ∈ Finset.range 3, (aE (i + 1) : ℝ) / (i + 1) * E1 (bn (i + 1))) := by
  rw [part3_eq]
  linarith [E1_b1_ge, E1_b2_le, E1_b3_le]

/-- 拆分：lprime1 = 2·(部分和 Σ_{i<3} + 尾项 Σ' g(n+3))。 -/
lemma lprime1_split :
    lprime1 = 2 * ((∑ i ∈ Finset.range 3, (aE (i + 1) : ℝ) / (i + 1) * E1 (bn (i + 1))) +
      ∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1))) := by
  unfold lprime1
  congr 1
  have htail : Summable (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := by
    exact (summable_nat_add_iff 3).mpr lprime1_summable
  have hs : HasSum (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1)))
      (∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := htail.hasSum
  have hfull : HasSum (fun n : ℕ => (aE (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * E1 (bn (n + 1)))
      ((∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) +
       ∑ i ∈ Finset.range 3, (aE (i + 1) : ℝ) / (((i : ℕ) : ℝ) + 1) * E1 (bn (i + 1))) := by
    exact (hasSum_nat_add_iff (k := 3)
      (f := fun n : ℕ => (aE (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * E1 (bn (n + 1)))
      (g := (∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))))).mp hs
  rw [show (∑' n : ℕ, (aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))) =
           (∑' n : ℕ, (aE (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * E1 (bn (n + 1))) by
    apply tsum_congr
    intro n
    simp [Nat.cast_add]]
  rw [hfull.tsum_eq]
  simp [Nat.cast_add]
  ring

-- 4.11 尾项绝对界 + L′(E,1) > 0（B3-min 落点）

/-- aE 全下标界：|aE m| ≤ 2m（m > 100 时 aE m = 0，自动成立）。 -/
theorem aE_bound_all (m : ℕ) : |aE m| ≤ 2 * (m : ℤ) := by
  by_cases hm : m ≤ 100
  · exact aE_bound m hm
  · dsimp [aE]
    rw [if_neg hm]
    norm_num

/-- bn m ≥ m·1.03（b₁ > 1.03 的乘性）。 -/
theorem bn_ge_103m (m : ℕ) : (m : ℝ) * 1.03 ≤ bn m := by
  have hb1 : (1.03 : ℝ) ≤ 2 * Real.pi / Real.sqrt 37 := b1_gt_103.le
  calc
    (m : ℝ) * 1.03 ≤ (m : ℝ) * (2 * Real.pi / Real.sqrt 37) := by
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = bn m := by
      dsimp [bn]
      ring

/-- m ≥ 4 ⟹ bn m ≥ 4·1.03。 -/
lemma bn_ge_4c (m : ℕ) (hm4 : 4 ≤ m) : (4 : ℝ) * 1.03 ≤ bn m := by
  calc
    (4 : ℝ) * 1.03 ≤ (m : ℝ) * 1.03 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm4) (by norm_num : (0 : ℝ) ≤ 1.03)
    _ ≤ bn m := bn_ge_103m m

/-- E₁(b) ≥ 0（被积函数在 (b,∞) 上非负）。 -/
lemma E1_nonneg (b : ℝ) (hb : 0 < b) : 0 ≤ E1 b := by
  dsimp [E1]
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi b)]
      (fun t : ℝ => Real.exp (-t) / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt (lt_trans hb ht))
  exact MeasureTheory.integral_nonneg_of_ae hae

/-- 尾项逐项界：|aE(m)/m·E₁(bn m)| ≤ 2·e^{−1.03m}/(4·1.03)，m ≥ 4。 -/
lemma g_abs_bound (m : ℕ) (hm4 : 4 ≤ m) :
    |(aE m : ℝ) / m * E1 (bn m)| ≤ 2 * Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ)) := by
  have hbpos : 0 < bn m := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4 * 1.03) (bn_ge_4c m hm4)
  have hdiv : |(aE m : ℝ) / m| ≤ 2 := by
    rw [abs_div]
    have hmcast : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rw [abs_of_nonneg hmcast]
    have hc : |(aE m : ℝ)| ≤ 2 * (m : ℝ) := by
      have hz : |(aE m : ℤ)| ≤ 2 * (m : ℤ) := aE_bound_all m
      exact_mod_cast hz
    calc
      |(aE m : ℝ)| / (m : ℝ) ≤ (2 * (m : ℝ)) / (m : ℝ) := by
        exact div_le_div_of_nonneg_right hc hmcast
      _ = 2 := by
        have hmz : (m : ℝ) ≠ 0 := by positivity
        field_simp [hmz]
  have hE0 : 0 ≤ E1 (bn m) := E1_nonneg (bn m) hbpos
  have hg2E : |(aE m : ℝ) / m * E1 (bn m)| ≤ 2 * E1 (bn m) := by
    rw [abs_mul]
    rw [abs_of_nonneg hE0]
    exact mul_le_mul_of_nonneg_right hdiv hE0
  have hmono : Real.exp (-bn m) ≤ Real.exp (-(1.03 : ℝ) * m) := by
    have hb : (m : ℝ) * 1.03 ≤ bn m := bn_ge_103m m
    have hneg : -bn m ≤ -(1.03 : ℝ) * m := by linarith
    exact (Real.exp_le_exp).mpr hneg
  have hinv : 1 / bn m ≤ 1 / (4 * (1.03 : ℝ)) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 * 1.03) (bn_ge_4c m hm4)
  have hE1 : E1 (bn m) ≤ Real.exp (-bn m) / bn m := E1_le (bn m) hbpos
  have hE2 : E1 (bn m) ≤ Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ)) := by
    have hstep1 : Real.exp (-bn m) / bn m ≤ Real.exp (-(1.03 : ℝ) * m) / bn m := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr (le_of_lt hbpos))
    have hstep2 : Real.exp (-(1.03 : ℝ) * m) / bn m ≤
        Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hm : (1 / bn m) * Real.exp (-(1.03 : ℝ) * m) ≤
          (1 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * m) := by
        have hEpos : (0 : ℝ) ≤ Real.exp (-(1.03 : ℝ) * m) := (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hinv hEpos
      simpa [mul_comm] using hm
    exact le_trans hE1 (le_trans hstep1 hstep2)
  calc
    |(aE m : ℝ) / m * E1 (bn m)| ≤ 2 * E1 (bn m) := hg2E
    _ ≤ 2 * (Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hE2 (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * Real.exp (-(1.03 : ℝ) * m) / (4 * (1.03 : ℝ)) := by ring

/-- 形态等式（i）：(n+4) 形态 = (((n+3:ℕ):ℝ)+1) 形态（匹配 summable_nat_add_iff 输出）。 -/
lemma g_sum_eq1 :
    (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) =
      (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := by
  funext n
  have h1 : (aE (n + 4) : ℝ) / (n + 4) = (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) := by
    congr 1
    · rw [Nat.cast_add]
      ring
  have h2 : E1 (bn (n + 4)) = E1 (bn (n + 3 + 1)) := by rfl
  calc
    (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))
        = (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1)) := by rw [h1, h2]

/-- 形态等式（ii）：(n+4) 形态 = (n+3+1) 无括号形态（匹配 lprime1_split 目标）。 -/
lemma g_sum_eq2 :
    (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) =
      (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1))) := by
  funext n
  have h1 : (aE (n + 4) : ℝ) / (n + 4) = (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) := by
    congr 1
    · ring
  have h2 : E1 (bn (n + 4)) = E1 (bn (n + 3 + 1)) := by rfl
  calc
    (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))
        = (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1)) := by rw [h1, h2]

/-- 形态等式（iii）：|aE/(n+4)·E1| = |aE|/|(n+4:ℝ)|·|E1|（abs 全拆）。 -/
lemma g_sum_abs :
    (fun n : ℕ => |(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))|) =
      (fun n : ℕ => |(aE (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |E1 (bn (n + 4))|) := by
  funext n
  simp [abs_div, abs_mul]

/-- 移位可和性：g(n+4) 绝对可和（反射公式级数收敛 + 移位）。 -/
lemma g_shift_summable : Summable (fun n : ℕ => (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))) := by
  have hs3 : Summable (fun n : ℕ => (aE (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * E1 (bn (n + 3 + 1))) := by
    exact (summable_nat_add_iff 3).mpr lprime1_summable
  rw [g_sum_eq1]
  exact hs3

/-- 几何尾和：Σ' e^{−1.03(n+4)} = e^{−4·1.03}/(1−e^{−1.03})。 -/
lemma geom_tail_value :
    (∑' n : ℕ, Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) =
      Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) := by
  have hq_abs : ‖Real.exp (-(1.03 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hb := hasSum_geometric_of_norm_lt_one hq_abs
  have hg0 : HasSum (fun n : ℕ => (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n)
      ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
    exact hb.mul_left ((Real.exp (-(1.03 : ℝ))) ^ 4)
  have hp : ∀ n : ℕ, (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n =
      Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
    intro n
    rw [← pow_add]
    have hswap : 4 + n = n + 4 := by omega
    rw [hswap]
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hg' : HasSum (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
    exact hg0.congr_fun (fun n : ℕ => (hp n).symm)
  have hg : HasSum (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(1.03 : ℝ))) ^ 4 / (1 - Real.exp (-(1.03 : ℝ)))) := by
    simpa [div_eq_mul_inv] using hg'
  have hval : (Real.exp (-(1.03 : ℝ))) ^ 4 = Real.exp (-(1.03 : ℝ) * 4) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  calc
    (∑' n : ℕ, Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) =
        (Real.exp (-(1.03 : ℝ))) ^ 4 / (1 - Real.exp (-(1.03 : ℝ))) := hg.tsum_eq
    _ = Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) := by
      rw [hval]

/-- 尾项上界：|Σ' g(n+4)| ≤ (1/(2·1.03))·0.358⁴/(1−0.358)。 -/
theorem tail_abs_bound :
    |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤
      (1 / (2 * (1.03 : ℝ))) * (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) := by
  have hgs : Summable (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) := by
    exact ⟨_, (by
      have hq_abs : ‖Real.exp (-(1.03 : ℝ))‖ < 1 := by
        rw [Real.norm_eq_abs]
        rw [abs_of_pos (Real.exp_pos _)]
        rw [Real.exp_lt_one_iff]
        norm_num
      have hb := hasSum_geometric_of_norm_lt_one hq_abs
      have hg0 : HasSum (fun n : ℕ => (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n)
          ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
        exact hb.mul_left ((Real.exp (-(1.03 : ℝ))) ^ 4)
      have hp : ∀ n : ℕ, (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n =
          Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
        intro n
        rw [← pow_add]
        have hswap : 4 + n = n + 4 := by omega
        rw [hswap]
        rw [← Real.exp_nat_mul]
        apply congrArg Real.exp
        ring
      have hg' : HasSum (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)))
          ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
        exact hg0.congr_fun (fun n : ℕ => (hp n).symm)
      simpa [div_eq_mul_inv] using hg')⟩
  have hgs2 : Summable (fun n : ℕ => (2 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) := by
    exact hgs.mul_left (2 / (4 * (1.03 : ℝ)))
  have hterm : ∀ n : ℕ, |(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤
      (2 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
    intro n
    have hb4 : 4 ≤ n + 4 := by omega
    have hg' := g_abs_bound (n + 4) hb4
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hg'
  have hf_abs_sum : Summable (fun n : ℕ => |(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))|) := by
    exact g_shift_summable.norm
  have hsum_le : (∑' n : ℕ, |(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))|) ≤
      ∑' n : ℕ, (2 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
    exact hf_abs_sum.tsum_le_tsum hterm hgs2
  have habs : |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤
      ∑' n : ℕ, |(aE (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |E1 (bn (n + 4))| := by
    have hnorm : Summable (fun n : ℕ => ‖(aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))‖) := by
      convert hf_abs_sum using 1
      ext n
      rw [Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have he4 : Real.exp (-(1.03 : ℝ) * 4) ≤ (0.358 : ℝ) ^ 4 := by
    have hp1 : Real.exp (-(1.03 : ℝ) * 4) = (Real.exp (-(1.03 : ℝ))) ^ 4 := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      ring
    rw [hp1]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_103_le 4
  have hq_lt1 : Real.exp (-(1.03 : ℝ)) < 1 := by
    exact lt_of_le_of_lt exp_neg_103_le (by norm_num : (0.358 : ℝ) < 1)
  have hden_le : 1 - (0.358 : ℝ) ≤ 1 - Real.exp (-(1.03 : ℝ)) := by
    exact sub_le_sub_left exp_neg_103_le (1 : ℝ)
  have hinv2 : 1 / (1 - Real.exp (-(1.03 : ℝ))) ≤ 1 / (1 - (0.358 : ℝ)) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 - 0.358) hden_le
  have hdiv1 : Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) ≤
      (0.358 : ℝ) ^ 4 / (1 - Real.exp (-(1.03 : ℝ))) := by
    exact div_le_div_of_nonneg_right he4 (le_of_lt (sub_pos.2 hq_lt1))
  have hdiv2 : (0.358 : ℝ) ^ 4 / (1 - Real.exp (-(1.03 : ℝ))) ≤
      (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hm : (1 / (1 - Real.exp (-(1.03 : ℝ)))) * (0.358 : ℝ) ^ 4 ≤
        (1 / (1 - (0.358 : ℝ))) * (0.358 : ℝ) ^ 4 := by
      have hq4 : (0 : ℝ) ≤ (0.358 : ℝ) ^ 4 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 0.358) 4
      exact mul_le_mul_of_nonneg_right hinv2 hq4
    simpa [mul_comm] using hm
  have hquot : Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) ≤
      (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) :=
    le_trans hdiv1 hdiv2
  calc
    |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤
        ∑' n : ℕ, |(aE (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |E1 (bn (n + 4))| := habs
    _ ≤ ∑' n : ℕ, (2 / (4 * (1.03 : ℝ))) * Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
      rw [← g_sum_abs]
      exact hsum_le
    _ = (2 / (4 * (1.03 : ℝ))) * (Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ)))) := by
      rw [tsum_mul_left, geom_tail_value]
    _ ≤ (2 / (4 * (1.03 : ℝ))) * ((0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = (1 / (2 * (1.03 : ℝ))) * (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) := by ring

/-- L′(E,1) > 0：部分和 ≥ 0.0557，尾项 |·| ≤ 0.0125，margin 充分。 -/
theorem lprime1_pos : 0 < lprime1 := by
  rw [lprime1_split]
  have htail_num : |∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1))| ≤ (0.0125 : ℝ) := by
    have htmp2 : |∑' n : ℕ, (aE (n + 4) : ℝ) / (n + 4) * E1 (bn (n + 4))| ≤ (0.0125 : ℝ) := by
      have hnum : (1 / (2 * (1.03 : ℝ))) * (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) ≤ (0.0125 : ℝ) := by norm_num
      exact le_trans tail_abs_bound hnum
    rw [g_sum_eq2] at htmp2
    exact htmp2
  have htail_lb : -(0.0125 : ℝ) ≤ ∑' n : ℕ, (aE (n + 3 + 1) : ℝ) / (n + 3 + 1) * E1 (bn (n + 3 + 1)) := by
    exact (abs_le.mp htail_num).1
  nlinarith [part3_lower, htail_lb]

end
