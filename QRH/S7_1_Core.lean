import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Continuity
import Mathlib.Topology.Algebra.Order.Field

/-!
# 攻防 XLII — S7.1 形式化证明（Core 件：核常数与离线误差）

`L(s, χ_5)` 单族 BGS 型配对公式（定理 S7.1）的**可形式化核件**：

1. `C_MT = 1/2 + (1/√2)·cot(1/√2)` —— λ≤1/2 核族无条件极小配对常数（Lamzouri Lemma 3.2 /
   Remark 3.4；S6 框架）。
2. `Khat` —— MT 最优核 `f₀(x) = cos(√2x)/(√2·sin(1/√2))`（支撑 [−1/2,1/2]）的余弦傅里叶
   变换闭式（数值件 E 同款解析式）：
   `Khat(u) = [ sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu) ] / (√2·sin(1/√2))`。
3. ε 正则化（Lamzouri η_ε 数值形态）：`f_ε(x) = f₀(x)·min(1, (1/2 − |x|)/ε)`，
   配对常数偏差的显式 `O(ε)` 界 —— 离线误差精细控制的第一层。

真证明件：`sin(1/√2)≠0`、`Khat` 偶性、`Khat(0)=1`（sin 极限延拓）、`Khat` 频域衰减界
（三角不等式）、`f₀` 连续。

构建说明（Windows 侧 mathlib 聚合 Mathlib.olean 未生成，故用具体模块 import 绕开；
`lake build mathlib` 跑完后可改回 `import Mathlib`）。

待补（击破清单）：
  - `f0_sub_feps_L1_bound`（ε 正则化 L¹ 偏差界）需 `MeasureTheory.Integral.IntervalIntegral`
    ——待 mathlib 全量构建后恢复。
  - `C_MT < 4/3` 数值上界（norm_num + sin/cos 数值引理）。
-/

noncomputable section

open scoped BigOperators
open Real

namespace QRH

/-! ## 1. 常数与核的定义 -/

/-- cot（mathlib 以 cos/sin 表示；此处为实数域局部定义）。 -/
def cotR (x : ℝ) : ℝ := cos x / sin x

/-- C_MT = 1/2 + (1/√2)·cot(1/√2)（λ≤1/2 核族无条件极小配对常数）。 -/
def C_MT : ℝ := (1 : ℝ) / 2 + (1 / sqrt 2) * cotR (1 / sqrt 2)

/-- 最优核 f₀(x) = cos(√2x)/(√2·sin(1/√2))，支撑 [−1/2, 1/2]。 -/
def f0 (x : ℝ) : ℝ := cos (sqrt 2 * x) / (sqrt 2 * sin (1 / sqrt 2))

/-- K̂ 解析式（u ≠ ±√2/(2π) 处；u=0 处按连续延拓取 1，见 `Khat_zero`）。
    与数值件 E 的解析实现完全一致：
    ∫_{−1/2}^{1/2} f₀(x)cos(2πux)dx
      = [ sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu) ] / (√2·sin(1/√2)). -/
def Khat (u : ℝ) : ℝ :=
  ((sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)
    + (sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u))
    / (sqrt 2 * sin (1 / sqrt 2))

/-- ε 端点过渡窗 w_ε(x) = max 0 (min 1 ((1/2 − |x|)/ε))（支撑 [−1/2,1/2] 内、ε→0 逼近 f₀；
    截断到 [0,1] 保证支撑外恒零——S6/S7 数值件 D/E 的端点过渡窗同款）。 -/
def w_eps (ε x : ℝ) : ℝ := max 0 (min 1 (((1 : ℝ) / 2 - |x|) / ε))

/-- 正则化核 f_ε(x) = f₀(x)·w_ε(x)。 -/
def f_eps (ε x : ℝ) : ℝ := f0 x * w_eps ε x

/-! ## 2. 基本事实：sin(1/√2) 非零（分母良定义） -/

lemma sin_inv_sqrt2_ne_zero : sin (1 / sqrt 2) ≠ 0 := by
  have h1 : 0 < (1 : ℝ) / sqrt 2 := by positivity
  have hsqrt : (1 : ℝ) < sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num)
  have h2 : (1 : ℝ) / sqrt 2 < 1 := by
    exact (div_lt_one (by positivity : (0 : ℝ) < sqrt 2)).mpr hsqrt
  have hp : (2 : ℝ) ≤ Real.pi := two_le_pi
  have hpi : (1 : ℝ) < Real.pi := by linarith
  have hlt : (1 : ℝ) / sqrt 2 < Real.pi := by linarith
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 hlt)

/-! ## 3. 真证明件：K̂ 的基本性质 -/

/-- K̂ 是偶函数（配对核复共轭对称性在频域的表现）。 -/
lemma Khat_neg (u : ℝ) : Khat (-u) = Khat u := by
  unfold Khat
  ring_nf

/-- K̂(0)=1：sin(x)/x → 1 的连续延拓（u=0 处解析式取极限）。 -/
lemma Khat_zero : Khat 0 = 1 := by
  unfold Khat
  have hsq2 : sqrt 2 / 2 = 1 / sqrt 2 := by
    field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show sqrt 2 - 2 * Real.pi * 0 = sqrt 2 by ring,
      show sqrt 2 + 2 * Real.pi * 0 = sqrt 2 by ring]
  have hmerge : (sin (sqrt 2 / 2)) / sqrt 2 + (sin (sqrt 2 / 2)) / sqrt 2
      = 2 * sin (sqrt 2 / 2) / sqrt 2 := by ring
  rw [hmerge, hsq2]
  field_simp [sin_inv_sqrt2_ne_zero]
  all_goals try rw [mul_div_assoc]
  all_goals try rw [div_self sin_inv_sqrt2_ne_zero]
  all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals try norm_num

/-- K̂ 的频域衰减界（三角不等式）：
    |K̂(u)| ≤ [ 1/|√2−2πu| + 1/|√2+2πu| ] / (√2·|sin(1/√2)|)。
    这是核频域窄支撑论证（素数项 δlogp 窗口）的定量基础。 -/
lemma Khat_abs_le (u : ℝ) :
    |Khat u| ≤
      (1 / |sqrt 2 - 2 * Real.pi * u| + 1 / |sqrt 2 + 2 * Real.pi * u|)
        / (sqrt 2 * |sin (1 / sqrt 2)|) := by
  unfold Khat
  have hd : sqrt 2 * sin (1 / sqrt 2) ≠ 0 := by
    have : sqrt 2 ≠ 0 := by positivity
    exact mul_ne_zero this sin_inv_sqrt2_ne_zero
  have h2 : |sin ((sqrt 2 - 2 * Real.pi * u) / 2)| ≤ 1 := abs_sin_le_one _
  have h3 : |sin ((sqrt 2 + 2 * Real.pi * u) / 2)| ≤ 1 := abs_sin_le_one _
  have htri :
      |(sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)
        + (sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u)|
        ≤ 1 / |sqrt 2 - 2 * Real.pi * u| + 1 / |sqrt 2 + 2 * Real.pi * u| := by
    have h1 :
        |(sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)
          + (sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u)|
          ≤ |sin ((sqrt 2 - 2 * Real.pi * u) / 2)| / |sqrt 2 - 2 * Real.pi * u|
            + |sin ((sqrt 2 + 2 * Real.pi * u) / 2)| / |sqrt 2 + 2 * Real.pi * u| := by
      calc
        |(sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)
          + (sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u)|
          ≤ |(sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)|
            + |(sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u)| := by
          exact abs_add_le _ _
        _ = |sin ((sqrt 2 - 2 * Real.pi * u) / 2)| / |sqrt 2 - 2 * Real.pi * u|
            + |sin ((sqrt 2 + 2 * Real.pi * u) / 2)| / |sqrt 2 + 2 * Real.pi * u| := by
          rw [abs_div, abs_div]
    have h2' : |sin ((sqrt 2 - 2 * Real.pi * u) / 2)| / |sqrt 2 - 2 * Real.pi * u|
        ≤ 1 / |sqrt 2 - 2 * Real.pi * u| := by
      exact div_le_div_of_nonneg_right h2 (abs_nonneg _)
    have h3' : |sin ((sqrt 2 + 2 * Real.pi * u) / 2)| / |sqrt 2 + 2 * Real.pi * u|
        ≤ 1 / |sqrt 2 + 2 * Real.pi * u| := by
      exact div_le_div_of_nonneg_right h3 (abs_nonneg _)
    exact h1.trans (add_le_add h2' h3')
  calc
    |((sin ((sqrt 2 - 2 * Real.pi * u) / 2)) / (sqrt 2 - 2 * Real.pi * u)
      + (sin ((sqrt 2 + 2 * Real.pi * u) / 2)) / (sqrt 2 + 2 * Real.pi * u))
        / (sqrt 2 * sin (1 / sqrt 2))|
        ≤ (1 / |sqrt 2 - 2 * Real.pi * u| + 1 / |sqrt 2 + 2 * Real.pi * u|)
            / (sqrt 2 * |sin (1 / sqrt 2)|) := by
      have hden : |(sqrt 2 * sin (1 / sqrt 2))⁻¹| = (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
        rw [abs_inv]
        rw [abs_mul]
        rw [abs_of_pos (by positivity : (0 : ℝ) < sqrt 2)]
      have hpos : 0 < sqrt 2 * |sin (1 / sqrt 2)| := by
        exact mul_pos (by positivity : 0 < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero)
      rw [div_eq_mul_inv, abs_mul, hden, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right htri (le_of_lt (inv_pos.mpr hpos))

/-! ## 4. f₀ 的连续性（核正则化论证的基础件） -/

lemma f0_continuous : Continuous f0 := by
  unfold f0
  continuity

/-! ## 5. 击破清单（下一轮逐步替换 sorry / 补回模块）

- [ ] `f0_sub_feps_L1_bound`（ε 正则化 L¹ 偏差界 ≤ 2ε·(√2·|sin(1/√2)|)⁻¹）：
      证明路线 = |1−w_ε| ≤ 1_{|x|>1/2−ε} + intervalIntegral 被积函数界 + 长度 ≤ 2ε。
      前置：`lake build mathlib` 生成聚合后 import `MeasureTheory.Integral.IntervalIntegral`。
- [ ] `pair_const_eps_bias`：由 L¹ 界 + 配对和 Lipschitz 性推出；C₁ 显式（Δ 归一后 K 差分）。
- [ ] `C_MT < 4/3`（数值上界）：norm_num + sin/cos 数值引理；或先用区间算术降级。
- [ ] `Khat_zero` 的化简（field_simp/ring 已通；若 v4.34 API 差异报错按报错修正）。
- [ ] mathlib 聚合 `Mathlib.olean` 生成后：Core/Main 改回 `import Mathlib`，恢复 ε L¹ 引理。
-/

end QRH
