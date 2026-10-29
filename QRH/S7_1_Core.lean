import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Continuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

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
open scoped MeasureTheory
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

/-! ## 4b. 频域/积分抽象算子（积分定义在文档层 S7.3 §3；Lean 侧载体，供 Main/Stage3 共用） -/

/-- 余弦傅里叶变换（实数核、频域 z）：积分定义在文档层；Lean 侧为抽象算子（S7.3 §3）。 -/
axiom fourierCos : (ℝ → ℝ) → ℝ → ℝ

/-- L¹ 范数（真定义，2026-10-27 由 axiom 降级）：‖f‖₁ = ∫|f|（Bochner 积分，ℝ 上 volume）。
    不可积时 mathlib 积分按惯例为 0；scaleKernel_L1_invariant 等不变性质在 Stage3 真证。 -/
noncomputable def normL1 (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, |f x|

/-! ## 5. C_MT < 4/3（纯有理链，无积分依赖；cos 四阶上界 73/96 自证） -/

/-- sin(x) ≥ x − x³/6 − x⁵/100 for 0 ≤ x ≤ 1。
    mathlib `Real.sin_bound`（v4.34）给出 5 阶余项 |sin x − (x − x³/6)| ≤ |x|⁵/100，
    故下界含 −x⁵/100 损失项（x ≤ 1 时 ≤ 1/100，可忽略量级）。 -/
lemma sin_lower_five (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x ^ 3 / 6 - x ^ 5 / 100 ≤ sin x := by
  have hxabs1 : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have habs : |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 100 := Real.sin_bound hxabs1
  have habs' : |sin x - (x - x ^ 3 / 6)| ≤ x ^ 5 / 100 := by
    simpa [abs_of_nonneg hx0] using habs
  have hneg : -(x ^ 5 / 100) ≤ sin x - (x - x ^ 3 / 6) := by
    exact neg_le_of_abs_le habs'
  linarith

/-- cos(x) < 1 − x²/2 + x⁴/24 for 0 < x ≤ 1。
    自证路线（无积分）：cos x = 1 − 2sin²(x/2)（cos_add + cos_sq），
    sin(x/2) ≥ x/2 − (x/2)³/6 − (x/2)⁵/100（sin_lower_five）⟹ 平方单调
    ⟹ cos x ≤ 1 − 2(A−B)² ≤ 1 − 2A² + 4AB ≤ 1 − x²/2 + x⁴/24 − x⁶/1152 + x⁶/1600 < 上界
    （A = x/2 − (x/2)³/6，B = (x/2)⁵/100；4AB ≤ x⁶/1600）。 -/
lemma cos_upper_four (x : ℝ) (hxpos : 0 < x) (hx1 : x ≤ 1) :
    cos x < 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let y : ℝ := x / 2
  let A : ℝ := y - y ^ 3 / 6
  let B : ℝ := y ^ 5 / 100
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    linarith
  have hsin : A - B ≤ sin y := by
    dsimp [A, B]
    exact sin_lower_five y hy0 hy1
  have hysq : y ^ 2 ≤ y := by
    calc
      y ^ 2 = y * y := by ring
      _ ≤ y * 1 := by exact mul_le_mul_of_nonneg_left hy1 hy0
      _ = y := by ring
  have hy3 : y ^ 3 ≤ y ^ 2 := by
    calc
      y ^ 3 = y * y ^ 2 := by ring
      _ ≤ y * y := by exact mul_le_mul_of_nonneg_left hysq hy0
      _ = y ^ 2 := by ring
  have hy5 : y ^ 5 ≤ y := by
    calc
      y ^ 5 = y ^ 3 * y ^ 2 := by ring
      _ ≤ y ^ 2 * y ^ 2 := by exact mul_le_mul_of_nonneg_right hy3 (sq_nonneg y)
      _ ≤ y * y ^ 2 := by exact mul_le_mul_of_nonneg_right hysq (sq_nonneg y)
      _ ≤ y * y := by exact mul_le_mul_of_nonneg_left hysq hy0
      _ = y ^ 2 := by ring
      _ ≤ y := hysq
  have hlin : 0 ≤ A - B := by
    dsimp [A, B]
    have hy3le : y ^ 3 ≤ y := by linarith [hy3, hysq]
    have hy5le : y ^ 5 / 100 ≤ y / 100 := by linarith [hy5]
    nlinarith
  have hsinpos : 0 ≤ sin y := by linarith [hsin, hlin]
  have hsq : (A - B) ^ 2 ≤ (sin y) ^ 2 := by
    calc
      (A - B) ^ 2 = (A - B) * (A - B) := by ring
      _ ≤ (A - B) * sin y := by
        exact mul_le_mul_of_nonneg_left hsin hlin
      _ ≤ sin y * sin y := by
        exact mul_le_mul_of_nonneg_right hsin hsinpos
      _ = (sin y) ^ 2 := by ring
  have hcos2y : cos (2 * y) = 1 - 2 * (sin y) ^ 2 := by
    rw [show 2 * y = y + y by ring]
    rw [Real.cos_add]
    have hpy' : sin y * sin y + cos y * cos y = 1 := by
      simpa [pow_two] using Real.sin_sq_add_cos_sq y
    have hcs : cos y * cos y = 1 - sin y * sin y := by
      nlinarith [hpy']
    rw [hcs]
    ring
  have hx2y : x = 2 * y := by
    dsimp [y]
    ring
  have hAB : 4 * A * B ≤ x ^ 6 / 1600 := by
    dsimp [A, B]
    have hA_le : y - y ^ 3 / 6 ≤ y := by
      have : 0 ≤ y ^ 3 / 6 := by positivity
      linarith
    have hB0 : 0 ≤ y ^ 5 / 100 := by positivity
    have hAB' : (y - y ^ 3 / 6) * (y ^ 5 / 100) ≤ y * (y ^ 5 / 100) := by
      exact mul_le_mul_of_nonneg_right hA_le hB0
    have h4 : 4 * y * (y ^ 5 / 100) = x ^ 6 / 1600 := by
      dsimp [y]
      ring
    nlinarith [hAB', h4]
  have hA2 : 1 - 2 * A ^ 2 = 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 := by
    dsimp [A, y]
    ring
  have hle1 : 1 - 2 * (A - B) ^ 2 ≤ 1 - 2 * A ^ 2 + 4 * A * B := by
    have hsqB : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith
  have hle2 : 1 - 2 * A ^ 2 + 4 * A * B ≤
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 + x ^ 6 / 1600 := by
    nlinarith [hA2, hAB]
  have hle3 : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 + x ^ 6 / 1600 <
      1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    have hx6 : 0 < x ^ 6 := by positivity
    have hcmp : x ^ 6 / 1600 < x ^ 6 / 1152 := by
      have hc : (1 : ℝ) / 1600 < 1 / 1152 := by norm_num
      have hmm : (1 : ℝ) / 1600 * x ^ 6 < 1 / 1152 * x ^ 6 :=
        mul_lt_mul_of_pos_right hc hx6
      convert hmm using 1 <;> ring
    linarith
  calc
    cos x = cos (2 * y) := by rw [hx2y]
    _ = 1 - 2 * (sin y) ^ 2 := hcos2y
    _ ≤ 1 - 2 * (A - B) ^ 2 := by
      have hle : 2 * (A - B) ^ 2 ≤ 2 * (sin y) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    _ ≤ 1 - 2 * A ^ 2 + 4 * A * B := hle1
    _ ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 + x ^ 6 / 1600 := hle2
    _ < 1 - x ^ 2 / 2 + x ^ 4 / 24 := hle3

/-- C_MT < 4/3：x₀ = 1/√2 处 cos 四阶上界 73/96（= 1 − 1/4 + 1/96）、
    sin 下界 11/(12√2) − √2/800（sin_bound 五阶损失项并入），cot 上界 1825/(1097√2)
    ⟹ C_MT < 1/2 + 1825/2194 = 2922/2194 < 4/3。√2 因子全程消去，纯有理链。 -/
theorem C_MT_lt_four_thirds : C_MT < (4 : ℝ) / 3 := by
  let x0 : ℝ := 1 / sqrt 2
  have hx0pos : 0 < x0 := by
    dsimp [x0]
    positivity
  have hx0sq : x0 ^ 2 = (1 : ℝ) / 2 := by
    dsimp [x0]
    field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hx0le1 : x0 ≤ 1 := by
    have hlt : x0 ^ 2 < 1 ^ 2 := by
      rw [hx0sq]
      norm_num
    have hlt' : x0 < 1 := by
      by_contra h
      have hge : (1 : ℝ) ≤ x0 := le_of_not_gt h
      have hsqle : (1 : ℝ) ^ 2 ≤ x0 ^ 2 := by
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hge 2
      have hsqlt : x0 ^ 2 < (1 : ℝ) := by
        rw [hx0sq]
        norm_num
      nlinarith
    linarith
  have hx0cub : x0 ^ 3 = sqrt 2 / 4 := by
    dsimp [x0]
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h4 : (sqrt 2) ^ 4 = 4 := by
      calc
        (sqrt 2) ^ 4 = (sqrt 2) ^ 2 * (sqrt 2) ^ 2 := by ring
        _ = 4 := by rw [h2]; norm_num
    field_simp
    rw [h4]
  have hx0fif : x0 ^ 5 = sqrt 2 / 8 := by
    dsimp [x0]
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h6 : (sqrt 2) ^ 6 = 8 := by
      calc
        (sqrt 2) ^ 6 = (sqrt 2) ^ 2 * (sqrt 2) ^ 2 * (sqrt 2) ^ 2 := by ring
        _ = 8 := by rw [h2]; norm_num
    field_simp
    rw [h6]
  have hcos : cos x0 < 73 / 96 := by
    have hx04 : x0 ^ 4 = (1 : ℝ) / 4 := by nlinarith [hx0sq]
    calc
      cos x0 < 1 - x0 ^ 2 / 2 + x0 ^ 4 / 24 := cos_upper_four x0 hx0pos hx0le1
      _ = 73 / 96 := by rw [hx0sq, hx04]; norm_num
  have hsin : 11 / (12 * sqrt 2) - sqrt 2 / 800 ≤ sin x0 := by
    calc
      11 / (12 * sqrt 2) - sqrt 2 / 800 = x0 - x0 ^ 3 / 6 - x0 ^ 5 / 100 := by
        rw [hx0cub, hx0fif]
        dsimp [x0]
        have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        rw [h2]
        ring
      _ ≤ sin x0 := sin_lower_five x0 (le_of_lt hx0pos) hx0le1
  have hdenpos : 0 < 11 / (12 * sqrt 2) - sqrt 2 / 800 := by
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [h2]
    norm_num
  have hsinpos : 0 < sin x0 := lt_of_lt_of_le hdenpos hsin
  have hcot : cotR x0 < (73 / 96) / (11 / (12 * sqrt 2) - sqrt 2 / 800) := by
    unfold cotR
    rw [div_lt_div_iff₀ hsinpos hdenpos]
    have hcross : cos x0 * (11 / (12 * sqrt 2) - sqrt 2 / 800) < (73 / 96) * sin x0 := by
      calc
        cos x0 * (11 / (12 * sqrt 2) - sqrt 2 / 800) < (73 / 96) * (11 / (12 * sqrt 2) - sqrt 2 / 800) := by
          exact mul_lt_mul_of_pos_right hcos hdenpos
        _ ≤ (73 / 96) * sin x0 := by
          exact mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 73 / 96)
    exact hcross
  have hcotb : (73 / 96) / (11 / (12 * sqrt 2) - sqrt 2 / 800) = 1825 / (1097 * sqrt 2) := by
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    rw [h2]
    ring
  have hcot' : cotR x0 < 1825 / (1097 * sqrt 2) := by
    simpa [hcotb] using hcot
  have hmul : (1 / sqrt 2) * cotR x0 < (1 / sqrt 2) * (1825 / (1097 * sqrt 2)) := by
    exact mul_lt_mul_of_pos_left hcot' (by positivity : 0 < 1 / sqrt 2)
  have hb : (1 / sqrt 2) * (1825 / (1097 * sqrt 2)) = 1825 / 2194 := by
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    rw [h2]
    norm_num
  calc
    C_MT = (1 : ℝ) / 2 + (1 / sqrt 2) * cotR x0 := by
      unfold C_MT
      rw [show (1 : ℝ) / sqrt 2 = x0 by rfl]
    _ < (1 : ℝ) / 2 + (1 / sqrt 2) * (1825 / (1097 * sqrt 2)) := by linarith
    _ = 2922 / 2194 := by rw [hb]; norm_num
    _ < (4 : ℝ) / 3 := by norm_num

/-! ## 6. 击破清单（下一轮逐步替换 sorry / 补回模块）

- [ ] `f0_sub_feps_L1_bound`（ε 正则化 L¹ 偏差界 ≤ 2ε·(√2·|sin(1/√2)|)⁻¹）：
      证明路线 = |1−w_ε| ≤ 1_{|x|>1/2−ε} + intervalIntegral 被积函数界 + 长度 ≤ 2ε。
      前置：`lake build mathlib` 生成聚合后 import `MeasureTheory.Integral.IntervalIntegral`。
- [ ] `pair_const_eps_bias`：由 L¹ 界 + 配对和 Lipschitz 性推出；C₁ 显式（Δ 归一后 K 差分）。
- [x] `C_MT < 4/3`（数值上界）：纯有理链真证（sin_lower_five + cos_upper_four + C_MT_lt_four_thirds；
      cos 四阶上界 73/96、sin 下界 11/(12√2) − √2/800（sin_bound 五阶损失并入）、cot < 1825/(1097√2)
      ⟹ C_MT < 2922/2194 < 4/3；√2 因子全程消去；无积分、无 mathlib 聚合依赖）。
- [ ] `Khat_zero` 的化简（field_simp/ring 已通；若 v4.34 API 差异报错按报错修正）。
- [ ] mathlib 聚合 `Mathlib.olean` 生成后：Core/Main 改回 `import Mathlib`，恢复 ε L¹ 引理。
-/

end QRH
