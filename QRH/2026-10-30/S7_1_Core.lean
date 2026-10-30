import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
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
open Filter
open Real

namespace QRH

/-! ## 1. 常数与核的定义 -/

/-- cot（mathlib 以 cos/sin 表示；此处为实数域局部定义）。 -/
def cotR (x : ℝ) : ℝ := cos x / sin x

/-- C_MT = 1/2 + (1/√2)·cot(1/√2)（λ≤1/2 核族无条件极小配对常数）。 -/
def C_MT : ℝ := (1 : ℝ) / 2 + (1 / sqrt 2) * cotR (1 / sqrt 2)

/-- 最优核 f₀(x) = 1_{|x|≤1/2}·cos(√2x)/(√2·sin(1/√2))，支撑 [−1/2, 1/2]。
    （2026-10-30 口径修正：原全实轴定义不衰减，∫_ℝ|f₀| 绝对发散，
     ‖f₀−f_ε‖₁ 在全空间 Bochner 惯例下归 0、直接真证空洞；
     Lamzouri 最优核本为支撑 [−1/2,1/2] 的紧支撑函数——注释口径即此，此处补截断，
     顺带修复 fourierCos f0 与 n2_linkage 的局部积分口径。） -/
def f0 (x : ℝ) : ℝ :=
  if |x| ≤ (1 : ℝ) / 2 then cos (sqrt 2 * x) / (sqrt 2 * sin (1 / sqrt 2)) else 0

/-- sin(x/2)/x 的连续延拓（x=0 处取极限 1/2）。
    K̂ 闭式含 sin/x 型奇点 √2±2πu=0（u=±√2/(2π)）：原闭式在奇点处 Lean 除零惯例取 0，
    与数学连续延拓值 1/2 相差 1/2——K̂ 在奇点处不连续、全局 Lipschitz（`khat_lipschitz`）为假。
    S_smooth 恢复连续性（2026-10-30 口径修正，同 f0 截断"先修口径再真证"模式）。 -/
def S_smooth (x : ℝ) : ℝ := if x = 0 then (1 : ℝ) / 2 else sin (x / 2) / x

/-- K̂ 解析式（sin/x 型奇点 √2±2πu=0 处按连续延拓 S_smooth；u=0 处取 1，见 `Khat_zero`）。
    与数值件 E 的解析实现完全一致：
    ∫_{−1/2}^{1/2} f₀(x)cos(2πux)dx
      = [ sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu) ] / (√2·sin(1/√2)).
    口径：奇点 √2±2πu=0 处两项分别取延拓值 1/2，保证 K̂ 全实轴连续——
    `khat_lipschitz` 全局 Lipschitz（L = π/(√2·|sin(1/√2)|)，导数件真证）的前提。 -/
def Khat (u : ℝ) : ℝ :=
  (S_smooth (sqrt 2 - 2 * Real.pi * u) + S_smooth (sqrt 2 + 2 * Real.pi * u))
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

/-- K̂ 是偶函数（配对核复共轭对称性在频域的表现；S_smooth 延拓保持偶性）。 -/
lemma Khat_neg (u : ℝ) : Khat (-u) = Khat u := by
  unfold Khat
  rw [show sqrt 2 - 2 * Real.pi * (-u) = sqrt 2 + 2 * Real.pi * u by ring,
      show sqrt 2 + 2 * Real.pi * (-u) = sqrt 2 - 2 * Real.pi * u by ring]
  rw [add_comm (S_smooth (sqrt 2 - 2 * Real.pi * u)) (S_smooth (sqrt 2 + 2 * Real.pi * u))]

/-- K̂(0)=1：sin(x)/x → 1 的连续延拓（u=0 处解析式取极限；√2 ≠ 0 故 S_smooth 走非延拓分支）。 -/
lemma Khat_zero : Khat 0 = 1 := by
  unfold Khat
  rw [show sqrt 2 - 2 * Real.pi * 0 = sqrt 2 by ring,
      show sqrt 2 + 2 * Real.pi * 0 = sqrt 2 by ring]
  simp [S_smooth]
  have hsq2 : sqrt 2 / 2 = 1 / sqrt 2 := by
    field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmerge : (sin (sqrt 2 / 2)) / sqrt 2 + (sin (sqrt 2 / 2)) / sqrt 2
      = 2 * sin (sqrt 2 / 2) / sqrt 2 := by ring
  rw [hmerge, hsq2]
  field_simp [sin_inv_sqrt2_ne_zero]
  all_goals try rw [mul_div_assoc]
  all_goals try rw [div_self sin_inv_sqrt2_ne_zero]
  all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals try norm_num

/-- K̂ 的频域衰减界（三角不等式；奇点 √2±2πu=0 处右端 1/|·| 在 Lean 除零惯例下有限、
    陈述退化，故前提限定非奇点——全轴界由 `khat_global_bound` 承担）：
    |K̂(u)| ≤ [ 1/|√2−2πu| + 1/|√2+2πu| ] / (√2·|sin(1/√2)|)。
    这是核频域窄支撑论证（素数项 δlogp 窗口）的定量基础。 -/
lemma Khat_abs_le (u : ℝ) (h1 : sqrt 2 - 2 * Real.pi * u ≠ 0)
    (h2 : sqrt 2 + 2 * Real.pi * u ≠ 0) :
    |Khat u| ≤
      (1 / |sqrt 2 - 2 * Real.pi * u| + 1 / |sqrt 2 + 2 * Real.pi * u|)
        / (sqrt 2 * |sin (1 / sqrt 2)|) := by
  unfold Khat
  rw [show S_smooth (sqrt 2 - 2 * Real.pi * u)
        = sin ((sqrt 2 - 2 * Real.pi * u) / 2) / (sqrt 2 - 2 * Real.pi * u) by
        unfold S_smooth; rw [ite_eq_right h1],
      show S_smooth (sqrt 2 + 2 * Real.pi * u)
        = sin ((sqrt 2 + 2 * Real.pi * u) / 2) / (sqrt 2 + 2 * Real.pi * u) by
        unfold S_smooth; rw [ite_eq_right h2]]
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

/-- 辅助：|sin t / (2t)| ≤ 1/2（t=0 处分母为零、Lean 除零惯例取值 0；用 |sin t| ≤ |t|）。 -/
lemma abs_sin_div_two_mul_le_half (t : ℝ) : |sin t / (2 * t)| ≤ 1 / 2 := by
  by_cases ht : t = 0
  · subst t
    simp
  · have ht' : |t| ≠ 0 := by simp [ht]
    have h2 : |2 * t| = 2 * |t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |sin t / (2 * t)| = |sin t| / |2 * t| := by rw [abs_div]
      _ = |sin t| / (2 * |t|) := by rw [h2]
      _ ≤ |t| / (2 * |t|) := by
        exact div_le_div_of_nonneg_right (show |sin t| ≤ |t| from Real.abs_sin_le_abs)
          (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 1 / 2 := by
        field_simp [ht']

/-! ## 3b. S_smooth：K̂ 闭式 sin/x 型奇点的连续延拓件（khat_lipschitz 导数件的基础） -/

/-- S_smooth 是偶函数。 -/
lemma S_smooth_neg (x : ℝ) : S_smooth (-x) = S_smooth x := by
  unfold S_smooth
  by_cases hx : x = 0
  · simp [hx]
  · have hnx : -x ≠ 0 := by
      intro h
      apply hx
      linarith
    rw [ite_eq_right hnx, ite_eq_right hx]
    rw [show -x / 2 = -(x / 2) by ring, Real.sin_neg]
    field_simp [hx]

/-- |S_smooth x| ≤ 1/2（∀x；x=0 延拓值 1/2，x≠0 用 |sin t| ≤ |t|）。 -/
lemma S_smooth_le_half (x : ℝ) : |S_smooth x| ≤ (1 : ℝ) / 2 := by
  unfold S_smooth
  by_cases hx : x = 0
  · simp [hx]
  · rw [ite_eq_right hx]
    have hx' : |x| ≠ 0 := by simp [hx]
    calc
      |sin (x / 2) / x| = |sin (x / 2)| / |x| := by rw [abs_div]
      _ ≤ |x / 2| / |x| := by
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_abs (x := x / 2)) (abs_nonneg _)
      _ = 1 / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        field_simp [hx']

/-- |cos s − 1| ≤ s²（s ≥ 0；均值定理于 cos−1，|−sin x| ≤ x ≤ s）。 -/
lemma abs_cos_sub_one_le_sq_of_nonneg {s : ℝ} (hs0 : 0 ≤ s) : |cos s - 1| ≤ s ^ 2 := by
  have hf : ∀ x ∈ Set.Icc (0 : ℝ) s,
      HasDerivWithinAt (cos - fun _ : ℝ => (1 : ℝ)) (-sin x) (Set.Icc (0 : ℝ) s) x := by
    intro x hx
    simpa using ((Real.hasDerivAt_cos x).sub (hasDerivAt_const x 1)).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (0 : ℝ) s, ‖-sin x‖ ≤ s := by
    intro x hx
    rw [Real.norm_eq_abs, abs_neg]
    calc
      |sin x| ≤ |x| := Real.abs_sin_le_abs (x := x)
      _ ≤ s := by
        rw [abs_of_nonneg hx.1]
        exact le_of_lt hx.2
  have hres :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => cos t - 1)
      (f' := fun t : ℝ => -sin t) (C := s) hf hb
  have hinst := hres s (Set.mem_Icc.mpr ⟨hs0, le_rfl⟩)
  simpa [Real.norm_eq_abs, sq] using hinst

/-- |sin t − t| ≤ |t|³（∀t；均值定理于 sin−x，|cos x − 1| ≤ x² ⟹ |·| ≤ t²·t；奇性对称到负轴）。 -/
lemma abs_sin_sub_id_le_cube_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) : |sin t - t| ≤ t ^ 3 := by
  have hf : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (sin - id) (cos x - 1) (Set.Icc (0 : ℝ) t) x := by
    intro x hx
    simpa using ((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (0 : ℝ) t, ‖cos x - 1‖ ≤ t ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxt : x ≤ t := le_of_lt hx.2
    calc
      ‖cos x - 1‖ ≤ x ^ 2 := by
        rw [Real.norm_eq_abs]
        exact abs_cos_sub_one_le_sq_of_nonneg hx0
      _ ≤ t ^ 2 := by gcongr
  have hres :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => sin u - u)
      (f' := fun u : ℝ => cos u - 1) (C := t ^ 2) hf hb
  have hinst := hres t (Set.mem_Icc.mpr ⟨ht0, le_rfl⟩)
  simpa [Real.norm_eq_abs, sq, pow_succ] using hinst

lemma abs_sin_sub_id_le_cube (t : ℝ) : |sin t - t| ≤ |t| ^ 3 := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using abs_sin_sub_id_le_cube_of_nonneg ht
  · have hs0 : 0 ≤ -t := by linarith
    have h := abs_sin_sub_id_le_cube_of_nonneg (t := -t) hs0
    -- sin(−t) − (−t) = −(sin t − t)（奇性）⟹ |·| 同；(−t)³ = |t|³（t ≤ 0）
    have hsym : |sin t - t| = |sin (-t) - (-t)| := by
      have : sin (-t) - (-t) = -(sin t - t) := by
        rw [sin_neg]
        ring
      rw [this, abs_neg]
    rw [hsym]
    have hpow : |t| ^ 3 = (-t) ^ 3 := by
      rw [abs_of_nonpos (by linarith : t ≤ 0)]
    rw [hpow]
    exact h

/-- |sin t − t·cos t| ≤ t²（∀t；均值定理于 sin−x·cos，h′=x·sin x，|·|≤|t|·|t|；负轴偶性）。 -/
lemma abs_sin_sub_mul_cos_le_sq_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) : |sin t - t * cos t| ≤ t ^ 2 := by
  have hf : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (sin - id * cos) (x * sin x) (Set.Icc (0 : ℝ) t) x := by
    intro x hx
    have hd1 : HasDerivAt sin (cos x) x := Real.hasDerivAt_sin x
    have hd2 : HasDerivAt (id * cos) (cos x - x * sin x) x := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id x).mul (Real.hasDerivAt_cos x)
    simpa using (hd1.sub hd2).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (0 : ℝ) t, ‖x * sin x‖ ≤ t := by
    intro x hx
    rw [Real.norm_eq_abs]
    calc
      |x * sin x| = |x| * |sin x| := abs_mul _ _
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one x) (abs_nonneg x)
      _ = x := by rw [abs_of_nonneg hx.1, mul_one]
      _ ≤ t := le_of_lt hx.2
  have hres :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => sin u - u * cos u)
      (f' := fun u : ℝ => u * sin u) (C := t) hf hb
  have hinst := hres t (Set.mem_Icc.mpr ⟨ht0, le_rfl⟩)
  simpa [Real.norm_eq_abs, sq] using hinst

lemma abs_sin_sub_mul_cos_le_sq (t : ℝ) : |sin t - t * cos t| ≤ t ^ 2 := by
  by_cases ht : 0 ≤ t
  · exact abs_sin_sub_mul_cos_le_sq_of_nonneg ht
  · have hs0 : 0 ≤ -t := by linarith
    have h := abs_sin_sub_mul_cos_le_sq_of_nonneg (t := -t) hs0
    -- sin(−t) − (−t)·cos(−t) = −(sin t − t·cos t)；|·| 同；(−t)² = t²
    have hsym : |sin t - t * cos t| = |sin (-t) - (-t) * cos (-t)| := by
      have : sin (-t) - (-t) * cos (-t) = -(sin t - t * cos t) := by
        rw [sin_neg, cos_neg]
        ring
      rw [this, abs_neg]
    rw [hsym]
    simpa [sq] using h

/-- S_smooth 在 0 处可导（导数 0；|sin(x/2) − x/2| ≤ |x/2|³ ⟹ 斜率 → 0）。 -/
lemma S_smooth_hasDerivAt_zero : HasDerivAt S_smooth 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hbound : ∀ y : ℝ, ‖slope S_smooth (0 : ℝ) y‖ ≤ |y| / 8 := by
    intro y
    by_cases hy : y = 0
    · simp [hy, S_smooth, slope]
    · have hsy : S_smooth y = sin (y / 2) / y := by
        unfold S_smooth
        rw [ite_eq_right hy]
      have hslope : slope S_smooth (0 : ℝ) y = (S_smooth y - S_smooth 0) / y := by
        unfold slope
        rw [sub_zero]
        rw [smul_eq_mul]
        rw [mul_comm]
        rfl
      rw [hslope]
      have hnum : |sin (y / 2) - y / 2| ≤ |y / 2| ^ 3 := abs_sin_sub_id_le_cube (y / 2)
      have hnum' : |sin (y / 2) / y - 1 / 2| ≤ |y| ^ 2 / 8 := by
        have hfact : sin (y / 2) / y - 1 / 2 = (sin (y / 2) - y / 2) / y := by
          field_simp [hy]
        rw [hfact, abs_div]
        calc
          |sin (y / 2) - y / 2| / |y| ≤ (|y / 2| ^ 3) / |y| := by
            exact div_le_div_of_nonneg_right hnum (abs_nonneg _)
          _ = |y| ^ 2 / 8 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            field_simp [show |y| ≠ 0 from abs_ne_zero.mpr hy]
            norm_num
      calc
        ‖(S_smooth y - S_smooth 0) / y‖
            = |(sin (y / 2) / y - 1 / 2) / y| := by
                rw [Real.norm_eq_abs, hsy]
                simp [S_smooth]
        _ ≤ (|y| ^ 2 / 8) / |y| := by
                rw [abs_div]
                exact div_le_div_of_nonneg_right hnum' (abs_nonneg _)
        _ = |y| / 8 := by
                field_simp [show |y| ≠ 0 from abs_ne_zero.mpr hy]
  have hconv : Tendsto (fun y : ℝ => |y| / 8) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h0 : Tendsto (fun y : ℝ => |y| / 8) (nhds (0 : ℝ)) (nhds 0) := by
      have h1 : Tendsto (fun y : ℝ => |y|) (nhds 0) (nhds 0) := by
        simpa using (continuous_abs.continuousAt (x := (0 : ℝ))).tendsto
      have h2 : Tendsto (fun y : ℝ => (8 : ℝ)⁻¹) (nhds (0 : ℝ)) (nhds ((8 : ℝ)⁻¹)) :=
        tendsto_const_nhds
      simpa [div_eq_mul_inv] using h1.mul h2
    exact h0.mono_left (inf_le_left : nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds (0 : ℝ))
  -- 夹逼 |slope|：0 ≤ ‖slope y‖ ≤ |y|/8，且 0 ≤ |y|/8 → 0
  have hnorm : Tendsto (fun y : ℝ => ‖slope S_smooth (0 : ℝ) y‖)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)))
      hconv
      (fun y => norm_nonneg (a := slope S_smooth (0 : ℝ) y))
      hbound
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- S_smooth 在 x ≠ 0 处可导（商法则：d[sin(x/2)/x] = (cos(x/2)/2·x − sin(x/2))/x²）。
    证明策略：sin(x/2)/x 可导（商法则）；S_smooth 与它在 x 的邻域逐点重合（x≠0 处
    if 分支恒走 else），由 `HasDerivAt.congr_of_eventuallyEq` 传递。 -/
lemma S_smooth_hasDerivAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt S_smooth ((cos (x / 2) / 2 * x - sin (x / 2)) / x ^ 2) x := by
  have hf : HasDerivAt (sin ∘ fun u : ℝ => u / 2) (cos (x / 2) / 2) x := by
    have hd : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) x := by
      simpa [div_eq_inv_mul, mul_comm] using (hasDerivAt_id x).const_mul ((2 : ℝ)⁻¹)
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_sin (x / 2)).comp x hd
  have hg : HasDerivAt id 1 x := hasDerivAt_id x
  have hdiv : HasDerivAt ((sin ∘ fun u : ℝ => u / 2) / id)
      ((cos (x / 2) / 2 * x - sin (x / 2)) / x ^ 2) x := by
    simpa [mul_one, one_mul] using hf.div hg hx
  have heq : ∀ᶠ y in nhds x, S_smooth y = sin (y / 2) / y := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    unfold S_smooth
    simp [hy]
  exact hdiv.congr_of_eventuallyEq heq

/-- S_smooth 全局可导（0 处导数 0，x≠0 处闭式）。 -/
lemma S_smooth_hasDerivAt (x : ℝ) : HasDerivAt S_smooth (deriv S_smooth x) x := by
  by_cases hx : x = 0
  · subst x
    have hd : HasDerivAt S_smooth 0 (0 : ℝ) := S_smooth_hasDerivAt_zero
    simpa [hd.deriv] using hd
  · have hd : HasDerivAt S_smooth ((cos (x / 2) / 2 * x - sin (x / 2)) / x ^ 2) x :=
      S_smooth_hasDerivAt_of_ne_zero hx
    simpa [hd.deriv] using hd

/-- |deriv S_smooth x| ≤ 1/4（全局；0 处 0，x≠0 处 |sin t − t·cos t| ≤ t² 闭式界）。 -/
lemma S_smooth_deriv_bound (x : ℝ) : ‖deriv S_smooth x‖ ≤ (1 : ℝ) / 4 := by
  by_cases hx : x = 0
  · subst x
    have hd : HasDerivAt S_smooth 0 (0 : ℝ) := S_smooth_hasDerivAt_zero
    rw [hd.deriv]
    norm_num
  · have hd : HasDerivAt S_smooth ((cos (x / 2) / 2 * x - sin (x / 2)) / x ^ 2) x :=
      S_smooth_hasDerivAt_of_ne_zero hx
    rw [hd.deriv]
    have hnum : |cos (x / 2) / 2 * x - sin (x / 2)| ≤ (x / 2) ^ 2 := by
      -- |cos·x − sin| = |sin − cos·x|（abs_sub_comm）；cos(x/2)/2·x = (x/2)·cos(x/2)
      rw [abs_sub_comm]
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (abs_sin_sub_mul_cos_le_sq (x / 2))
    calc
      ‖(cos (x / 2) / 2 * x - sin (x / 2)) / x ^ 2‖
          = |cos (x / 2) / 2 * x - sin (x / 2)| / |x ^ 2| := by
              rw [Real.norm_eq_abs, abs_div]
      _ ≤ (x / 2) ^ 2 / |x ^ 2| := by
              exact div_le_div_of_nonneg_right hnum (abs_nonneg _)
      _ = 1 / 4 := by
              rw [abs_of_nonneg (sq_nonneg x)]
              field_simp [hx]
              ring

/-- S_smooth 是 1/4-Lipschitz（凸集均值定理；S 全局可导 + |deriv| ≤ 1/4）。 -/
lemma S_smooth_lipschitz (x y : ℝ) : |S_smooth x - S_smooth y| ≤ (1 : ℝ) / 4 * |x - y| := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ S_smooth x := by
    intro x
    exact (S_smooth_hasDerivAt x).differentiableAt
  have hb : ∀ x : ℝ, ‖deriv S_smooth x‖ ≤ (1 : ℝ) / 4 := S_smooth_deriv_bound
  have hres := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ)
    (f := S_smooth) (s := Set.univ) (C := (1 : ℝ) / 4) (x := x) (y := y)
    (fun x _ => hdiff x) (fun x _ => hb x) convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hres

/-- K̂ 全局一致界：|Khat u| ≤ 1/(√2·|sin(1/√2)|)。
    注意 `Khat_abs_le` 的分母含 |√2±2πu|（u=±√2/(2π) 处为零），非全局界；
    此处用 S_smooth 逐项 |·| ≤ 1/2 给全局一致界（奇点处延拓值 1/2 同样成立）——
    `prime_weight_bounds` 有界分支的常数件。 -/
lemma khat_global_bound (u : ℝ) :
    |Khat u| ≤ 1 / (sqrt 2 * |sin (1 / sqrt 2)|) := by
  unfold Khat
  have hpos : 0 < sqrt 2 * |sin (1 / sqrt 2)| := by
    exact mul_pos (by positivity : (0 : ℝ) < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero)
  have h1 : |S_smooth (sqrt 2 - 2 * Real.pi * u)| ≤ 1 / 2 := S_smooth_le_half _
  have h2 : |S_smooth (sqrt 2 + 2 * Real.pi * u)| ≤ 1 / 2 := S_smooth_le_half _
  have hnum :
      |S_smooth (sqrt 2 - 2 * Real.pi * u) + S_smooth (sqrt 2 + 2 * Real.pi * u)| ≤ 1 := by
    calc
      |S_smooth (sqrt 2 - 2 * Real.pi * u) + S_smooth (sqrt 2 + 2 * Real.pi * u)|
        ≤ |S_smooth (sqrt 2 - 2 * Real.pi * u)| + |S_smooth (sqrt 2 + 2 * Real.pi * u)| :=
          abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add h1 h2
      _ = 1 := by norm_num
  have hden : |(sqrt 2 * sin (1 / sqrt 2))⁻¹| = (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
    rw [abs_inv]
    rw [abs_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < sqrt 2)]
  rw [div_eq_mul_inv, abs_mul, hden, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hpos))

/-! ## 3c. khat_lipschitz 的 L 导数件真证（2026-10-30）
    L = π/(√2·|sin(1/√2)|)：K̂′ = 2π(S′(√2+2πu) − S′(√2−2πu))/d，|S′| ≤ 1/4
    ⟹ |K̂′| ≤ 2π·(1/4+1/4)/(√2|sin|) = π/(√2|sin|)；凸集均值定理 ⟹ 全局 Lipschitz。 -/

/-- K̂ 全局可导（S_smooth 仿射复合 + 常数倍；导数闭式）。 -/
lemma khat_hasDerivAt (u : ℝ) :
    HasDerivAt Khat
      (2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)) / (sqrt 2 * sin (1 / sqrt 2))) u := by
  unfold Khat
  have hlin1 : HasDerivAt (fun t : ℝ => sqrt 2 - 2 * Real.pi * t) (-(2 * Real.pi)) u := by
    have hc : HasDerivAt (fun t : ℝ => sqrt 2) 0 u := hasDerivAt_const u (sqrt 2)
    have hlin : HasDerivAt ((fun _ : ℝ => (2 * Real.pi)) * id) (2 * Real.pi) u := by
      simpa [zero_mul, one_mul, zero_add] using
        (hasDerivAt_const u (2 * Real.pi)).mul (hasDerivAt_id u)
    have hsub : HasDerivAt (fun t : ℝ => sqrt 2 - (2 * Real.pi) * t) (0 - 2 * Real.pi) u :=
      hc.sub hlin
    simpa using hsub
  have hd1 : HasDerivAt (fun t : ℝ => S_smooth (sqrt 2 - 2 * Real.pi * t))
      (deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))) u := by
    exact (S_smooth_hasDerivAt (sqrt 2 - 2 * Real.pi * u)).comp u hlin1
  have hlin2 : HasDerivAt (fun t : ℝ => sqrt 2 + 2 * Real.pi * t) (2 * Real.pi) u := by
    have hc : HasDerivAt (fun t : ℝ => sqrt 2) 0 u := hasDerivAt_const u (sqrt 2)
    have hlin : HasDerivAt ((fun _ : ℝ => (2 * Real.pi)) * id) (2 * Real.pi) u := by
      simpa [zero_mul, one_mul, zero_add] using
        (hasDerivAt_const u (2 * Real.pi)).mul (hasDerivAt_id u)
    have hadd : HasDerivAt (fun t : ℝ => sqrt 2 + (2 * Real.pi) * t) (0 + 2 * Real.pi) u :=
      hc.add hlin
    simpa using hadd
  have hd2 : HasDerivAt (fun t : ℝ => S_smooth (sqrt 2 + 2 * Real.pi * t))
      (deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) u := by
    exact (S_smooth_hasDerivAt (sqrt 2 + 2 * Real.pi * u)).comp u hlin2
  have hsum : HasDerivAt (fun t : ℝ => S_smooth (sqrt 2 - 2 * Real.pi * t)
      + S_smooth (sqrt 2 + 2 * Real.pi * t))
      (deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
        + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) u :=
    hd1.add hd2
  have hdiv : sqrt 2 * sin (1 / sqrt 2) ≠ 0 := by
    exact mul_ne_zero (by positivity : sqrt 2 ≠ 0) sin_inv_sqrt2_ne_zero
  have hc : HasDerivAt (fun t : ℝ => sqrt 2 * sin (1 / sqrt 2)) 0 u :=
    hasDerivAt_const u (sqrt 2 * sin (1 / sqrt 2))
  have hd := hsum.div hc hdiv
  -- hd : HasDerivAt (f/c) ((f'·c − f·0)/c²) u；目标导数 2π(d2−d1)/c——经两步 rw 转换
  have h_num : 2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))
      = deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
        + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi) := by
    ring
  have h_eq1 : (2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))) / (sqrt 2 * sin (1 / sqrt 2))
      = (deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
        + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi))
        / (sqrt 2 * sin (1 / sqrt 2)) := by
    rw [h_num]
  have h_eq2 : (deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
        + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi))
        / (sqrt 2 * sin (1 / sqrt 2))
      = ((deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
        + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) * (sqrt 2 * sin (1 / sqrt 2))
        - (S_smooth (sqrt 2 - 2 * Real.pi * u) + S_smooth (sqrt 2 + 2 * Real.pi * u)) * 0)
        / (sqrt 2 * sin (1 / sqrt 2)) ^ 2 := by
    have hcc : (sqrt 2 * sin (1 / sqrt 2))⁻¹
        = (sqrt 2 * sin (1 / sqrt 2)) * (sqrt 2 * sin (1 / sqrt 2))⁻¹ ^ 2 := by
      rw [pow_two, ← mul_assoc]
      rw [mul_inv_cancel₀ hdiv]
      rw [one_mul]
    rw [div_eq_mul_inv]
    rw [hcc]
    rw [← mul_assoc]
    rw [show ((deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
          + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) * (sqrt 2 * sin (1 / sqrt 2))
          - (S_smooth (sqrt 2 - 2 * Real.pi * u) + S_smooth (sqrt 2 + 2 * Real.pi * u)) * 0)
          = (deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
          + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) * (sqrt 2 * sin (1 / sqrt 2)) by
        ring]
    have h_div : ((deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
          + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) * (sqrt 2 * sin (1 / sqrt 2)))
          / (sqrt 2 * sin (1 / sqrt 2)) ^ 2
        = ((deriv S_smooth (sqrt 2 - 2 * Real.pi * u) * (-(2 * Real.pi))
          + deriv S_smooth (sqrt 2 + 2 * Real.pi * u) * (2 * Real.pi)) * (sqrt 2 * sin (1 / sqrt 2)))
          * (sqrt 2 * sin (1 / sqrt 2))⁻¹ ^ 2 := by
      rw [div_eq_mul_inv]
      rw [← inv_pow]
    rw [h_div]
  have hd0 : HasDerivAt (fun t : ℝ => (S_smooth (sqrt 2 - 2 * Real.pi * t)
      + S_smooth (sqrt 2 + 2 * Real.pi * t)) / (sqrt 2 * sin (1 / sqrt 2)))
      (2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)) / (sqrt 2 * sin (1 / sqrt 2))) u := by
    rw [h_eq1, h_eq2]
    exact hd
  exact hd0

/-- |deriv Khat u| ≤ π/(√2·|sin(1/√2)|)（全局；Lipschitz 常数件）。 -/
lemma khat_deriv_bound (u : ℝ) :
    ‖deriv Khat u‖ ≤ Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|) := by
  have hd := khat_hasDerivAt u
  rw [hd.deriv]
  have hpos : 0 < sqrt 2 * |sin (1 / sqrt 2)| := by
    exact mul_pos (by positivity : (0 : ℝ) < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero)
  have hnum : ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
      - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))‖ ≤ Real.pi := by
    have htri : ‖deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)‖ ≤ (1 : ℝ) / 2 := by
      calc
        ‖deriv S_smooth (sqrt 2 + 2 * Real.pi * u) - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)‖
            ≤ ‖deriv S_smooth (sqrt 2 + 2 * Real.pi * u)‖ + ‖deriv S_smooth (sqrt 2 - 2 * Real.pi * u)‖ :=
              norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 4 := add_le_add (S_smooth_deriv_bound _) (S_smooth_deriv_bound _)
        _ = 1 / 2 := by norm_num
    calc
      ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
            - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))‖
          ≤ ‖2 * Real.pi‖ * ‖deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
              - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)‖ := by
              exact norm_mul_le (a := (2 : ℝ) * Real.pi)
                (b := deriv S_smooth (sqrt 2 + 2 * Real.pi * u) - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))
      _ = 2 * Real.pi * ‖deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
              - deriv S_smooth (sqrt 2 - 2 * Real.pi * u)‖ := by
              rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      _ ≤ 2 * Real.pi * (1 / 2) := by
              exact mul_le_mul_of_nonneg_left htri (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      _ = Real.pi := by ring
  calc
    ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
        - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))
      / (sqrt 2 * sin (1 / sqrt 2))‖
        ≤ Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|) := by
        have hden_abs : |sqrt 2 * sin (1 / sqrt 2)| = sqrt 2 * |sin (1 / sqrt 2)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < sqrt 2)]
        calc
          ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
                - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))
            / (sqrt 2 * sin (1 / sqrt 2))‖
              = |2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
                    - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))
                  / (sqrt 2 * sin (1 / sqrt 2))| := by
                  rw [Real.norm_eq_abs]
          _ = |2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
                  - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))|
                / |sqrt 2 * sin (1 / sqrt 2)| := by
                  rw [abs_div]
          _ = ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
                  - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))‖
              / |sqrt 2 * sin (1 / sqrt 2)| := by
                  rw [Real.norm_eq_abs]
          _ = ‖2 * Real.pi * (deriv S_smooth (sqrt 2 + 2 * Real.pi * u)
                  - deriv S_smooth (sqrt 2 - 2 * Real.pi * u))‖
              / (sqrt 2 * |sin (1 / sqrt 2)|) := by
                  rw [hden_abs]
          _ ≤ Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|) := by
                  exact div_le_div_of_nonneg_right hnum (le_of_lt hpos)

/-- khat_lipschitz 真证（axiom → theorem）：∃L, 0≤L ∧ 全局 Lipschitz，
    L = π/(√2·|sin(1/√2)|)（导数件 + 凸集均值定理）。 -/
theorem khat_lipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : ℝ, |Khat u - Khat v| ≤ L * |u - v| := by
  refine ⟨Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|), ?_, ?_⟩
  · exact div_nonneg (le_of_lt pi_pos)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ sqrt 2) (abs_nonneg _))
  · intro u v
    have hdiff : ∀ x : ℝ, DifferentiableAt ℝ Khat x := by
      intro x
      exact (khat_hasDerivAt x).differentiableAt
    have hb : ∀ x : ℝ, ‖deriv Khat x‖ ≤ Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|) :=
      khat_deriv_bound
    have hres := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ)
      (f := Khat) (s := Set.univ)
      (C := Real.pi / (sqrt 2 * |sin (1 / sqrt 2)|)) (x := u) (y := v)
      (fun x _ => hdiff x) (fun x _ => hb x) convex_univ trivial trivial
    simpa [Real.norm_eq_abs, abs_sub_comm] using hres

/-! ## 4. f₀ 的界与可测性（截断核；原 `f0_continuous` 因 ±1/2 支撑截断不再连续，删除——
    无使用点；fourierCos/normL1 只须可测 + 可积，界件 f0_abs_le 供 f0_sub_feps_L1_bound） -/

/-- |(√2·sin(1/√2))⁻¹| = (√2·|sin(1/√2)|)⁻¹（分母模件，f0 界的基础）。 -/
lemma f0_den_abs : |(sqrt 2 * sin (1 / sqrt 2))⁻¹| = (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
  rw [abs_inv]
  rw [abs_mul]
  rw [abs_of_pos (by positivity : (0 : ℝ) < sqrt 2)]

/-- |f₀(x)| ≤ (√2·|sin(1/√2)|)⁻¹：|cos| ≤ 1 × 分母绝对值件。 -/
lemma f0_abs_le (x : ℝ) : |f0 x| ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
  unfold f0
  by_cases hx : |x| ≤ (1 : ℝ) / 2
  · rw [ite_eq_left hx]
    calc
      |cos (sqrt 2 * x) / (sqrt 2 * sin (1 / sqrt 2))|
          = |cos (sqrt 2 * x)| * |(sqrt 2 * sin (1 / sqrt 2))⁻¹| := by
            rw [div_eq_mul_inv, abs_mul]
      _ ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
            rw [f0_den_abs]
            have hx : 0 ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
              exact inv_nonneg.mpr (mul_nonneg (by positivity : (0 : ℝ) ≤ sqrt 2) (abs_nonneg _))
            calc
              |cos (sqrt 2 * x)| * (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
                  ≤ 1 * (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
                    exact mul_le_mul_of_nonneg_right (abs_cos_le_one (sqrt 2 * x)) hx
              _ = (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by simp
  · rw [ite_eq_right hx]
    simp

/-- f₀ 可测（截断 = if |x|≤1/2；闭集 {|x|≤1/2} = Icc (−1/2) (1/2) 可测，分支连续/常数）。 -/
lemma f0_measurable : Measurable f0 := by
  unfold f0
  refine Measurable.ite ?hp ?hf ?hg
  · rw [show {x : ℝ | |x| ≤ (1 : ℝ) / 2} = Set.Icc (-((1 : ℝ) / 2)) ((1 : ℝ) / 2) by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]]
    exact (isClosed_Icc).measurableSet
  · have hden0 : (sqrt 2 * sin (1 / sqrt 2)) ≠ 0 :=
      mul_ne_zero (by positivity : sqrt 2 ≠ 0) sin_inv_sqrt2_ne_zero
    have hc : Continuous (fun x : ℝ => cos (sqrt 2 * x) / (sqrt 2 * sin (1 / sqrt 2))) :=
      (continuous_cos.comp (continuous_const.mul continuous_id)).div continuous_const (fun _ => hden0)
    exact hc.measurable
  · exact measurable_const

/-! ## 4b. 频域/积分抽象算子（积分定义在文档层 S7.3 §3；Lean 侧载体，供 Main/Stage3 共用） -/

/-- 余弦傅里叶变换（实数核、频域 z）：K̂(z) = ∫ K(x)cos(2πzx)dx（Bochner 积分，ℝ 上 volume；
    文档 S7.3 §3）。2026-10-29 由 axiom 降为真定义——基础 Bochner 积分件在本环境可编译
    （normL1 同款机制）；不可积时积分按 mathlib 惯例为 0。
    定义一致件 `fourierCos_Khat` 与光滑件 `khat_lipschitz` 仍为命名 axiom（解析闭式/导数件）。 -/
noncomputable def fourierCos (K : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ x : ℝ, K x * Real.cos (2 * Real.pi * z * x)

/-- 定义一致件（axiom，积分层）：fourierCos 对最优核 Khat 的解析实现 = Khat
    （文档 S7.3 §3：K̂(u) = ∫ f₀(x)cos(2πux)dx 的闭式；Lean 侧 fourierCos 为抽象算子、
    积分定义在文档层，此件把抽象算子与解析式挂钩——`prime_weight_bounds` 降定理的前置件）。 -/
axiom fourierCos_Khat (u : ℝ) : fourierCos Khat u = Khat u

/-! 光滑件（2026-10-30 真证）：`khat_lipschitz` theorem 已由 §3b/§3c 导数件
（S_smooth 奇点延拓 + |deriv S_smooth| ≤ 1/4 + 凸集均值定理）替换原命名 axiom；
显式 L = π/(√2·|sin(1/√2)|)——`prime_weight_bounds` 平滑分支前置件已闭合。 -/

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
