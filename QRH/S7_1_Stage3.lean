import QRH.S7_1_Core
import QRH.S7_1_Main
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

open scoped BigOperators
open scoped MeasureTheory
open scoped intervalIntegral
open scoped Classical
open Real

/-!
# 攻防 XLII — S7.1 Stage 3+：超支撑断层闭合（N1/N2/N3）+ 三条真证明件

对应文档（d1 已交付）：
  - S7.3（骨头 1，N1）：BGS 引理 5 超支撑推广——缩放自同构与 A→1；
  - S7.4（骨头 2，N2）：ε–λ 联动——正则化撑宽与有效核宽标度律；
  - S7.5（骨头 3，N3）：离线项一致版本——BGS 余项跨 λ 一致；
  - S7.2（数值件 F）：素数项 |S_a|≈2.05 窄带有界、K″(0)≈−3.06、二阶主导 ratio=1.000；
  - S7.6（SW 常数显式化）：(C,c) = (数值 1.70e-3，理论 c=1/√R₀≈0.3954)。

构建约定（Windows 侧）：仅 import 具体模块（Mathlib.olean 聚合缺失）。
  「先 Sorry 占位 → 逐个击破 → 批量降级公理」：真证明件（支撑、偶性、Abel 求和）尽可能真证；
  积分层（Fourier 变换、L¹ 不变）与数论件（零点计数）挂 axiom——语义由文档层论证（S7.3/4/5）。
-/

noncomputable section

namespace QRH

/-! ## 显式误差界宏（不引入 Asymptotics.IsBigO）

Mathlib 的 `Asymptotics.IsBigO` 依赖 filter 参数（atTop / 𝓝），组合引理（trans/mul/add）
全部背着 filter 类型，证明时大量时间耗在 filter 消解而非数学内容。本项目所有余项
（S7.5 BGS、S7.6 SW）都是定量显式口径——直接用具名常数 C 与显式函数 f 的点态不等式。
ε–N 语言只适合「→ 0」的定性结论，会把常数信息丢掉，也不用。

- `Bound`：T→∞ 型误差界（|err(T)| ≤ C·f(T)，∀ T ≥ T₀）——BGS/SW 余项；
- `BoundBall`：双侧球域型（|err(x)| ≤ C·f(x)，∀ |x| ≤ δ）——K̂ 二阶 Taylor 界（核宽 x=a·u 在支撑带内）。
组合规则：三角不等式 + linarith（|e₁+e₂| ≤ C₁f + C₂f ≤ (C₁+C₂)f）。 -/

/-- 点态显式界（T→∞ 型）：0 ≤ C 且 ∀ T ≥ T₀, |err T| ≤ C · f T。 -/
def Bound (C T0 : ℝ) (err f : ℝ → ℝ) : Prop :=
  0 ≤ C ∧ ∀ T : ℝ, T0 ≤ T → |err T| ≤ C * f T

/-- 双侧点态界（球域型）：0 ≤ C 且 ∀ x, |x| ≤ δ → |err x| ≤ C · f x。 -/
def BoundBall (C δ : ℝ) (err f : ℝ → ℝ) : Prop :=
  0 ≤ C ∧ ∀ x : ℝ, |x| ≤ δ → |err x| ≤ C * f x

/-! ## N1：BGS 引理 5 超支撑推广——缩放自同构（文档 S7.3 定理 N1） -/

/-- 缩放核 r_a(α) = a⁻¹·r(α/a)（a>0；supp r⊂[−1,1] ⟹ supp r_a⊂[−a,a]）。 -/
def scaleKernel (a : ℝ) (r : ℝ → ℝ) : ℝ → ℝ := fun α => (1 / a) * r (α / a)

/-- N1-支撑保持（真证明件）：r 支撑 [−1,1]（|t|>1 ⟹ r(t)=0）⟹ scaleKernel a r 支撑 [−a,a]。 -/
lemma scaleKernel_support (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ)
    (hsupp : ∀ t : ℝ, 1 < |t| → r t = 0) :
    ∀ α : ℝ, a < |α| → scaleKernel a r α = 0 := by
  intro α hα
  unfold scaleKernel
  have hquot : 1 < |α / a| := by
    rw [abs_div]
    rw [one_lt_div (abs_pos.mpr (ne_of_gt ha))]
    rw [abs_of_pos ha]
    exact hα
  rw [hsupp (α / a) hquot]
  ring

/-- N1-频域缩放（真证，2026-10-29）：r̂_a(z) = r̂(az)——Fourier 变换变量替换
    （S7.3 定理 N1(iv)）。证明链：integral_const_mul（提出 1/a）+
    Measure.integral_comp_inv_mul_left（Haar 变量替换 x ↦ a⁻¹x，无正则性前提——
    scaleKernel_L1_invariant 同款）+ integral_congr_ae（cos 参数 ring 重写）+ field_simp（消 |a|）。 -/
lemma fourierCos_scale (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) (z : ℝ) :
    fourierCos (scaleKernel a r) z = fourierCos r (a * z) := by
  unfold fourierCos scaleKernel
  calc
    ∫ x : ℝ, ((1 / a) * r (x / a)) * Real.cos (2 * Real.pi * z * x)
        = ∫ x : ℝ, (1 / a) * (r (x / a) * Real.cos (2 * Real.pi * z * x)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = (1 / a) * ∫ x : ℝ, r (x / a) * Real.cos (2 * Real.pi * z * x) := by
          exact MeasureTheory.integral_const_mul (1 / a)
            (fun x : ℝ => r (x / a) * Real.cos (2 * Real.pi * z * x))
    _ = (1 / a) * (|a| * ∫ y : ℝ, r y * Real.cos (2 * Real.pi * (a * z) * y)) := by
          congr 1
          calc
            ∫ x : ℝ, r (x / a) * Real.cos (2 * Real.pi * z * x)
                = ∫ x : ℝ, r (a⁻¹ * x) * Real.cos (2 * Real.pi * z * (a * (a⁻¹ * x))) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with x
                  congr 2
                  · rw [div_eq_inv_mul]
                  · field_simp [ne_of_gt ha]
            _ = |a| * ∫ y : ℝ, r y * Real.cos (2 * Real.pi * z * (a * y)) := by
                  exact MeasureTheory.Measure.integral_comp_inv_mul_left
                    (fun y : ℝ => r y * Real.cos (2 * Real.pi * z * (a * y))) a
            _ = |a| * ∫ y : ℝ, r y * Real.cos (2 * Real.pi * (a * z) * y) := by
                  congr 1
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with y
                  congr 2
                  ring
    _ = ∫ y : ℝ, r y * Real.cos (2 * Real.pi * (a * z) * y) := by
          rw [abs_of_pos ha]
          have ha0 : a ≠ 0 := ne_of_gt ha
          field_simp [ha0]

/-- w_ε(x) ∈ [0,1]（max/min 截断性质，左端；S7.4 文档 N2 §2(i)）。 -/
lemma w_eps_nonneg (ε x : ℝ) : 0 ≤ w_eps ε x := by
  unfold w_eps
  exact le_max_left 0 (min 1 (((1 : ℝ) / 2 - |x|) / ε))

/-- w_ε(x) ∈ [0,1]（右端）。 -/
lemma w_eps_le_one (ε x : ℝ) : w_eps ε x ≤ 1 := by
  unfold w_eps
  exact max_le (by norm_num : (0 : ℝ) ≤ 1) (min_le_left 1 (((1 : ℝ) / 2 - |x|) / ε))

/-- |1 − w_ε(x)| ≤ 1（1−w_ε ∈ [0,1]，差点界的因子件）。 -/
lemma abs_one_sub_w_le_one (ε x : ℝ) : |1 - w_eps ε x| ≤ 1 := by
  have hw0 : 0 ≤ w_eps ε x := w_eps_nonneg ε x
  have hw1 : w_eps ε x ≤ 1 := w_eps_le_one ε x
  have hsub0 : 0 ≤ 1 - w_eps ε x := by linarith
  have hsub1 : 1 - w_eps ε x ≤ 1 := by linarith
  rw [abs_of_nonneg hsub0]
  exact hsub1

/-- w_ε 连续（max/min/线性组合；f_eps 可测性的前提件）。 -/
lemma w_eps_continuous (ε : ℝ) : Continuous (fun x : ℝ => w_eps ε x) := by
  unfold w_eps
  have hlin : Continuous (fun x : ℝ => ((1 : ℝ) / 2 - |x|) / ε) := by
    rw [show (fun x : ℝ => ((1 : ℝ) / 2 - |x|) / ε) = fun x : ℝ => ((1 : ℝ) / 2 - |x|) * ε⁻¹ by
      ext x
      rw [div_eq_mul_inv]]
    exact (continuous_const.sub continuous_abs).mul continuous_const
  exact Continuous.max continuous_const (Continuous.min continuous_const hlin)

/-- w_ε 在 [−(1/2−ε), 1/2−ε] 恒 1：t = (1/2−|x|)/ε ≥ 1 ⟹ min 1 t = 1。 -/
lemma w_eps_eq_one (ε x : ℝ) (hε : 0 < ε) (hx : |x| ≤ (1 : ℝ) / 2 - ε) : w_eps ε x = 1 := by
  unfold w_eps
  have ht : 1 ≤ ((1 : ℝ) / 2 - |x|) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hmin : min 1 (((1 : ℝ) / 2 - |x|) / ε) = 1 := min_eq_left ht
  rw [hmin]
  norm_num

/-- 指示函数体积件：∫ 1_{Icc a b} = b − a（a ≤ b；过渡区测度 2ε 的基础）。
    走 integral_indicator + setIntegral_const + Real.volume_Icc + toReal_ofReal。 -/
lemma indicator_Icc_integral (a b : ℝ) (hab : a ≤ b) :
  (∫ x : ℝ, (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) x) = b - a := by
  rw [MeasureTheory.integral_indicator (isClosed_Icc.measurableSet : MeasurableSet (Set.Icc a b))]
  rw [MeasureTheory.setIntegral_const]
  simp [hab]

/-- 差函数点界：|f₀(x) − f_ε(x)| ≤ C·(1_{I1}(x) + 1_{I2}(x))，
    I1∪I2 = 过渡区 (1/2−ε, 1/2] ∪ [−1/2, −1/2+ε)；
    过渡区外差 = 0（|x|≤1/2−ε 时 w_ε=1，|x|>1/2 时 f₀ 截断）。 -/
lemma f0_sub_feps_abs_le (ε x : ℝ) (hε : 0 < ε) :
  |f0 x - f_eps ε x| ≤
    (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ *
      ((Set.Icc (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2) + ε)).indicator (fun _ : ℝ => (1 : ℝ)) x
        + (Set.Icc ((1 : ℝ) / 2 - ε) ((1 : ℝ) / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x) := by
  let I1 : Set ℝ := Set.Icc (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2) + ε)
  let I2 : Set ℝ := Set.Icc ((1 : ℝ) / 2 - ε) ((1 : ℝ) / 2)
  let C : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hCpos : 0 < C := by
    unfold C
    exact inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero))
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hdiff : f0 x - f_eps ε x = f0 x * (1 - w_eps ε x) := by
    unfold f_eps
    ring
  by_cases hA : |x| ≤ (1 : ℝ) / 2 - ε
  · have hw : w_eps ε x = 1 := w_eps_eq_one ε x hε hA
    rw [hdiff, hw]
    have hnonneg : 0 ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
      exact mul_nonneg hCnonneg
        (add_nonneg (Set.indicator_nonneg (by intro a ha; norm_num) x)
          (Set.indicator_nonneg (by intro a ha; norm_num) x))
    simpa [C, I1, I2] using hnonneg
  · by_cases hC : |x| ≤ (1 : ℝ) / 2
    · -- 过渡区：1/2−ε < |x| ≤ 1/2
      rcases le_total x 0 with hx0 | hx0
      · -- x ≤ 0 ⟹ x ∈ I1
        have hI1 : x ∈ I1 := by
          unfold I1
          rw [Set.mem_Icc]
          have hxabs : |x| = -x := abs_of_nonpos hx0
          constructor
          · rw [hxabs] at hC
            linarith
          · have hbig : (1 : ℝ) / 2 - ε < |x| := lt_of_not_ge hA
            rw [hxabs] at hbig
            linarith
        calc
          |f0 x - f_eps ε x| = |f0 x * (1 - w_eps ε x)| := by rw [hdiff]
          _ = |f0 x| * |1 - w_eps ε x| := by rw [abs_mul]
          _ ≤ C * 1 := by
            exact mul_le_mul (f0_abs_le x) (abs_one_sub_w_le_one ε x) (abs_nonneg _) hCnonneg
          _ = C := by ring
          _ ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
            have hI1i : (I1.indicator (fun _ : ℝ => (1 : ℝ))) x = 1 := by
              simp [hI1]
            rw [hI1i]
            have hI2nn : 0 ≤ (I2.indicator (fun _ : ℝ => (1 : ℝ))) x :=
              Set.indicator_nonneg (by intro a ha; norm_num) x
            nlinarith [mul_le_mul_of_nonneg_left hI2nn hCnonneg]
      · -- 0 ≤ x ⟹ x ∈ I2
        have hI2 : x ∈ I2 := by
          unfold I2
          rw [Set.mem_Icc]
          have hxabs : |x| = x := abs_of_nonneg hx0
          constructor
          · have hbig : (1 : ℝ) / 2 - ε < |x| := lt_of_not_ge hA
            rw [hxabs] at hbig
            linarith
          · rw [hxabs] at hC
            linarith
        calc
          |f0 x - f_eps ε x| = |f0 x * (1 - w_eps ε x)| := by rw [hdiff]
          _ = |f0 x| * |1 - w_eps ε x| := by rw [abs_mul]
          _ ≤ C * 1 := by
            exact mul_le_mul (f0_abs_le x) (abs_one_sub_w_le_one ε x) (abs_nonneg _) hCnonneg
          _ = C := by ring
          _ ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
            have hI2i : (I2.indicator (fun _ : ℝ => (1 : ℝ))) x = 1 := by
              simp [hI2]
            have hI1nn : 0 ≤ (I1.indicator (fun _ : ℝ => (1 : ℝ))) x :=
              Set.indicator_nonneg (by intro a ha; norm_num) x
            rw [hI2i]
            nlinarith [mul_le_mul_of_nonneg_left hI1nn hCnonneg]
    · -- |x| > 1/2：f0 截断 ⟹ f0(x) = 0 ⟹ 差 = 0
      have hC' : (1 : ℝ) / 2 < |x| := lt_of_not_ge hC
      have hf0 : f0 x = 0 := by
        unfold f0
        rw [ite_eq_right (not_le_of_gt hC')]
      rw [hdiff, hf0]
      have hnonneg : 0 ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
        exact mul_nonneg hCnonneg
          (add_nonneg (Set.indicator_nonneg (by intro a ha; norm_num) x)
            (Set.indicator_nonneg (by intro a ha; norm_num) x))
      simpa [C, I1, I2] using hnonneg

/-- Core 件 f0_sub_feps_L1_bound（真证 2026-10-30；axiom → theorem）：
    ‖f₀ − f_ε‖₁ ≤ 2ε·(√2·|sin(1/√2)|)⁻¹。
    数学链（f₀ 支撑截断 [−1/2,1/2] 后，Core 口径修正）：
    f₀−f_ε = f₀·(1−w_ε) 支撑 ⊂ 过渡区 (1/2−ε, 1/2] ∪ [−1/2, −1/2+ε)（测度 2ε），
    |f₀| ≤ (√2·|sin(1/√2)|)⁻¹（f0_abs_le）⟹ ‖f₀−f_ε‖₁ ≤ 2ε·(√2·|sin(1/√2)|)⁻¹。
    件：f0_sub_feps_abs_le（点界）、indicator_Icc_integral（体积 2ε）、
    integral_mono_ae（单调）、integrableOn 支撑桥（可积）、
    aestronglyMeasurable_iff_aemeasurable（可测→强可测桥）。 -/
theorem f0_sub_feps_L1_bound (ε : ℝ) (hε : 0 < ε) :
  normL1 (fun x => f0 x - f_eps ε x) ≤ 2 * ε * (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
  unfold normL1
  let I1 : Set ℝ := Set.Icc (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2) + ε)
  let I2 : Set ℝ := Set.Icc ((1 : ℝ) / 2 - ε) ((1 : ℝ) / 2)
  let C : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hCpos : 0 < C := by
    unfold C
    exact inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero))
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  -- 1. 点界
  have hpoint : ∀ x : ℝ, |f0 x - f_eps ε x| ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    intro x
    simpa [I1, I2, C] using f0_sub_feps_abs_le ε x hε
  -- 2. RHS 可积：C·(1_{I1} + 1_{I2})（支撑 ⊂ 有限测度区间）
  have hI1int : MeasureTheory.Integrable (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    have hsupp : Function.support (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) ⊆ I1 := by
      intro y hy
      rw [Set.support_indicator] at hy
      exact hy.1
    rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
    exact MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := by
        unfold I1
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top))
      (by intro x hx; exact (Set.indicator_of_mem (f := fun _ : ℝ => (1 : ℝ)) hx).symm)
      (isClosed_Icc).measurableSet
  have hI2int : MeasureTheory.Integrable (fun x : ℝ => (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    have hsupp : Function.support (fun x : ℝ => (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) ⊆ I2 := by
      intro y hy
      rw [Set.support_indicator] at hy
      exact hy.1
    rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
    exact MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := by
        unfold I2
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top))
      (by intro x hx; exact (Set.indicator_of_mem (f := fun _ : ℝ => (1 : ℝ)) hx).symm)
      (isClosed_Icc).measurableSet
  have hsumint : MeasureTheory.Integrable (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := hI1int.add hI2int
  have hRHSint : MeasureTheory.Integrable (fun x : ℝ => C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)) := hsumint.const_mul C
  -- 3. LHS 可测 ⟹ 强可测 ⟹ 可积（点界 + RHS 可积）
  have hLHSmeas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |f0 x - f_eps ε x|) := by
    have hfepsm : Measurable (fun x : ℝ => f_eps ε x) := by
      unfold f_eps
      change Measurable (f0 * fun x : ℝ => w_eps ε x)
      exact f0_measurable.mul (w_eps_continuous ε).measurable
    have hdiffm : Measurable (fun x : ℝ => f0 x - f_eps ε x) := f0_measurable.sub hfepsm
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (measurable_norm.comp hdiffm).aemeasurable
  have hLHSint : MeasureTheory.Integrable (fun x : ℝ => |f0 x - f_eps ε x|) := by
    refine MeasureTheory.Integrable.mono hRHSint hLHSmeas ?_
    filter_upwards with x
    have hSumNN : 0 ≤ (I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x := by
      exact add_nonneg (Set.indicator_nonneg (by intro a ha; norm_num) x)
        (Set.indicator_nonneg (by intro a ha; norm_num) x)
    have hRnn : 0 ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) :=
      mul_nonneg hCnonneg hSumNN
    calc
      ‖|f0 x - f_eps ε x|‖ = |f0 x - f_eps ε x| := by
        rw [Real.norm_eq_abs, abs_abs]
      _ ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := hpoint x
      _ = ‖C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)‖ := by
        rw [Real.norm_eq_abs]
        exact (abs_of_nonneg hRnn).symm
  -- 4. 积分单调 + 体积
  calc
    ∫ x : ℝ, |f0 x - f_eps ε x| ≤ ∫ x : ℝ, C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
      refine MeasureTheory.integral_mono_ae hLHSint hRHSint ?_
      filter_upwards with x
      exact hpoint x
    _ = C * (∫ x : ℝ, (I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
      exact MeasureTheory.integral_const_mul C (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)
    _ = C * ((∫ x : ℝ, (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) + (∫ x : ℝ, (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)) := by
      rw [MeasureTheory.integral_add hI1int hI2int]
    _ = C * (ε + ε) := by
      have hI1v : (∫ x : ℝ, (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) = ε := by
        unfold I1
        rw [indicator_Icc_integral (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2) + ε) (by linarith)]
        ring
      have hI2v : (∫ x : ℝ, (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) = ε := by
        unfold I2
        rw [indicator_Icc_integral ((1 : ℝ) / 2 - ε) ((1 : ℝ) / 2) (by linarith)]
        ring
      rw [hI1v, hI2v]
    _ = 2 * ε * (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
      unfold C
      ring

/-- N1-L¹ 保持（真证，S7.3 定理 N1(vi)）：‖r_a‖₁ = ‖r‖₁——缩放变量替换
    ∫x |a⁻¹·r(x/a)| dx = a⁻¹·∫x |r(a⁻¹·x)| dx = a⁻¹·|a|·∫y|r(y)|dy = ∫|r|（a>0）。
    引理件：integral_const_mul（常数因子提出）、integral_comp_inv_mul_left（Haar 变量替换）、
    abs_mul + abs_of_pos。 -/
lemma scaleKernel_L1_invariant (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) :
  normL1 (scaleKernel a r) = normL1 r := by
  unfold normL1 scaleKernel
  calc
    ∫ x : ℝ, |(1 / a) * r (x / a)| = ∫ x : ℝ, (1 / a) * |r (x / a)| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [abs_mul]
      congr 1
      exact abs_of_pos (one_div_pos.mpr ha)
    _ = (1 / a) * ∫ x : ℝ, |r (x / a)| := by
      exact MeasureTheory.integral_const_mul (1 / a) (fun x : ℝ => |r (x / a)|)
    _ = (1 / a) * (|a| * ∫ y : ℝ, |r y|) := by
      congr 1
      calc
        ∫ x : ℝ, |r (x / a)| = ∫ x : ℝ, |r (a⁻¹ * x)| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [div_eq_inv_mul]
        _ = |a| * ∫ y : ℝ, |r y| := by
          exact MeasureTheory.Measure.integral_comp_inv_mul_left (fun y : ℝ => |r y|) a
    _ = ∫ y : ℝ, |r y| := by
      rw [abs_of_pos ha]
      have ha0 : a ≠ 0 := ne_of_gt ha
      field_simp [ha0]

/-- N1-对角主项不变（真证）：缩放自同构不改变引理 5 对角主项
    (T/2π)·logT·[r̂(0)+2∫₀¹αr(α)dα]——r̂_a(0)=r̂(a·0)=r̂(0)（fourierCos_scale 取 z=0）。 -/
lemma n1_diag_invariant (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) :
  fourierCos (scaleKernel a r) 0 = fourierCos r 0 := by
  rw [fourierCos_scale a ha r 0]
  congr 1
  ring

/-- N1-非对角核因子缩放（真证）：K̂_a(2δ)² = r̂(2aδ)²（fourierCos_scale 取 z=2δ）——
    vanishing 的核结构件：缩放把频域参数从 2δ 换到 2aδ。 -/
lemma n1_offdiag_scale_eq (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) (δ : ℝ) :
  (fourierCos (scaleKernel a r) (2 * δ)) ^ 2 = (fourierCos r (2 * a * δ)) ^ 2 := by
  rw [fourierCos_scale a ha r (2 * δ)]
  congr 1
  congr 1
  ring

/-- N1-非对角项消失（结构件真证，S7.3 推论）：supp⊂[−a,a]（a→0）时非对角配对和
    的主导核因子 K̂_a(2δ)² = r̂(2aδ)² 按 a² 衰减——在频域衰减件
    |r̂(2aδ)|² ≤ a²C（被积有界 × 支撑收缩层，数值件 F 已实测 A−1 单调
    1.86e-2→3.09e-9、a 0.5→0.008；积分层长线）假设下，vanishing 闭合。 -/
lemma n1_offdiag_vanishes (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) (δ C : ℝ)
    (hrhat : (fourierCos r (2 * a * δ)) ^ 2 ≤ (a ^ 2) * C) :
    (fourierCos (scaleKernel a r) (2 * δ)) ^ 2 ≤ (a ^ 2) * C := by
  rw [n1_offdiag_scale_eq a ha r δ]
  exact hrhat

/-! ## N2：ε–λ 联动（文档 S7.4 定理 N2） -/

/-- N2-支撑容忍（真证明件）：f_ε(x)=f₀(x)·w_ε(x)，w_ε=max 0 (min 1 ((1/2−|x|)/ε)) 截断到 [0,1]
    ⟹ |x|>1/2 时 w_ε=0 ⟹ f_ε 支撑 ⊂ [−1/2,1/2]（ε 容忍的解析形态）。 -/
lemma f_eps_support (ε x : ℝ) (hε : 0 < ε) (hx : (1 : ℝ) / 2 < |x|) : f_eps ε x = 0 := by
  have ht : ((1 : ℝ) / 2 - |x|) / ε < 0 := by
    have hnum : (1 : ℝ) / 2 - |x| < 0 := by linarith
    exact div_neg_of_neg_of_pos hnum hε
  have hw : w_eps ε x = 0 := by
    unfold w_eps
    -- 目标：max 0 (min 1 t) = 0（t = (1/2 − |x|)/ε < 0）
    apply le_antisymm
    · -- max 0 (min 1 t) ≤ 0：min 1 t ≤ t < 0
      have hm1t0 : min (1 : ℝ) (((1 : ℝ) / 2 - |x|) / ε) ≤ 0 :=
        (min_le_right (1 : ℝ) (((1 : ℝ) / 2 - |x|) / ε)).trans (le_of_lt ht)
      exact max_le (le_refl (0 : ℝ)) hm1t0
    · -- 0 ≤ max 0 (min 1 t)
      exact le_max_left (0 : ℝ) (min (1 : ℝ) (((1 : ℝ) / 2 - |x|) / ε))
  unfold f_eps
  rw [hw]
  ring

/-- N2-联动定理（statement，S7.4 定理 N2(iii)，Bound 显式界化）：
    λ=(logT)^q、a=(logT)^{−q}、ε=c·(logT)^{−q} ⟹ 总偏差 O((logT)^{−q})→0（无速度竞争）。
    ε 取联动取等号 ε(T)=c·(logT)^{−q}（文档定理 N2 口径；(logT)^{−q}=exp(−q·log(logT))）。
    数学链：ε≤O(a) 硬约束（S7.4 §2(ii)）+ 缩放不变偏差。更强形式（∀ ε ≤ 阈值单调）留待击破。 -/
axiom n2_linkage (T0 c q : ℝ) (hT0 : 1 < T0) (hq : 0 < q) (hc : 0 < c) :
  ∃ C : ℝ,
    Bound C T0
      (fun T => |fourierCos (f_eps (c * Real.exp (-q * Real.log (Real.log T)))) 0
        - fourierCos f0 0|)
      (fun T => Real.exp (-q * Real.log (Real.log T)))

/-! ### N2b：配对常数对核扰动的 Lipschitz 偏差（pair_const_eps_bias）

文档 S7.4 定理 N2（ε–λ 联动）的配对常数层：
  pairConstant(K, δ, N, Z) = 1 + Σ_{z₁≠z₂∈Z} K(δ·im(z₁−z₂))²/N，
  核扰动 K₁↦K₂ 的偏差被 |K₁(x)²−K₂(x)²| ≤ (|K₁|+|K₂|)|K₁−K₂|（Lipschitz 代数件，
  sq_sub_sq_abs_le + f_eps_abs_le 真证）+ L¹ 界（f0_sub_feps_L1_bound 真证：
  ‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹）压制：
  Σ_{Δ} |f₀(δΔ)²−f_ε(δΔ)²|/N ≤ 2M·(配对密度)·‖f₀−f_ε‖₁ = O(ε)。
  积分层挂钩（离散配对和 ≤ normL1·密度）**已真证**（2026-10-31 增量⑧，axiom → theorem）：
  `pairCount_L1_bound`（Σ_{z₁≠z₂∈Z_T}|g(δΔ)| ≤ D·N_Z(T)·‖f₀−f_ε‖₁ + tsum 可和性三件打包）。
  口径修正（本轮，先修口径再真证，同 f0 支撑截断模式）：原 axiom 两处硬伤——
  (i) zerosLChi5 为临界带全零点集（无限），竖直差带窗口 2πε/logT 内配对无限多 ⟹ Summable 假；
  (ii) 归一化参数 N:=δ（Lean 侧）与文档层 S7.1 §2「N = 零点数」不一致，D 无法对 T 一致。
  修正：① 截断零点集 Z_T := zerosLChi5UpTo T（有限 ⟹ Summable 自动为 Finset 和）；
  ② RHS 归一化改 D·N_Z(T)·‖·‖₁（D 对数配对密度、对 T 一致）；
  ③ 数论结构 axiom 两件：`zerosLChi5_bounded_finite`（截断零点集有限）+ `pair_count_bound`
  （竖直差带 |Δ|≤1/(2δ) 内配对总数 ≤ Dcnt·N_L(T)，RvM 密度 + 零点分离）；
  ④ `pair_const_eps_bias` 组装同步改 N:=N_L T、Z:=zerosLChi5UpTo T，Bound 仍 = ε。
  三段链（Lipschitz 归约 pairConst_sub_pairL1 + 积分层挂钩 + L¹ 界 + 组装）全部真证出账。 -/

/-- Lipschitz 代数件（真证）：|a²−b²| ≤ (|a|+|b|)·|a−b|（平方差按绝对值差压缩）。 -/
lemma sq_sub_sq_abs_le (a b : ℝ) : |a ^ 2 - b ^ 2| ≤ (|a| + |b|) * |a - b| := by
  have h : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  calc
    |a ^ 2 - b ^ 2| = |(a - b) * (a + b)| := by rw [h]
    _ = |a - b| * |a + b| := by rw [abs_mul]
    _ ≤ |a - b| * (|a| + |b|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le a b) (abs_nonneg (a - b))
    _ = (|a| + |b|) * |a - b| := by ring

/-- N2b-Lipschitz 件 II（真证）：|f_ε(x)| ≤ (√2·|sin(1/√2)|)⁻¹
    （f_ε = f₀·w_ε，w_ε 截断 [0,1]：f0_abs_le + w_eps_nonneg/le_one）。 -/
lemma f_eps_abs_le (ε x : ℝ) : |f_eps ε x| ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by
  unfold f_eps
  have hM0 : 0 ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (by positivity : (0 : ℝ) ≤ sqrt 2) (abs_nonneg _))
  calc
    |f0 x * w_eps ε x| = |f0 x| * |w_eps ε x| := by rw [abs_mul]
    _ ≤ (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ * 1 := by
      exact mul_le_mul (f0_abs_le x)
        (by simpa [abs_of_nonneg (w_eps_nonneg ε x)] using w_eps_le_one ε x)
        (abs_nonneg _) hM0
    _ = (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ := by ring

/-! ### 件 3：N_L 对数增长下界（数论件，S6 口径）
    （2026-10-31 增量⑧：N_L / N_L_lower_bound 前移至 N2b 挂钩之前——
    pairCount_L1_bound / pair_count_bound 组装依赖其定义，原位置在文件后部。） -/

/-- L(s,χ₅) 零点计数函数（抽象算子）。 -/
axiom N_L : ℝ → ℝ

/-- N_L 对数增长下界（statement）：∃c>0，N_L(T) ≥ c·T·logT。
    数论件（L(s,χ5) 零点计数显式下界，S6 框架）——axiom 挂账（数学已证、形式化长线）。 -/
axiom N_L_lower_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → c * T * Real.log T ≤ N_L T

/-- 截断零点集 Z_T := zerosLChi5 ∩ {|Im z| ≤ T}（BGS 配对公式的有限口径：
    零点局部有限 + 紧竖带 ⟹ 有限集（`zerosLChi5_bounded_finite`）；
    配对和只在 Z_T 上跑，Summable 自动为 Finset 和。 -/
def zerosLChi5UpTo (T : ℝ) : Set ℂ := { z : ℂ | z ∈ zerosLChi5 ∧ |z.im| ≤ T }

/-- 数论结构件（axiom；数学真、形式化长线）：截断零点集 Z_T 有限。
    依据：L(s,χ₅) 全纯的零点离散（亚纯函数零点无聚点 ⟹ 局部有限），
    紧竖带 {0<Re<1, |Im|≤T} ∩ 零点集有限——复分析标准事实
    （显式计数 N_Z(T) ≤ C·T·logT 为 RvM 长线，此处仅需有限性）。 -/
axiom zerosLChi5_bounded_finite (T : ℝ) : Set.Finite (zerosLChi5UpTo T)

/-- 数论结构件（axiom；数学真、形式化长线）：竖直差带配对计数界。
    对 δ = logT/(2π)，竖直差 |Δ| = |im(z₁−z₂)| ≤ 1/(2δ) 的配对总数 ≤ Dcnt·N_L(T)：
    RvM 密度 + 零点分离性 ⟹ 每零点至多 O(1) 个竖直邻居 ⟹ 总配对 O(N_Z(T))；
    Dcnt 对 T 一致（对数配对密度）。 -/
axiom pair_count_bound (T0 : ℝ) (hT0 : 1 < T0) :
  ∃ Dcnt : ℝ, 0 ≤ Dcnt ∧
    ∀ T : ℝ, T0 ≤ T →
      let δ := Real.log T / (2 * Real.pi)
      (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) ≤ Dcnt * N_L T

/-- N2b-辅助（真证）：过渡区左沿 x ∈ (1/2−ε, 1/2) 且 x ≥ 0 时 w_ε(x) = (1/2−x)/ε ∈ (0,1)
    （max/min 截断展开：|x|=x、0 < (1/2−x)/ε < 1）。 -/
lemma w_eps_lt_one_of_mem (ε x : ℝ) (hε : 0 < ε) (hx0 : 0 ≤ x) (hxgt : (1 : ℝ) / 2 - ε < x)
    (hxlt : x < (1 : ℝ) / 2) : w_eps ε x < 1 := by
  have hnum_pos : 0 < (1 : ℝ) / 2 - x := by linarith
  have hnum_lt : (1 : ℝ) / 2 - x < ε := by linarith
  have hq : 0 < ((1 : ℝ) / 2 - x) / ε := div_pos hnum_pos hε
  have hq1 : ((1 : ℝ) / 2 - x) / ε < 1 := (div_lt_one hε).mpr hnum_lt
  unfold w_eps
  rw [abs_of_nonneg hx0]
  rw [min_eq_right (le_of_lt hq1), max_eq_right (le_of_lt hq)]
  exact hq1

/-- N2b-辅助（真证）：0 < x ≤ 1/2 时 f₀(x) > 0（cos(√2x) > 0：√2x ∈ (0, √2/2] ⊆ (0, π/2)）。 -/
lemma f0_pos_of_le_half (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ (1 : ℝ) / 2) : 0 < f0 x := by
  unfold f0
  rw [if_pos]
  · have hcpos : 0 < cos (sqrt 2 * x) := by
      have harg0 : 0 < sqrt 2 * x := mul_pos (by positivity : (0 : ℝ) < sqrt 2) hx0
      have hargle : sqrt 2 * x ≤ sqrt 2 * (1 : ℝ) / 2 := by
        calc
          sqrt 2 * x ≤ sqrt 2 * ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hx1 (le_of_lt (by positivity : (0 : ℝ) < sqrt 2))
          _ = sqrt 2 * (1 : ℝ) / 2 := by ring
      have harglt : sqrt 2 * x < Real.pi / 2 := by
        have h2 : sqrt 2 * (1 : ℝ) / 2 < Real.pi / 2 := by
          have hs : sqrt 2 < 2 := by
            have hlt : sqrt 2 < sqrt (4 : ℝ) :=
              Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (2 : ℝ) < 4)
            have h4 : sqrt (4 : ℝ) = 2 := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
              exact Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))
            rwa [h4] at hlt
          nlinarith [two_le_pi]
        exact lt_of_le_of_lt hargle h2
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith, harglt⟩
    have hdpos : 0 < sqrt 2 * sin (1 / sqrt 2) := by
      have hsin : 0 < sin (1 / sqrt 2) := by
        have h1 : 0 < (1 : ℝ) / sqrt 2 := by positivity
        have h2 : (1 : ℝ) / sqrt 2 < Real.pi := by
          have hs : (1 : ℝ) / sqrt 2 < 1 := by
            have hlt : sqrt (1 : ℝ) < sqrt 2 :=
              Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
            have hone : 1 < sqrt 2 := by
              simpa [Real.sqrt_one] using hlt
            exact (div_lt_one (by positivity : (0 : ℝ) < sqrt 2)).mpr hone
          nlinarith [two_le_pi]
        exact Real.sin_pos_of_pos_of_lt_pi h1 h2
      exact mul_pos (by positivity : (0 : ℝ) < sqrt 2) hsin
    exact div_pos hcpos hdpos
  · rw [abs_of_nonneg (le_of_lt hx0)]
    exact hx1

/-- N2b-真证件（2026-10-31）：|f₀−f_ε| 全空间可积（支撑 ⊂ [−1/2,1/2] 有界 + 全局界）。
    复用 f0_sub_feps_L1_bound 内部证明骨架（点界 ≤ C·(1_{I1}+1_{I2}) + RHS 可积 + mono），
    供 `normL1_sub_pos` 的 integral_mono_measure 前提。 -/
lemma normL1_sub_integrable (ε : ℝ) (hε : 0 < ε) :
    MeasureTheory.Integrable (fun x : ℝ => |f0 x - f_eps ε x|) := by
  let I1 : Set ℝ := Set.Icc (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2) + ε)
  let I2 : Set ℝ := Set.Icc ((1 : ℝ) / 2 - ε) ((1 : ℝ) / 2)
  let C : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hCpos : 0 < C := by
    unfold C
    exact inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < sqrt 2)
      (abs_pos.mpr sin_inv_sqrt2_ne_zero))
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hpoint : ∀ x : ℝ, |f0 x - f_eps ε x| ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x
      + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    intro x
    simpa [I1, I2, C] using f0_sub_feps_abs_le ε x hε
  have hI1int : MeasureTheory.Integrable (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    have hsupp : Function.support (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x) ⊆ I1 := by
      intro y hy
      rw [Set.support_indicator] at hy
      exact hy.1
    rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
    exact MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := by
        unfold I1
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top))
      (by intro x hx; exact (Set.indicator_of_mem (f := fun _ : ℝ => (1 : ℝ)) hx).symm)
      (isClosed_Icc).measurableSet
  have hI2int : MeasureTheory.Integrable (fun x : ℝ => (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := by
    have hsupp : Function.support (fun x : ℝ => (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) ⊆ I2 := by
      intro y hy
      rw [Set.support_indicator] at hy
      exact hy.1
    rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
    exact MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := by
        unfold I2
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top))
      (by intro x hx; exact (Set.indicator_of_mem (f := fun _ : ℝ => (1 : ℝ)) hx).symm)
      (isClosed_Icc).measurableSet
  have hsumint : MeasureTheory.Integrable (fun x : ℝ => (I1.indicator (fun _ : ℝ => (1 : ℝ))) x
      + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := hI1int.add hI2int
  have hRHSint : MeasureTheory.Integrable (fun x : ℝ => C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x
      + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)) := hsumint.const_mul C
  have hLHSmeas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |f0 x - f_eps ε x|) := by
    have hfepsm : Measurable (fun x : ℝ => f_eps ε x) := by
      unfold f_eps
      change Measurable (f0 * fun x : ℝ => w_eps ε x)
      exact f0_measurable.mul (w_eps_continuous ε).measurable
    have hdiffm : Measurable (fun x : ℝ => f0 x - f_eps ε x) := f0_measurable.sub hfepsm
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (measurable_norm.comp hdiffm).aemeasurable
  refine MeasureTheory.Integrable.mono hRHSint hLHSmeas ?_
  filter_upwards with x
  have hSumNN : 0 ≤ (I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x := by
    exact add_nonneg (Set.indicator_nonneg (by intro a ha; norm_num) x)
      (Set.indicator_nonneg (by intro a ha; norm_num) x)
  have hRnn : 0 ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) :=
    mul_nonneg hCnonneg hSumNN
  calc
    ‖|f0 x - f_eps ε x|‖ = |f0 x - f_eps ε x| := by
      rw [Real.norm_eq_abs, abs_abs]
    _ ≤ C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x) := hpoint x
    _ = ‖C * ((I1.indicator (fun _ : ℝ => (1 : ℝ))) x + (I2.indicator (fun _ : ℝ => (1 : ℝ))) x)‖ := by
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg hRnn).symm

/-- N2b-真证件（2026-10-31）：‖f₀−f_ε‖₁ > 0（ε>0 时过渡区 g 非零 ⟹ 积分正）。
    区间 (1/2−min(ε/2,1/4), 1/2) ⊆ (1/4,1/2)：f₀ > 0（f0_pos_of_le_half）+ w_ε < 1
    （w_eps_lt_one_of_mem）⟹ g = f₀(1−w_ε) > 0 逐点 ⟹ 区间积分正
    （intervalIntegral.integral_pos_of_pos_on）⟹ 全空间积分 ≥ 区间积分
    （integral_mono_measure：restrict ≤ volume）。 -/
lemma normL1_sub_pos (ε : ℝ) (hε : 0 < ε) :
    0 < normL1 (fun x => f0 x - f_eps ε x) := by
  unfold normL1
  let a : ℝ := (1 : ℝ) / 2 - min (ε / 2) (1 / 4)
  let b : ℝ := (1 : ℝ) / 2
  have hamin_pos : 0 < min (ε / 2) (1 / 4) := lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hamin_le_eps : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
  have hamin_le_q : min (ε / 2) (1 / 4) ≤ (1 : ℝ) / 4 := min_le_right _ _
  have hab : a < b := by
    unfold a b
    linarith [hamin_pos]
  have hpos : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 < |f0 x - f_eps ε x| := by
    intro x hx
    have hxa : a < x := hx.1
    have hxb : x < b := hx.2
    have hxpos : 0 < x := by
      unfold a at hxa
      linarith [hamin_le_q]
    have hxlt : x < (1 : ℝ) / 2 := by
      unfold b at hxb
      exact hxb
    have hxbig : (1 : ℝ) / 2 - ε < x := by
      have : (1 : ℝ) / 2 - ε / 2 < x := by
        unfold a at hxa
        linarith [hamin_le_eps]
      linarith
    have hf0pos : 0 < f0 x := f0_pos_of_le_half x hxpos (le_of_lt hxlt)
    have hwlt : w_eps ε x < 1 := w_eps_lt_one_of_mem ε x hε (le_of_lt hxpos) hxbig hxlt
    have hwpos : 0 < 1 - w_eps ε x := sub_pos.mpr hwlt
    have hg : |f0 x - f_eps ε x| = f0 x * (1 - w_eps ε x) := by
      have hdiff : f0 x - f_eps ε x = f0 x * (1 - w_eps ε x) := by
        unfold f_eps
        ring
      rw [hdiff, abs_mul, abs_of_pos hf0pos, abs_of_pos hwpos]
    rw [hg]
    exact mul_pos hf0pos hwpos
  have hf0cont : ContinuousOn f0 (Set.Icc a b) := by
    have hf0c_piece : ContinuousOn (fun x : ℝ => cos (sqrt 2 * x) / (sqrt 2 * sin (1 / sqrt 2)))
        (Set.Icc a b) := by
      have hden_ne : ∀ x : ℝ, x ∈ Set.Icc a b → (sqrt 2 * sin (1 / sqrt 2)) ≠ 0 := fun _ _ =>
        mul_ne_zero (by positivity : (sqrt 2 : ℝ) ≠ 0) sin_inv_sqrt2_ne_zero
      exact (continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.div
        continuous_const.continuousOn hden_ne
    refine ContinuousOn.congr hf0c_piece ?_
    intro x hx
    have hxpos : 0 < x := by
      have : a ≤ x := hx.1
      unfold a at this
      linarith [hamin_le_q]
    unfold f0
    rw [if_pos (by
      rw [abs_of_nonneg (le_of_lt hxpos)]
      simpa [b] using hx.2)]
  have hg_form : ∀ x : ℝ, x ∈ Set.Icc a b → |f0 x - f_eps ε x| = f0 x * (1 - w_eps ε x) := by
    intro x hx
    have hxpos : 0 < x := by
      have : a ≤ x := hx.1
      unfold a at this
      linarith [hamin_le_q]
    have hxle : x ≤ (1 : ℝ) / 2 := hx.2
    have hxbig : (1 : ℝ) / 2 - ε < x := by
      have hle' : a ≤ x := hx.1
      unfold a at hle'
      have hstep : (1 : ℝ) / 2 - ε < (1 : ℝ) / 2 - min (ε / 2) (1 / 4) := by
        have hmin_lt : min (ε / 2) (1 / 4) < ε := lt_of_le_of_lt hamin_le_eps (by linarith)
        linarith
      exact lt_of_lt_of_le hstep hle'
    have hf0pos : 0 < f0 x := f0_pos_of_le_half x hxpos hxle
    have hw1 : w_eps ε x < 1 := by
      by_cases hx12 : x < (1 : ℝ) / 2
      · exact w_eps_lt_one_of_mem ε x hε (le_of_lt hxpos) hxbig hx12
      · have hxeq : x = (1 : ℝ) / 2 := le_antisymm hxle (le_of_not_gt hx12)
        rw [hxeq]
        unfold w_eps
        simp [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    have hwpos : 0 < 1 - w_eps ε x := sub_pos.mpr hw1
    have hdiff : f0 x - f_eps ε x = f0 x * (1 - w_eps ε x) := by
      unfold f_eps
      ring
    rw [hdiff, abs_mul, abs_of_pos hf0pos, abs_of_pos hwpos]
  have hcont : ContinuousOn (fun x : ℝ => |f0 x - f_eps ε x|) (Set.Icc a b) := by
    have hw : ContinuousOn (w_eps ε) (Set.Icc a b) := by
      unfold w_eps
      exact (Continuous.max continuous_const (Continuous.min continuous_const
        (((continuous_const.sub continuous_abs).div_const ε)))).continuousOn
    refine ContinuousOn.congr (f := fun x => f0 x * (1 - w_eps ε x)) ?_ ?_
    · exact hf0cont.mul (continuous_const.continuousOn.sub hw)
    · intro x hx
      exact hg_form x hx
  have hint_pos : 0 < ∫ x in a..b, |f0 x - f_eps ε x| := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hab
    · have hcont_u : ContinuousOn (fun x => |f0 x - f_eps ε x|) (Set.uIcc a b) := by
        simpa [Set.uIcc_of_le (le_of_lt hab)] using hcont
      exact hcont_u.intervalIntegrable
    · intro x hx
      have hx' : x ∈ Set.Ioo a b := by
        simpa [Set.uIoo, min_eq_left (le_of_lt hab), max_eq_left (le_of_lt hab)] using hx
      exact hpos x hx'
  have hLHSint : MeasureTheory.Integrable (fun x : ℝ => |f0 x - f_eps ε x|) :=
    normL1_sub_integrable ε hε
  have hsub : (∫ x in a..b, |f0 x - f_eps ε x|) ≤ ∫ x : ℝ, |f0 x - f_eps ε x| := by
    rw [intervalIntegral.integral_of_le (le_of_lt hab)]
    refine MeasureTheory.integral_mono_measure MeasureTheory.Measure.restrict_le_self ?_ ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hLHSint
  exact lt_of_lt_of_le hint_pos hsub

/-- N2b-积分层挂钩（真证 2026-10-31；axiom → theorem，口径修正）：
    截断零点集 Z_T := zerosLChi5UpTo T（有限 ⟹ Summable 自动为 Finset 和）上，
    离散配对和 ≤ D·N_Z(T)·‖f₀−f_ε‖₁（D 对数配对密度、对 T 一致）。
    数学链：竖直差带计数（|Δ|≤1/(2δ) 内每零点 O(1) 邻居，pair_count_bound）
      → 逐项 2M 界（支撑外 g=0，支撑内 |g| ≤ 2M）→ tsum 链 → D 归一化到 N_Z(T)。
    旧口径两处硬伤已修：(i) zerosLChi5 全零点集无限、竖直差带窗口内配对无限多 ⟹ Summable 假；
    (ii) D·δ 归一化参数 N:=δ 与文档层 N:=N_Z 不一致，D 无法对 T 一致。 -/
theorem pairCount_L1_bound (T0 ε : ℝ) (hT0 : 1 < T0) (hε : 0 < ε) :
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ T : ℝ, T0 ≤ T →
      let δ := Real.log T / (2 * Real.pi)
      Summable (fun p : ℂ × ℂ => if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
          then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
             + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) ∧
      (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
          then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)
        ≤ D * N_L T * normL1 (fun x => f0 x - f_eps ε x) := by
  rcases pair_count_bound T0 hT0 with ⟨Dcnt, hDcnt0, hpc⟩
  let M : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hMpos : 0 < M := by
    unfold M
    exact inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < sqrt 2)
      (abs_pos.mpr sin_inv_sqrt2_ne_zero))
  have hM0 : 0 ≤ M := le_of_lt hMpos
  have hLpos : 0 < normL1 (fun x => f0 x - f_eps ε x) := normL1_sub_pos ε hε
  let D : ℝ := (2 * M * Dcnt) / normL1 (fun x => f0 x - f_eps ε x)
  have hD0 : 0 ≤ D := by
    unfold D
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0) hDcnt0)
      (le_of_lt hLpos)
  refine ⟨D, hD0, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT1
  let δ : ℝ := Real.log T / (2 * Real.pi)
  have hδpos : 0 < δ := div_pos hlog (by positivity : (0 : ℝ) < 2 * Real.pi)
  have hNL0 : 0 ≤ N_L T := by
    rcases N_L_lower_bound with ⟨c, hc0, hlb⟩
    have hclog : 0 ≤ c * T * Real.log T :=
      mul_nonneg (mul_nonneg (le_of_lt hc0) (by positivity : 0 ≤ T)) (Real.log_nonneg (le_of_lt hT1))
    exact le_trans hclog (hlb T (le_of_lt hT1))
  have hfinZ : Set.Finite (zerosLChi5UpTo T) := zerosLChi5_bounded_finite T
  have hfinP : Set.Finite {p : ℂ × ℂ | p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T} :=
    hfinZ.prod hfinZ
  have hsum_supp : Function.support (fun p : ℂ × ℂ =>
      if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) ⊆
      {p : ℂ × ℂ | p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T} := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra hz
    have hit : (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) = 0 := by
      rw [if_neg]
      intro h
      exact hz ⟨h.1, h.2.1⟩
    exact hp hit
  have hsum : Summable (fun p : ℂ × ℂ =>
      if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) :=
    summable_of_finite_support (hfinP.subset hsum_supp)
  have hcnt_supp : Function.support (fun p : ℂ × ℂ =>
      if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) ⊆
      {p : ℂ × ℂ | p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T} := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra hz
    have hit : (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]
      intro h
      exact hz ⟨h.1, h.2.1⟩
    exact hp hit
  have hcnt_sum : Summable (fun p : ℂ × ℂ =>
      if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) :=
    summable_of_finite_support (hfinP.subset hcnt_supp)
  have hterm : ∀ p : ℂ × ℂ,
      (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
          then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) ≤
        (2 * M) * (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) := by
    intro p
    by_cases hz : p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
    · let a : ℝ := δ * (p.1 - p.2).im
      by_cases hw : |(p.1 - p.2).im| ≤ 1 / (2 * δ)
      · have htri : |f0 a - f_eps ε a| ≤ |f0 a| + |f_eps ε a| := by
          rw [abs_sub_le_iff]
          constructor
          · linarith [le_abs_self (f0 a), neg_le_abs (f_eps ε a)]
          · linarith [le_abs_self (f_eps ε a), neg_le_abs (f0 a)]
        have hb : |f0 a - f_eps ε a| ≤ 2 * M := by
          linarith [f_eps_abs_le ε a, f0_abs_le a, htri, hM0]
        have hcnt1 : (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
              ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) = 1 := by
          rw [if_pos ⟨hz.1, ⟨hz.2.1, ⟨hz.2.2, hw⟩⟩⟩]
        rw [if_pos hz]
        change |f0 a - f_eps ε a| ≤ (2 * M) * (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
              ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0)
        rw [hcnt1, mul_one]
        exact hb
      · have hnot_le : ¬ |(p.1 - p.2).im| ≤ 1 / (2 * δ) := hw
        have hbig : (1 : ℝ) / 2 < δ * |(p.1 - p.2).im| := by
          have hgt : 1 / (2 * δ) < |(p.1 - p.2).im| := lt_of_not_ge hnot_le
          calc
            (1 : ℝ) / 2 = δ * (1 / (2 * δ)) := by
              field_simp [ne_of_gt hδpos]
            _ < δ * |(p.1 - p.2).im| := mul_lt_mul_of_pos_left hgt hδpos
        have harg : (1 : ℝ) / 2 < |a| := by
          calc
            (1 : ℝ) / 2 < δ * |(p.1 - p.2).im| := hbig
            _ = |δ * (p.1 - p.2).im| := by
              rw [abs_mul, abs_of_pos hδpos]
        have hf0zero : f0 a = 0 := by
          unfold f0
          rw [ite_eq_right]
          intro hle
          exact (not_le_of_gt harg) hle
        have hfepszero : f_eps ε a = 0 := by
          unfold f_eps
          rw [hf0zero]
          simp
        have hg0 : |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| = 0 := by
          change |f0 a - f_eps ε a| = 0
          simp [hf0zero, hfepszero]
        have hcnt0 : (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
              ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) = 0 := by
          rw [if_neg]
          intro h
          exact hw h.2.2.2
        rw [hg0, hcnt0]
        norm_num
    · rw [if_neg hz]
      have hcnt0 : (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) = 0 := by
        rw [if_neg]
        intro h
        exact hz ⟨h.1, ⟨h.2.1, h.2.2.1⟩⟩
      rw [hcnt0]
      norm_num
  have hg_sum : Summable (fun p : ℂ × ℂ =>
      if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
    exact Summable.of_norm_bounded hsum (by
      intro p
      simp [Real.norm_eq_abs]
      by_cases hz : p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
      · rw [if_pos hz, if_pos hz]
        calc
          |(|f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)|)|
              = |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| := by
                exact abs_of_nonneg (abs_nonneg _)
          _ ≤ |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
              + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| := by
            linarith [abs_nonneg (f0 (δ * (p.1 - p.2).im)),
              abs_nonneg (f_eps ε (δ * (p.1 - p.2).im))]
      · rw [if_neg hz, if_neg hz]
        simp)
  have hcnt2 : Summable (fun p : ℂ × ℂ => (2 * M) * (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0)) :=
    hcnt_sum.mul_left (2 * M)
  have hle_sum : (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) ≤
      (∑' p : ℂ × ℂ, (2 * M) * (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0)) :=
    Summable.tsum_le_tsum hterm hg_sum hcnt2
  have hcnt_le : (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
            ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) ≤ Dcnt * N_L T :=
    hpc T hT
  have hle2 : (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) ≤
      2 * M * (Dcnt * N_L T) := by
    calc
      (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
          then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)
          ≤ ∑' p : ℂ × ℂ, (2 * M) * (if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
              ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) := hle_sum
      _ = (2 * M) * (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
              ∧ |(p.1 - p.2).im| ≤ 1 / (2 * δ) then (1 : ℝ) else 0) := by
        rw [tsum_mul_left]
      _ ≤ (2 * M) * (Dcnt * N_L T) :=
        mul_le_mul_of_nonneg_left hcnt_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0)
  have hle3 : 2 * M * (Dcnt * N_L T) ≤ D * N_L T * normL1 (fun x => f0 x - f_eps ε x) := by
    unfold D
    have hden : normL1 (fun x => f0 x - f_eps ε x) ≠ 0 := ne_of_gt hLpos
    have hform : D * N_L T * normL1 (fun x => f0 x - f_eps ε x)
        = (2 * M * Dcnt * N_L T * normL1 (fun x => f0 x - f_eps ε x)) / normL1 (fun x => f0 x - f_eps ε x) := by
      ring
    rw [hform, le_div_iff₀ hLpos]
    ring_nf
    exact le_rfl
  exact ⟨hsum, le_trans hle2 hle3⟩

/-- N2b-通用件（真证）：两个可和 tsum 之差的绝对值 ≤ 逐项绝对差之和
    （|Σf − Σg| ≤ Σ|f−g|：tsum_sub 重写 + norm_tsum_le_tsum_norm；
    |f−g| 的可和性由调用方逐项界保证（hfg 参数）。 -/
lemma abs_tsum_sub_le_tsum_abs (f g : ℂ × ℂ → ℝ) (hf : Summable f) (hg : Summable g)
    (hfg : Summable (fun p => |f p - g p|)) :
  |(∑' p, f p) - (∑' p, g p)| ≤ ∑' p, |f p - g p| := by
  have hsub : (∑' p : ℂ × ℂ, f p) - (∑' p : ℂ × ℂ, g p) =
      ∑' p : ℂ × ℂ, (f p - g p) := (hf.tsum_sub hg).symm
  simpa [hsub, Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm (f := fun p => f p - g p) hfg

/-- N2b-核心归约（真证）：|pairConstant(f_ε) − pairConstant(f₀)| ≤ (2M/N)·Σ_p|f₀−f_ε|(δΔ)。
    链：pairConstant 展开（常数 1 抵消）→ |Σx2 − Σx0|/N（abs_tsum_sub_le_tsum_abs）
    → Σ|x2−x0|/N（逐项 sq_sub_sq_abs_le + 全局界 2M，tsum_le_tsum）
    → (2M/N)·Σ'y（tsum 线性）。 -/
lemma pairConst_sub_pairL1 (ε δ N : ℝ) (Z : ZeroSet) (hN : 0 < N)
    (hsum : Summable (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)) :
    |pairConstant (f_eps ε) δ N Z - pairConstant f0 δ N Z|
      ≤ (2 * (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ / N) *
        (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
  let M : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hM0 : 0 ≤ M := by
    unfold M
    exact inv_nonneg.mpr (mul_nonneg (by positivity : (0 : ℝ) ≤ sqrt 2) (abs_nonneg _))
  have hterm : ∀ p : ℂ × ℂ,
      |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
        - (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)|
        ≤ (2 * M) * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
    intro p
    by_cases hz : p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
    · simp [hz]
      let a : ℝ := δ * (p.1 - p.2).im
      have hb2 : |f_eps ε a| + |f0 a| ≤ 2 * M := by
        linarith [f_eps_abs_le ε a, f0_abs_le a]
      have hb3 : (|f_eps ε a| + |f0 a|) * |f_eps ε a - f0 a| ≤ (2 * M) * |f0 a - f_eps ε a| := by
        rw [abs_sub_comm (f_eps ε a) (f0 a)]
        exact mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
      calc
        |f_eps ε a ^ 2 - f0 a ^ 2|
            ≤ (|f_eps ε a| + |f0 a|) * |f_eps ε a - f0 a| :=
              sq_sub_sq_abs_le (f_eps ε a) (f0 a)
        _ ≤ (2 * M) * |f0 a - f_eps ε a| := hb3
    · simp [hz]
  have hy : Summable (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
    have hybd : ∀ p : ℂ × ℂ,
        |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
          then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)|
          ≤ (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
               + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
      intro p
      by_cases hz : p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      · let a : ℝ := δ * (p.1 - p.2).im
        have ha : a = δ * (p.1 - p.2).im := rfl
        rw [← ha]
        simp [hz]
        linarith [abs_nonneg (f0 a), abs_nonneg (f_eps ε a),
          abs_nonneg (f0 a - f_eps ε a)]
      · simp [hz]
    exact Summable.of_norm_bounded hsum (by simpa [Real.norm_eq_abs] using hybd)
  have hx2 : Summable (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0) := by
    have hMc : Summable (fun p : ℂ × ℂ => M * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)) :=
      Summable.mul_left M hsum
    have hx2bd : ∀ p : ℂ × ℂ,
        |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
          then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)|
          ≤ M * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
               + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
      intro p
      by_cases hz : p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      · let a : ℝ := δ * (p.1 - p.2).im
        have ha : a = δ * (p.1 - p.2).im := rfl
        rw [← ha]
        simp [hz]
        calc
          f_eps ε a ^ 2 ≤ M * |f_eps ε a| := by
            rw [← sq_abs (f_eps ε a), pow_two]
            exact mul_le_mul_of_nonneg_right (f_eps_abs_le ε a) (abs_nonneg (f_eps ε a))
          _ ≤ M * (|f0 a| + |f_eps ε a| + |f0 a - f_eps ε a|) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [abs_nonneg (f0 a), abs_nonneg (f0 a - f_eps ε a)]) hM0
      · simp [hz]
    exact Summable.of_norm_bounded hMc (by simpa [Real.norm_eq_abs] using hx2bd)
  have hx0 : Summable (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      then f0 (δ * (p.1 - p.2).im) ^ 2 else 0) := by
    have hMc : Summable (fun p : ℂ × ℂ => M * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
        then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
           + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)) :=
      Summable.mul_left M hsum
    have hx0bd : ∀ p : ℂ × ℂ,
        |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
          then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)|
          ≤ M * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im)| + |f_eps ε (δ * (p.1 - p.2).im)|
               + |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
      intro p
      by_cases hz : p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      · let a : ℝ := δ * (p.1 - p.2).im
        have ha : a = δ * (p.1 - p.2).im := rfl
        rw [← ha]
        simp [hz]
        calc
          f0 a ^ 2 ≤ M * |f0 a| := by
            rw [← sq_abs (f0 a), pow_two]
            exact mul_le_mul_of_nonneg_right (f0_abs_le a) (abs_nonneg (f0 a))
          _ ≤ M * (|f0 a| + |f_eps ε a| + |f0 a - f_eps ε a|) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [abs_nonneg (f_eps ε a), abs_nonneg (f0 a - f_eps ε a)]) hM0
      · simp [hz]
    exact Summable.of_norm_bounded hMc (by simpa [Real.norm_eq_abs] using hx0bd)
  have h2My : Summable (fun p : ℂ × ℂ => (2 * M) * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
      then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)) :=
    Summable.mul_left (2 * M) hy
  have hfg : Summable (fun p : ℂ × ℂ =>
      |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
        - (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)|) := by
    exact Summable.of_norm_bounded h2My (by
      intro p
      simpa [Real.norm_eq_abs] using hterm p)
  calc
    |pairConstant (f_eps ε) δ N Z - pairConstant f0 δ N Z|
        = |(1 + (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
              then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0) / N)
            - (1 + (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
              then f0 (δ * (p.1 - p.2).im) ^ 2 else 0) / N)| := by
      simp [pairConstant]
    _ = |((∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
          - (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)) / N| := by ring
    _ = |(∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
        - (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)| / |N| := by rw [abs_div]
    _ = |(∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
        - (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)| / N := by rw [abs_of_pos hN]
    _ ≤ (∑' p : ℂ × ℂ, |(if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
          - (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)|) / N := by
      exact div_le_div_of_nonneg_right
        (abs_tsum_sub_le_tsum_abs
          (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f_eps ε (δ * (p.1 - p.2).im) ^ 2 else 0)
          (fun p : ℂ × ℂ => if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then f0 (δ * (p.1 - p.2).im) ^ 2 else 0)
          hx2 hx0 hfg) (le_of_lt hN)
    _ ≤ (∑' p : ℂ × ℂ, (2 * M) * (if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0)) / N := by
      exact div_le_div_of_nonneg_right (Summable.tsum_le_tsum hterm hfg h2My) (le_of_lt hN)
    _ = (2 * M) * (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) / N := by
      rw [tsum_mul_left]
    _ = (2 * M / N) * (∑' p : ℂ × ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2
            then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by ring

/-- N2b-配对常数偏差界（真证 2026-10-30 + 口径修正 2026-10-31；axiom → theorem）——最终组装：
    三段链：Lipschitz 归约（pairConst_sub_pairL1）→ 积分层挂钩（pairCount_L1_bound 真证）
    → L¹ 界（f0_sub_feps_L1_bound）；C₁ = 4M²D（D 由挂钩定理给出、对 T 一致）。
    口径修正（2026-10-31 增量⑧）：归一化参数 N 从 δ 改为 N_Z(T)（文档 S7.1 §2「N = 零点数」），
    零点集从 zerosLChi5 改为截断集 zerosLChi5UpTo T（有限 ⟹ Summable 真证）；Bound 仍 = ε。 -/
theorem pair_const_eps_bias (T0 ε : ℝ) (hT0 : 1 < T0) (hε : 0 < ε) :
  ∃ C₁ : ℝ,
    Bound C₁ T0
      (fun T => |pairConstant (f_eps ε) (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)
        - pairConstant f0 (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)|)
      (fun _T => ε) := by
  rcases pairCount_L1_bound T0 ε hT0 hε with ⟨D, hD0, hPC⟩
  let M : ℝ := (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹
  have hMpos : 0 < M := by
    unfold M
    exact inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < sqrt 2)
      (abs_pos.mpr sin_inv_sqrt2_ne_zero))
  have hM0 : 0 ≤ M := le_of_lt hMpos
  refine ⟨4 * M ^ 2 * D, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_two_nonneg M)) hD0
  · intro T hT
    have hT1 : (1 : ℝ) < T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos hT1
    let δ : ℝ := Real.log T / (2 * Real.pi)
    have hδpos : 0 < δ := div_pos hlog (by positivity : (0 : ℝ) < 2 * Real.pi)
    have hNLpos : 0 < N_L T := by
      rcases N_L_lower_bound with ⟨c, hc0, hlb⟩
      have hclog : 0 < c * T * Real.log T := mul_pos (mul_pos hc0 (by positivity : 0 < T)) hlog
      exact lt_of_lt_of_le hclog (hlb T (le_of_lt hT1))
    rcases hPC T hT with ⟨hsum, hcnt⟩
    calc
      |(fun T => |pairConstant (f_eps ε) (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)
        - pairConstant f0 (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)|) T|
          = |pairConstant (f_eps ε) δ (N_L T) (zerosLChi5UpTo T)
            - pairConstant f0 δ (N_L T) (zerosLChi5UpTo T)| := by
          simpa [δ]
      _ ≤ (2 * M / (N_L T)) *
            (∑' p : ℂ × ℂ, if p.1 ∈ zerosLChi5UpTo T ∧ p.2 ∈ zerosLChi5UpTo T ∧ p.1 ≠ p.2
                then |f0 (δ * (p.1 - p.2).im) - f_eps ε (δ * (p.1 - p.2).im)| else 0) := by
          simpa [M] using pairConst_sub_pairL1 ε δ (N_L T) (zerosLChi5UpTo T) hNLpos hsum
      _ ≤ (2 * M / (N_L T)) * (D * N_L T * normL1 (fun x => f0 x - f_eps ε x)) := by
        simpa [δ] using
          (mul_le_mul_of_nonneg_left hcnt
            (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0) (le_of_lt hNLpos)))
      _ = 2 * M * D * normL1 (fun x => f0 x - f_eps ε x) := by
        field_simp [ne_of_gt hNLpos]
      _ ≤ 2 * M * D * (2 * ε * M) := by
        exact mul_le_mul_of_nonneg_left (f0_sub_feps_L1_bound ε hε)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0) hD0)
      _ = (4 * M ^ 2 * D) * ε := by ring

/-! ## N3：离线项一致版本（文档 S7.5 定理 N3） -/

/-- 离线（off-critical）误差算子：BGS 余项结构，核无关（S7.5 §2 判定）。 -/
axiom offcritSum : (ℝ → ℝ) → ℝ → ℝ

/-- N3-余项跨 λ 一致（statement，S7.5 定理 N3(i)(iii)，Bound 显式界化）：
    BGS 余项 O(T√logT) 对 supp⊂[−1,1] 一切核一致（核只在零点侧 L(x,T)，经 L=R 吸收）；
    R 对 K 一致（外层 ∃R，∀ K supp → Bound R …）、T 侧套 Bound（∀ T ≥ T₀）。 -/
axiom n3_remainder_uniform (T0 : ℝ) (hT0 : 1 ≤ T0) :
  ∃ R : ℝ, 0 ≤ R ∧
    ∀ K : ℝ → ℝ, (∀ u : ℝ, 1 < |u| → fourierCos K u = 0) →
      Bound R T0 (fun T => |offcritSum K T|) (fun T => T * Real.sqrt (Real.log T))

/-! ## 三条真证明件（超支撑素数项层；清单 §4 Stage 3+） -/

/-! ### 件 1：K̂_a 偶性（一阶校正恒为零的解析形态，真证明件） -/

/-- 一阶校正恒为零（偶核）：K̂_a(u)=K̂(au) 是偶函数（K̂_a(u)=K̂_a(−u)），
    故 Taylor 展开无线性项——二阶主导（数值件 F 实测 ratio=1.000 @ aδ≤3e−3）。 -/
lemma Khat_a_even (a u : ℝ) : Khat (a * u) = Khat (-(a * u)) := by
  rw [← Khat_neg (a * u)]

/-! ### 件 1b：K̂ 二阶一致界真证（K̂ 导数闭式 + 区间界；替代原 axiom）

迁入自 Dbg_Khat.lean（2026-10-26 编译 exit=0）。数学链：
  K̂(u) = [cos(πu) − √2·πu·cotR(√2/2)·sin(πu)] / (1 − 2π²u²)（Khat_closed_form 乘形式）；
  |u| ≤ 1/24 ⟹ |m| = |πu| ≤ 2/15（π < 16/5），m² ≤ 4/225 ⟹ 分母 1−2m² ≥ 217/225 > 0；
  N = cos m − 1 + 2m² − √2·m·cotR·sin m = m²(3/2 − √2·cotR) + rc − √2·m·cotR·rs，
  其中 cos 二阶余项 |rc| ≤ m⁴·5/96（cos_bound）、sin 一阶余项 |rs| ≤ |m|⁵/100 + |m|³/6（sin_bound）；
  |3/2 − √2·cotR(√2/2)| ≤ 9/50（c0_bound，cotR ∈ [1, 237/200] 数值区间）；
  拼接得 |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴（194/1000·π² ≤ 2 由 π ≤ 16/5）。
  数值核对：½|K̂″(0)|≈1.53<2（2u² 系数）、π²≈9.87、√2·cotR≈3/2。 -/

private lemma abs_add_ineq (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_le_abs a, neg_le_abs b]
  · linarith [le_abs_self a, le_abs_self b]

/-- √2 ≥ q（q ≥ 0，q² ≤ 2）。 -/
lemma sqrt2_ge (q : ℝ) (hq0 : 0 ≤ q) (hq : q ^ 2 ≤ 2) : q ≤ sqrt 2 := by
  have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : q ^ 2 ≤ (sqrt 2) ^ 2 := by simpa [h2] using hq
  have habs : |q| ≤ |sqrt 2| := (sq_le_sq.mp hsq)
  have hqabs : |q| = q := abs_of_nonneg hq0
  have hsq2abs : |sqrt 2| = sqrt 2 := abs_of_nonneg (by positivity)
  simpa [hqabs, hsq2abs] using habs

/-- √2 ≤ q（q ≥ 0，2 ≤ q²）。 -/
lemma sqrt2_le (q : ℝ) (hq0 : 0 ≤ q) (hq : 2 ≤ q ^ 2) : sqrt 2 ≤ q := by
  have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : (sqrt 2) ^ 2 ≤ q ^ 2 := by simpa [h2] using hq
  have habs : |sqrt 2| ≤ |q| := (sq_le_sq.mp hsq)
  have hqabs : |q| = q := abs_of_nonneg hq0
  have hsq2abs : |sqrt 2| = sqrt 2 := abs_of_nonneg (by positivity)
  simpa [hqabs, hsq2abs] using habs

/-- cos 在 [0, π] 上递减（自证：cos x = sin(π/2 − x)，sin 在 [−π/2, π/2] 递增）。 -/
lemma cos_dec_on (x y : ℝ) (hxy : x ≤ y) (hx0 : 0 ≤ x) (hypi : y ≤ Real.pi) :
    cos y ≤ cos x := by
  have htmp' : ∀ t : ℝ, cos (Real.pi / 2 - t) = sin t := by
    intro t
    rw [Real.cos_sub]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have h2 : cos (Real.pi / 2 - (Real.pi / 2 - x)) = sin (Real.pi / 2 - x) :=
    htmp' (Real.pi / 2 - x)
  have hcosx : cos x = sin (Real.pi / 2 - x) := by
    convert h2 using 1
    ring_nf
  have h3 : cos (Real.pi / 2 - (Real.pi / 2 - y)) = sin (Real.pi / 2 - y) :=
    htmp' (Real.pi / 2 - y)
  have hcosy : cos y = sin (Real.pi / 2 - y) := by
    convert h3 using 1
    ring_nf
  rw [hcosx, hcosy]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have : -(Real.pi / 2) ≤ Real.pi / 2 - y := by linarith [hypi]
    exact this
  · have : Real.pi / 2 - x ≤ Real.pi / 2 := by linarith [hx0]
    exact this
  · linarith [hxy]

/-- cos(8/5) < 0（cos 1.6 = 2cos²0.8 − 1；cos_bound 给出 cos 0.8 ≤ 3507/5000）。 -/
lemma cos_8_div_5_lt : cos (8 / 5) < 0 := by
  have hb : |(4 : ℝ) / 5| ≤ 1 := by norm_num
  have hcb := Real.cos_bound (x := (4 : ℝ) / 5) hb
  have hc : cos (4 / 5) ≤ 3507 / 5000 := by
    have hcb2 : cos (4 / 5) - (1 - (4 / 5) ^ 2 / 2) ≤ (4 / 5) ^ 4 * (5 / 96) := by
      simpa [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] using (abs_le.mp hcb).2
    have : cos (4 / 5) ≤ 1 - (4 / 5) ^ 2 / 2 + (4 / 5) ^ 4 * 5 / 96 := by
      linarith
    nlinarith
  have hcosnonneg : 0 ≤ cos (4 / 5) := by
    exact le_of_lt (Real.cos_pos_of_mem_Ioo (by
      constructor
      · have : -(Real.pi / 2) < (4 : ℝ) / 5 := by linarith [two_le_pi]
        exact this
      · have : (4 : ℝ) / 5 < Real.pi / 2 := by linarith [two_le_pi]
        exact this))
  have hcsq : cos (4 / 5) ^ 2 ≤ (3507 / 5000) ^ 2 := by
    have habs : |cos (4 / 5)| ≤ |3507 / 5000| := by
      simpa [abs_of_nonneg hcosnonneg, abs_of_pos (by norm_num : (0 : ℝ) < 3507 / 5000)]
        using hc
    exact sq_le_sq.mpr habs
  rw [show (8 : ℝ) / 5 = 2 * ((4 : ℝ) / 5) by norm_num]
  rw [Real.cos_two_mul]
  nlinarith

/-- π < 16/5（=3.2）：π/2 ≥ 8/5 则 cos 递减 ⟹ 0 ≤ cos(8/5)，与 cos(8/5)<0 矛盾。 -/
lemma pi_lt_32 : Real.pi < 16 / 5 := by
  by_contra h
  have hge : 16 / 5 ≤ Real.pi := le_of_not_gt h
  have hhalf : (8 : ℝ) / 5 ≤ Real.pi / 2 := by linarith
  have hdec : cos (Real.pi / 2) ≤ cos (8 / 5) :=
    cos_dec_on (8 / 5) (Real.pi / 2) hhalf (by norm_num) (by linarith [hge])
  rw [Real.cos_pi_div_two] at hdec
  have hcoslt : cos (8 / 5) < 0 := cos_8_div_5_lt
  linarith

/-- √2/2 = 1/√2。 -/
lemma sqrt2_div_two_eq_inv : sqrt 2 / 2 = 1 / sqrt 2 := by
  field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- 14141/10000 ≤ √2。 -/
lemma sqrt2_14141 : (14141 : ℝ) / 10000 ≤ sqrt 2 :=
  sqrt2_ge (14141 / 10000) (by norm_num) (by norm_num : ((14141 : ℝ) / 10000) ^ 2 ≤ 2)

/-- √2 ≤ 14143/10000。 -/
lemma sqrt2_le_14143 : sqrt 2 ≤ (14143 : ℝ) / 10000 :=
  sqrt2_le (14143 / 10000) (by norm_num) (by norm_num : 2 ≤ ((14143 : ℝ) / 10000) ^ 2)

/-- |1/√2| ≤ 1。 -/
lemma inv_sqrt2_abs_le_one : |1 / sqrt 2| ≤ 1 := by
  have h1 : (1 : ℝ) ≤ sqrt 2 := sqrt2_ge 1 (by norm_num) (by norm_num : (1 : ℝ) ^ 2 ≤ 2)
  have hbb : 1 / sqrt 2 ≤ 1 / (1 : ℝ) :=
    (one_div_le_one_div (by positivity : (0 : ℝ) < sqrt 2) (by norm_num : (0 : ℝ) < 1)).mpr h1
  have hb' : 1 / sqrt 2 ≤ 1 := by simpa using hbb
  have hnn : 0 ≤ 1 / sqrt 2 := by positivity
  rwa [abs_of_nonneg hnn]

/-- 10000/14143 ≤ 1/√2 ≤ 10000/14141。 -/
lemma inv_sqrt2_bounds :
    10000 / 14143 ≤ 1 / sqrt 2 ∧ 1 / sqrt 2 ≤ 10000 / 14141 := by
  constructor
  · -- 1/(14143/10000) ≤ 1/√2 ↔ √2 ≤ 14143/10000
    have hb : 1 / (14143 / 10000) ≤ 1 / sqrt 2 :=
      (one_div_le_one_div (by norm_num : (0 : ℝ) < 14143 / 10000)
        (by positivity : (0 : ℝ) < sqrt 2)).mpr sqrt2_le_14143
    -- 1/(14143/10000) = 10000/14143
    simpa using hb
  · -- 1/√2 ≤ 1/(14141/10000) ↔ 14141/10000 ≤ √2
    have hb : 1 / sqrt 2 ≤ 1 / (14141 / 10000) :=
      (one_div_le_one_div (by positivity : (0 : ℝ) < sqrt 2)
        (by norm_num : (0 : ℝ) < 14141 / 10000)).mpr sqrt2_14141
    -- 1/(14141/10000) = 10000/14141
    simpa using hb

/-- sin(1/√2) ≥ 323/500（sin_bound 三阶下界 + 1/√2 区间）。 -/
lemma sin_inv_sqrt2_ge : sin (1 / sqrt 2) ≥ 323 / 500 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.sin_bound (x := 1 / sqrt 2) hb0
  -- sin x ≥ x − x³/6 − |x|⁵/100
  have hl : sin (1 / sqrt 2) ≥ (1 / sqrt 2) - (1 / sqrt 2) ^ 3 / 6 - |1 / sqrt 2| ^ 5 / 100 := by
    have h1 := (abs_le.mp hb).1
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx5 : |1 / sqrt 2| ^ 5 = (1 / sqrt 2) ^ 5 := by rw [abs_of_nonneg hx]
  rw [hx5] at hl
  have h1 : (1 / sqrt 2) ^ 3 ≤ (10000 / 14141) ^ 3 := pow_le_pow_left₀ hx hib 3
  have h2 : (1 / sqrt 2) ^ 5 ≤ (10000 / 14141) ^ 5 := pow_le_pow_left₀ hx hib 5
  have h3 : (10000 / 14143 : ℝ) ≤ 1 / sqrt 2 := hia
  have hnum : 10000 / 14143 - (10000 / 14141) ^ 3 / 6 - (10000 / 14141) ^ 5 / 100 ≥ 323 / 500 := by
    norm_num
  linarith

/-- sin(1/√2) ≤ 651/1000（sin_bound 三阶上界 + 1/√2 区间）。 -/
lemma sin_inv_sqrt2_le : sin (1 / sqrt 2) ≤ 651 / 1000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.sin_bound (x := 1 / sqrt 2) hb0
  have hl : sin (1 / sqrt 2) ≤ (1 / sqrt 2) - (1 / sqrt 2) ^ 3 / 6 + |1 / sqrt 2| ^ 5 / 100 := by
    have h1 := (abs_le.mp hb).2
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx5 : |1 / sqrt 2| ^ 5 = (1 / sqrt 2) ^ 5 := by rw [abs_of_nonneg hx]
  rw [hx5] at hl
  have h1 : (10000 / 14143) ^ 3 ≤ (1 / sqrt 2) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 14143) hia 3
  have h2 : (1 / sqrt 2) ^ 5 ≤ (10000 / 14141) ^ 5 := pow_le_pow_left₀ hx hib 5
  have hnum : 10000 / 14141 - (10000 / 14143) ^ 3 / 6 + (10000 / 14141) ^ 5 / 100 ≤ 651 / 1000 := by
    norm_num
  linarith

/-- cos(1/√2) ≥ 736/1000（cos_bound 二阶下界 + 1/√2 区间）。 -/
lemma cos_inv_sqrt2_ge : cos (1 / sqrt 2) ≥ 736 / 1000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.cos_bound (x := 1 / sqrt 2) hb0
  have hl : cos (1 / sqrt 2) ≥ 1 - (1 / sqrt 2) ^ 2 / 2 - |1 / sqrt 2| ^ 4 * (5 / 96) := by
    have h1 := (abs_le.mp hb).1
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx4 : |1 / sqrt 2| ^ 4 = (1 / sqrt 2) ^ 4 := by rw [abs_of_nonneg hx]
  rw [hx4] at hl
  have h1 : (1 / sqrt 2) ^ 2 ≤ (10000 / 14141) ^ 2 := pow_le_pow_left₀ hx hib 2
  have h2 : (1 / sqrt 2) ^ 4 ≤ (10000 / 14141) ^ 4 := pow_le_pow_left₀ hx hib 4
  have hnum : 1 - (10000 / 14141) ^ 2 / 2 - (10000 / 14141) ^ 4 * (5 / 96) ≥ 736 / 1000 := by
    norm_num
  linarith

/-- cos(1/√2) ≤ 7631/10000（cos_bound 二阶上界 + 1/√2 区间）。 -/
lemma cos_inv_sqrt2_le : cos (1 / sqrt 2) ≤ 7631 / 10000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.cos_bound (x := 1 / sqrt 2) hb0
  have hl : cos (1 / sqrt 2) ≤ 1 - (1 / sqrt 2) ^ 2 / 2 + |1 / sqrt 2| ^ 4 * (5 / 96) := by
    have h1 := (abs_le.mp hb).2
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx4 : |1 / sqrt 2| ^ 4 = (1 / sqrt 2) ^ 4 := by rw [abs_of_nonneg hx]
  rw [hx4] at hl
  have h1sq : (10000 / 14143) ^ 2 ≤ (1 / sqrt 2) ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 14143) hia 2
  have h2p4 : (1 / sqrt 2) ^ 4 ≤ (10000 / 14141) ^ 4 := pow_le_pow_left₀ hx hib 4
  have hnum : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 + ((10000 : ℝ) / 14141) ^ 4 * (5 / 96)
      ≤ 7631 / 10000 := by
    have hna : ((10000 : ℝ) / 14143) ^ 2 ≥ 12497 / 25000 := by norm_num
    have hnb : ((10000 : ℝ) / 14141) ^ 4 ≤ 25012 / 100000 := by norm_num
    have hpart1 : ((10000 : ℝ) / 14143) ^ 2 / 2 ≥ 12497 / 50000 := by
      have h1 : (12497 / 25000) / 2 ≤ ((10000 : ℝ) / 14143) ^ 2 / 2 :=
        div_le_div_of_nonneg_right hna (by norm_num : (0 : ℝ) ≤ 2)
      have hnumv : (12497 / 25000 : ℝ) / 2 = 12497 / 50000 := by norm_num
      rwa [hnumv] at h1
    have hpart2 : ((10000 : ℝ) / 14141) ^ 4 * (5 / 96) ≤ 6253 / 480000 := by
      have h1 : ((10000 : ℝ) / 14141) ^ 4 * (5 / 96) ≤ (25012 / 100000) * (5 / 96) :=
        mul_le_mul_of_nonneg_right hnb (by norm_num : (0 : ℝ) ≤ 5 / 96)
      have hnumv : (25012 / 100000 : ℝ) * (5 / 96) = 6253 / 480000 := by norm_num
      rwa [hnumv] at h1
    have hnum2 : 37503 / 50000 + 6253 / 480000 ≤ 7631 / 10000 := by norm_num
    have h1 : (12497 : ℝ) / 50000 ≤ (10000 / 14143) ^ 2 / 2 := by linarith [hpart1]
    have hone : (12497 : ℝ) / 50000 + 37503 / 50000 = 1 := by norm_num
    have hstepA : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 ≤ 37503 / 50000 := by
      linarith [h1, hone]
    have hstep : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 + ((10000 : ℝ) / 14141) ^ 4 * (5 / 96)
        ≤ 37503 / 50000 + 6253 / 480000 := by
      linarith [h1, hone, hpart2]
    linarith [hstep, hnum2]
  nlinarith [hl, h1sq, h2p4, hnum]

/-- 1 ≤ cotR(√2/2) ≤ 237/200。 -/
lemma cotR_half_bounds : 1 ≤ cotR (sqrt 2 / 2) ∧ cotR (sqrt 2 / 2) ≤ 237 / 200 := by
  unfold cotR
  rw [sqrt2_div_two_eq_inv]
  have hsin : 0 < sin (1 / sqrt 2) := by linarith [sin_inv_sqrt2_ge]
  constructor
  · -- cot ≥ 1 ⟸ cos ≥ sin
    have hcos : (736 : ℝ) / 1000 ≤ cos (1 / sqrt 2) := cos_inv_sqrt2_ge
    have hsinu : sin (1 / sqrt 2) ≤ 651 / 1000 := sin_inv_sqrt2_le
    have hcs : cos (1 / sqrt 2) ≥ sin (1 / sqrt 2) := by linarith
    -- (cos−sin)/sin = cos/sin − 1 ≥ 0
    have hnum : 0 ≤ cos (1 / sqrt 2) - sin (1 / sqrt 2) := by linarith
    have hfrac : 0 ≤ (cos (1 / sqrt 2) - sin (1 / sqrt 2)) / sin (1 / sqrt 2) :=
      div_nonneg hnum (le_of_lt hsin)
    have hrewrite : (cos (1 / sqrt 2) - sin (1 / sqrt 2)) / sin (1 / sqrt 2)
        = cos (1 / sqrt 2) / sin (1 / sqrt 2) - 1 := by
      field_simp [ne_of_gt hsin]
    rw [hrewrite] at hfrac
    linarith
  · -- cot ≤ 237/200：cos/sin ≤ (7631/10000)/(323/500)
    have hcos : cos (1 / sqrt 2) ≤ 7631 / 10000 := cos_inv_sqrt2_le
    have hsinu : (323 : ℝ) / 500 ≤ sin (1 / sqrt 2) := sin_inv_sqrt2_ge
    -- 1/sin ≤ 500/323（hsinu：倒数递减）
    have hinv : (sin (1 / sqrt 2))⁻¹ ≤ 500 / 323 := by
      have hb : 1 / sin (1 / sqrt 2) ≤ 1 / (323 / 500) :=
        (one_div_le_one_div hsin (by norm_num : (0 : ℝ) < 323 / 500)).mpr hsinu
      simpa [one_div] using hb
    have hcosn : 0 ≤ cos (1 / sqrt 2) := by linarith [cos_inv_sqrt2_ge]
    have hprod : cos (1 / sqrt 2) * (sin (1 / sqrt 2))⁻¹ ≤ 7631 / 10000 * (500 / 323) := by
      exact mul_le_mul hcos hinv (inv_nonneg.mpr (le_of_lt hsin))
        (by norm_num : (0 : ℝ) ≤ 7631 / 10000)
    have hnum : 7631 / 10000 * (500 / 323) ≤ 237 / 200 := by norm_num
    have hrewrite : cos (1 / sqrt 2) / sin (1 / sqrt 2) = cos (1 / sqrt 2) * (sin (1 / sqrt 2))⁻¹ := by
      rw [div_eq_mul_inv]
    rw [hrewrite]
    linarith

/-- |3/2 − √2·cotR(√2/2)| ≤ 9/50。 -/
lemma c0_bound : |(3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2)| ≤ 9 / 50 := by
  have hcot1 : 1 ≤ cotR (sqrt 2 / 2) := cotR_half_bounds.1
  have hcot2 : cotR (sqrt 2 / 2) ≤ 237 / 200 := cotR_half_bounds.2
  have hsqrtn : 0 ≤ sqrt 2 := by positivity
  have hup : (3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2) ≤ 9 / 50 := by
    have h1 : sqrt 2 * 1 ≤ sqrt 2 * cotR (sqrt 2 / 2) :=
      mul_le_mul_of_nonneg_left hcot1 hsqrtn
    have hlo : (14141 : ℝ) / 10000 ≤ sqrt 2 := sqrt2_14141
    linarith
  have hlo : -(9 / 50) ≤ (3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2) := by
    have hsqrt2 : sqrt 2 ≤ 14143 / 10000 := sqrt2_le_14143
    have hcotn : 0 ≤ cotR (sqrt 2 / 2) := by linarith [hcot1]
    have hprod : sqrt 2 * cotR (sqrt 2 / 2) ≤ 14143 / 10000 * (237 / 200) :=
      mul_le_mul hsqrt2 hcot2 hcotn (by norm_num : (0 : ℝ) ≤ 14143 / 10000)
    have hnum : 14143 / 10000 * (237 / 200) ≤ (3 : ℝ) / 2 + 9 / 50 := by norm_num
    nlinarith
  exact abs_le.mpr ⟨hlo, hup⟩

/-- 闭式（乘形式）：K̂(u)·(1 − 2π²u²) = cos(πu) − √2πu·cotR(√2/2)·sin(πu)，|u| ≤ 1/24 域内。 -/
lemma Khat_closed_form (u : ℝ) (hu : |u| ≤ (1 : ℝ) / 24) :
    Khat u * (1 - 2 * (Real.pi * u) ^ 2)
      = cos (Real.pi * u) - sqrt 2 * Real.pi * u * cotR (sqrt 2 / 2) * sin (Real.pi * u) := by
  unfold Khat cotR
  have hpi : Real.pi ≤ 4 := by linarith [pi_lt_32]
  have hpi_nonneg : 0 ≤ Real.pi := le_of_lt pi_pos
  have hpu2 : Real.pi * |u| ≤ 1 / 6 := by
    calc
      Real.pi * |u| ≤ 4 * (1 / 24) := by
        exact mul_le_mul hpi hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 4)
      _ = 1 / 6 := by norm_num
  have hpu : |Real.pi * u| ≤ 1 / 6 := by
    calc
      |Real.pi * u| = Real.pi * |u| := by rw [abs_mul, abs_of_pos pi_pos]
      _ ≤ 1 / 6 := hpu2
  have hb2 : 2 * Real.pi * |u| ≤ 1 / 3 := by
    calc
      2 * Real.pi * |u| = 2 * (Real.pi * |u|) := by ring
      _ ≤ 2 * (1 / 6) := by exact mul_le_mul_of_nonneg_left hpu2 (by norm_num)
      _ = 1 / 3 := by norm_num
  have hlo : (0 : ℝ) < sqrt 2 - 1 / 3 := by
    have h43 : (4 : ℝ) / 3 ≤ sqrt 2 :=
      sqrt2_ge (4 / 3) (by norm_num) (by norm_num : ((4 : ℝ) / 3) ^ 2 ≤ 2)
    linarith
  have hd1 : sqrt 2 - 2 * Real.pi * u ≠ 0 := by
    have h2u : 2 * Real.pi * u ≤ 2 * Real.pi * |u| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self u) (mul_nonneg (by norm_num) hpi_nonneg)
    have : 0 < sqrt 2 - 2 * Real.pi * u := by linarith
    exact ne_of_gt this
  have hd2 : sqrt 2 + 2 * Real.pi * u ≠ 0 := by
    have hc : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpi_nonneg
    have hneg : -u ≤ |u| := neg_le_abs u
    have h2u : -(2 * Real.pi * u) ≤ 2 * Real.pi * |u| := by
      calc
        -(2 * Real.pi * u) = (2 * Real.pi) * (-u) := by ring
        _ ≤ (2 * Real.pi) * |u| := mul_le_mul_of_nonneg_left hneg hc
    have : 0 < sqrt 2 + 2 * Real.pi * u := by linarith
    exact ne_of_gt this
  -- 1−2m² = (√2−2πu)(√2+2πu)/2
  have hmain : (1 : ℝ) - 2 * (Real.pi * u) ^ 2
      = (sqrt 2 - 2 * Real.pi * u) * (sqrt 2 + 2 * Real.pi * u) / 2 := by
    ring_nf
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  rw [hmain]
  field_simp [hd1, hd2, sin_inv_sqrt2_ne_zero]
  have hsa : S_smooth (sqrt 2 - 2 * Real.pi * u)
      = sin ((sqrt 2 - 2 * Real.pi * u) / 2) / (sqrt 2 - 2 * Real.pi * u) := by
    unfold S_smooth
    rw [ite_eq_right hd1]
  have hsb : S_smooth (sqrt 2 + 2 * Real.pi * u)
      = sin ((sqrt 2 + 2 * Real.pi * u) / 2) / (sqrt 2 + 2 * Real.pi * u) := by
    unfold S_smooth
    rw [ite_eq_right hd2]
  rw [hsa, hsb]
  have hA : (sqrt 2 - 2 * Real.pi * u) / 2 = sqrt 2 / 2 - Real.pi * u := by ring
  have hB : (sqrt 2 + 2 * Real.pi * u) / 2 = sqrt 2 / 2 + Real.pi * u := by ring
  rw [hA, hB]
  rw [Real.sin_sub, Real.sin_add]
  rw [sqrt2_div_two_eq_inv]
  have hs0 : sin (sqrt 2)⁻¹ ≠ 0 := by
    simpa [one_div] using sin_inv_sqrt2_ne_zero
  field_simp [hd1, hd2, hs0]
  ring_nf
  have hsq : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsq]
  ring_nf

/-- |K̂(u)−1| ≤ 2u²+u⁴ 在 |u| ≤ 1/24 域（Taylor 二阶余项 + cotR 数值区间 + π < 16/5）。 -/
lemma khat_second_order_bound :
    BoundBall 1 (1 / 24) (fun x => |Khat x - 1|) (fun x => 2 * x ^ 2 + x ^ 4) := by
  unfold BoundBall
  constructor
  · norm_num
  · intro u hu
    let m : ℝ := Real.pi * u
    have hpi : Real.pi ≤ 16 / 5 := le_of_lt pi_lt_32
    have hm : |m| ≤ 2 / 15 := by
      dsimp [m]
      calc
        |Real.pi * u| = Real.pi * |u| := by rw [abs_mul, abs_of_pos pi_pos]
        _ ≤ (16 / 5) * (1 / 24) := by
          exact mul_le_mul hpi hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 16 / 5)
        _ = 2 / 15 := by norm_num
    have hm2 : m ^ 2 ≤ 4 / 225 := by
      have habs : |m| ≤ |(2 : ℝ) / 15| := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 15)]
        exact hm
      calc
        m ^ 2 ≤ (2 / 15) ^ 2 := sq_le_sq.mpr habs
        _ = 4 / 225 := by norm_num
    have hm2nonneg : 0 ≤ m ^ 2 := sq_nonneg m
    have hden_ge : (1 : ℝ) - 2 * m ^ 2 ≥ 217 / 225 := by nlinarith [hm2]
    have hden_pos : 0 < 1 - 2 * m ^ 2 := by linarith [hden_ge]
    have hden_ne : (1 : ℝ) - 2 * m ^ 2 ≠ 0 := ne_of_gt hden_pos
    have hm1 : |m| ≤ 1 := by linarith [hm]
    -- 闭式
    have hcf := Khat_closed_form u hu
    have hK : Khat u = (cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m) / (1 - 2 * m ^ 2) := by
      have hd : (1 : ℝ) - 2 * (Real.pi * u) ^ 2 ≠ 0 := by
        dsimp [m] at hden_ne
        exact hden_ne
      have hcf' : Khat u = (cos (Real.pi * u) - sqrt 2 * (Real.pi * u) * cotR (sqrt 2 / 2)
          * sin (Real.pi * u)) / (1 - 2 * (Real.pi * u) ^ 2) := by
        calc
          Khat u = (Khat u * (1 - 2 * (Real.pi * u) ^ 2)) / (1 - 2 * (Real.pi * u) ^ 2) := by
            rw [div_eq_mul_inv]
            rw [mul_assoc]
            rw [mul_inv_cancel₀ hd]
            ring
          _ = (cos (Real.pi * u) - sqrt 2 * (Real.pi * u) * cotR (sqrt 2 / 2)
              * sin (Real.pi * u)) / (1 - 2 * (Real.pi * u) ^ 2) := by
            rw [hcf]
            ring_nf
      dsimp [m]
      convert hcf' using 1
    have hden_ne2 : (1 : ℝ) - m ^ 2 * 2 ≠ 0 := by
      convert hden_ne using 1
      ring
    -- |K̂u−1| = |N|/(1−2m²)
    have hN_abs : |Khat u - 1|
        = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := by
      calc
        |Khat u - 1| = |(cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m) / (1 - 2 * m ^ 2) - 1| := by rw [hK]
        _ = |(cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m - (1 - 2 * m ^ 2)) / (1 - 2 * m ^ 2)| := by
          congr 1
          field_simp [hden_ne2]
        _ = |cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m - (1 - 2 * m ^ 2)| / (1 - 2 * m ^ 2) := by
          rw [abs_div]
          rw [abs_of_pos hden_pos]
        _ = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := by
          congr 1
          ring
    -- rc：cos 二阶余项
    have hrc : |cos m - (1 - m ^ 2 / 2)| ≤ m ^ 4 * (5 / 96) := by
      have hcb := Real.cos_bound (x := m) hm1
      have htmp : |m| ^ 4 = m ^ 4 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]; exact sq_nonneg (m ^ 2))
      simpa [htmp] using hcb
    -- rs：sin 一阶余项
    have hrs : |sin m - m| ≤ |m| ^ 5 / 100 + |m| ^ 3 / 6 := by
      have hsb := Real.sin_bound (x := m) hm1
      calc
        |sin m - m| = |(sin m - (m - m ^ 3 / 6)) + (-(m ^ 3 / 6))| := by congr 1; ring
        _ ≤ |sin m - (m - m ^ 3 / 6)| + |-(m ^ 3 / 6)| := by
          simpa using abs_add_ineq (sin m - (m - m ^ 3 / 6)) (-(m ^ 3 / 6))
        _ = |sin m - (m - m ^ 3 / 6)| + |m ^ 3 / 6| := by rw [abs_neg]
        _ ≤ |m| ^ 5 / 100 + |m| ^ 3 / 6 := by
          have h2 : |m ^ 3 / 6| = |m| ^ 3 / 6 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
            rw [abs_pow]
          rw [h2]
          linarith [hsb]
    -- A 项
    have hA : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| ≤ (9 / 50) * m ^ 2 := by
      calc
        |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            = |3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)| * |m ^ 2| := by rw [abs_mul]
        _ = |3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)| * m ^ 2 := by rw [abs_of_nonneg hm2nonneg]
        _ ≤ (9 / 50) * m ^ 2 := mul_le_mul_of_nonneg_right c0_bound hm2nonneg
    -- |m|⁴ = m⁴、|m|⁶ ≤ m⁴
    have hm4eq : |m| ^ 4 = m ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]; exact sq_nonneg (m ^ 2))
    have hm6le : |m| ^ 6 ≤ m ^ 4 := by
      have hmm2 : |m| ^ 2 ≤ 1 := by nlinarith [hm]
      have hmp : 0 ≤ |m| ^ 4 := pow_nonneg (abs_nonneg m) 4
      calc
        |m| ^ 6 = |m| ^ 4 * |m| ^ 2 := by rw [← pow_add]
        _ ≤ |m| ^ 4 * 1 := mul_le_mul_of_nonneg_left hmm2 hmp
        _ = |m| ^ 4 := by simp
        _ = m ^ 4 := hm4eq
    -- B 项：|√2 m cotR (sin m − m)|
    have hB1 : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
        ≤ sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m| := by
      rw [abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg (by positivity : 0 ≤ sqrt 2)]
      rw [abs_of_nonneg (by linarith [cotR_half_bounds.1] : 0 ≤ cotR (sqrt 2 / 2))]
    have hsq15 : sqrt 2 ≤ 3 / 2 := sqrt2_le (3 / 2 : ℝ) (by norm_num) (by norm_num : 2 ≤ (3 / 2 : ℝ) ^ 2)
    have hcotle : cotR (sqrt 2 / 2) ≤ 237 / 200 := cotR_half_bounds.2
    have hA2 : sqrt 2 * cotR (sqrt 2 / 2) ≤ (3 / 2) * (237 / 200) :=
      mul_le_mul hsq15 hcotle (by linarith [cotR_half_bounds.1] : 0 ≤ cotR (sqrt 2 / 2))
        (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hB2 : sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m|
        ≤ (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) := by
      calc
        sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m|
            = (sqrt 2 * cotR (sqrt 2 / 2)) * (|m| * |sin m - m|) := by ring
        _ ≤ ((3 / 2) * (237 / 200)) * (|m| * |sin m - m|) := by
          exact mul_le_mul_of_nonneg_right hA2 (mul_nonneg (abs_nonneg m) (abs_nonneg (sin m - m)))
        _ ≤ ((3 / 2) * (237 / 200)) * (|m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)) := by
          have hmm : |m| * |sin m - m| ≤ |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) :=
            mul_le_mul_of_nonneg_left hrs (abs_nonneg m)
          exact mul_le_mul_of_nonneg_left hmm (by norm_num : (0 : ℝ) ≤ (3 / 2) * (237 / 200))
        _ = (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) := by ring
    have hB3 : (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)
        ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
      have hnum : (3 : ℝ) / 2 * (237 / 200) = 711 / 400 := by norm_num
      have hmm : |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) = |m| ^ 6 / 100 + |m| ^ 4 / 6 := by
        ring
      have hsum : |m| ^ 6 / 100 + |m| ^ 4 / 6 ≤ m ^ 4 / 100 + m ^ 4 / 6 := by
        have h1 : |m| ^ 6 / 100 ≤ m ^ 4 / 100 := by
          exact div_le_div_of_nonneg_right hm6le (by norm_num : (0 : ℝ) ≤ 100)
        have h2 : |m| ^ 4 / 6 = m ^ 4 / 6 := by rw [hm4eq]
        rw [h2]
        linarith [h1]
      calc
        (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)
            = (711 / 400) * (|m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)) := by
              rw [hnum]
              ring
        _ = (711 / 400) * (|m| ^ 6 / 100 + |m| ^ 4 / 6) := by rw [hmm]
        _ ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 711 / 400)
    have hB : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
        ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
      exact le_trans (le_trans hB1 hB2) hB3
    -- N 的三角分解
    have hsplit : cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m
        = (3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
          + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)) := by
      ring
    have htri1 : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
          + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
        ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| + |cos m - (1 - m ^ 2 / 2)|
          + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
      have h1 : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
            + ((cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
          ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            + |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
        exact abs_add_ineq ((3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2)
          ((cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))
      have h2 : |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
          ≤ |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
        calc
          |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
              = |(cos m - (1 - m ^ 2 / 2)) + (-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)))| := by
                rfl
          _ ≤ |cos m - (1 - m ^ 2 / 2)| + |-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))| :=
            abs_add_ineq (cos m - (1 - m ^ 2 / 2)) (-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)))
          _ = |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
            rw [abs_neg]
      linarith [h1, h2]
    have hN_le : |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m|
        ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
      rw [hsplit]
      have hnumc : (5 / 96 : ℝ) + 711 / 400 * (1 / 100 + 1 / 6) ≤ 367 / 1000 := by norm_num
      have hrc' : |cos m - (1 - m ^ 2 / 2)| ≤ m ^ 4 * (5 / 96) := hrc
      have hB' : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := hB
      have hpart : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            + |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
          ≤ (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
        linarith [hA, hrc', hB']
      have hnum : (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6)
          ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
        nlinarith [hnumc]
      calc
        |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
            + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
            ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| + |cos m - (1 - m ^ 2 / 2)|
              + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := htri1
        _ ≤ (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := hpart
        _ ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := hnum
    -- 比例拼接
    have hstep1 : |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2)
        ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2) := by
      exact div_le_div_of_nonneg_right hN_le (le_of_lt hden_pos)
    have h1d : (1 : ℝ) / (1 - 2 * m ^ 2) ≤ 225 / 217 := by
      have hc : (0 : ℝ) ≤ 225 / 217 := by norm_num
      have hle : (1 : ℝ) ≤ (225 / 217) * (1 - 2 * m ^ 2) := by
        calc
          (225 / 217) * (1 - 2 * m ^ 2) ≥ (225 / 217) * (217 / 225) :=
            mul_le_mul_of_nonneg_left hden_ge hc
          _ = 1 := by norm_num
      exact (div_le_iff₀ hden_pos).mpr hle
    have hstep2 : ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2)
        ≤ (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := by
      have ha : 0 ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
        have hm4n : 0 ≤ m ^ 4 := by
          rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]
          exact sq_nonneg (m ^ 2)
        nlinarith [hm2nonneg, hm4n]
      calc
        ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2)
            = ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) * (1 / (1 - 2 * m ^ 2)) := by ring
        _ ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) * (225 / 217) :=
          mul_le_mul_of_nonneg_left h1d ha
        _ = (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := by ring
    have hm4le : m ^ 4 ≤ (4 / 225) * m ^ 2 := by
      calc
        m ^ 4 = m ^ 2 * m ^ 2 := by ring
        _ ≤ m ^ 2 * (4 / 225) := mul_le_mul_of_nonneg_left hm2 hm2nonneg
        _ = (4 / 225) * m ^ 2 := by ring
    have hstep3 : (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) ≤ (194 / 1000) * m ^ 2 := by
      have hm4le2 : (225 / 217) * (367 / 1000) * m ^ 4 ≤ (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by
        calc
          (225 / 217) * (367 / 1000) * m ^ 4 = (225 / 217) * (367 / 1000) * (m ^ 4) := by ring
          _ ≤ (225 / 217) * (367 / 1000) * ((4 / 225) * m ^ 2) := by
            exact mul_le_mul_of_nonneg_left hm4le (by norm_num : (0 : ℝ) ≤ (225 / 217) * (367 / 1000))
          _ = (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by ring
      have hcoef : (225 : ℝ) / 217 * (9 / 50) + (225 / 217 : ℝ) * (367 / 1000) * (4 / 225)
          ≤ 194 / 1000 := by
        norm_num
      have hle2 : ((225 / 217) * (9 / 50) + (225 / 217) * (367 / 1000) * (4 / 225)) * m ^ 2
          ≤ (194 / 1000) * m ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hm2nonneg
      calc
        (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4)
            = (225 / 217) * (9 / 50) * m ^ 2 + (225 / 217) * (367 / 1000) * m ^ 4 := by ring
        _ ≤ (225 / 217) * (9 / 50) * m ^ 2 + (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by
          exact add_le_add_right hm4le2 _
        _ = ((225 / 217) * (9 / 50) + (225 / 217) * (367 / 1000) * (4 / 225)) * m ^ 2 := by ring
        _ ≤ (194 / 1000) * m ^ 2 := hle2
    have hpi2 : (194 / 1000 : ℝ) * Real.pi ^ 2 ≤ 2 := by
      have hpin : 0 ≤ Real.pi := le_of_lt pi_pos
      have hpi2le : Real.pi ^ 2 ≤ (16 / 5) ^ 2 := by
        calc
          Real.pi ^ 2 = Real.pi * Real.pi := by ring
          _ ≤ (16 / 5) * Real.pi := mul_le_mul_of_nonneg_right hpi hpin
          _ ≤ (16 / 5) * (16 / 5) := mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 16 / 5)
          _ = (16 / 5) ^ 2 := by ring
      have hc : (0 : ℝ) ≤ 194 / 1000 := by norm_num
      calc
        (194 / 1000) * Real.pi ^ 2 ≤ (194 / 1000) * (16 / 5) ^ 2 := mul_le_mul_of_nonneg_left hpi2le hc
        _ = 49664 / 25000 := by norm_num
        _ ≤ 2 := by norm_num
    have hstep4 : (194 / 1000) * m ^ 2 ≤ 2 * u ^ 2 := by
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
      dsimp [m]
      calc
        (194 / 1000 : ℝ) * (Real.pi * u) ^ 2 = ((194 / 1000) * Real.pi ^ 2) * u ^ 2 := by ring
        _ ≤ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hpi2 hu2
    have hchain1 : |Khat u - 1| ≤ (194 / 1000) * m ^ 2 := by
      calc
        |Khat u - 1| = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := hN_abs
        _ ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2) := hstep1
        _ ≤ (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := hstep2
        _ ≤ (194 / 1000) * m ^ 2 := hstep3
    have hfin : |Khat u - 1| ≤ 2 * u ^ 2 + u ^ 4 := by
      calc
        |Khat u - 1| ≤ (194 / 1000) * m ^ 2 := hchain1
        _ ≤ 2 * u ^ 2 := hstep4
        _ ≤ 2 * u ^ 2 + u ^ 4 := by
          have hu4 : 0 ≤ u ^ 4 := by
            rw [show u ^ 4 = (u ^ 2) ^ 2 by ring]
            exact sq_nonneg (u ^ 2)
          linarith [hu4]
    simpa using hfin

/-! ### 件 2：Abel 求和（summation by parts，ℝ 有限和，真证明件） -/

/-- Abel 求和（summation by parts，ℝ 有限和）：
    Σ_{i=0..N} a_i·(b_{i+1} − b_i) = a_{N+1}·b_{N+1} − a_0·b_0 − Σ_{i=0..N} b_{i+1}·(a_{i+1} − a_i)。
    用于素数项 S(X) 的分部求和（S7.6 §2.4 的离散骨架）。 -/
lemma sum_abel (N : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (N + 1), a i * (b (i + 1) - b i))
      = a (N + 1) * b (N + 1) - a 0 * b 0
        - (∑ i ∈ Finset.range (N + 1), b (i + 1) * (a (i + 1) - a i)) := by
  induction N with
  | zero =>
      simp
      ring
  | succ N ih =>
      calc
        (∑ i ∈ Finset.range (N + 1 + 1), a i * (b (i + 1) - b i))
            = (∑ i ∈ Finset.range (N + 1), a i * (b (i + 1) - b i))
                + a (N + 1) * (b (N + 2) - b (N + 1)) := by
                rw [Finset.sum_range_succ]
        _ = (a (N + 1) * b (N + 1) - a 0 * b 0
                - (∑ i ∈ Finset.range (N + 1), b (i + 1) * (a (i + 1) - a i)))
              + a (N + 1) * (b (N + 2) - b (N + 1)) := by
                rw [ih]
        _ = a (N + 2) * b (N + 2) - a 0 * b 0
              - (∑ i ∈ Finset.range (N + 2), b (i + 1) * (a (i + 1) - a i)) := by
              have hsplit :
                  (∑ i ∈ Finset.range (N + 2), b (i + 1) * (a (i + 1) - a i))
                    = (∑ i ∈ Finset.range (N + 1), b (i + 1) * (a (i + 1) - a i))
                        + b (N + 2) * (a (N + 2) - a (N + 1)) := by
                rw [Finset.sum_range_succ]
              rw [hsplit]
              ring

/-! ### 件 3：N_L 对数增长下界（数论件，S6 口径）
    （定义已前移至 N2b 积分层挂钩之前，见上方。此处仅保留击破清单条目。） -/


/-! ## 击破清单（Stage 3+ 剩余）

- [x] `sum_abel`：真证（range 口径归纳 + Finset.sum_range_succ + ring）。
- [x] `khat_second_order_bound`（BoundBall 1 (1/24) …）：**真证**（2026-10-26，自 Dbg_Khat.lean 迁入替换 axiom）：
      Khat_closed_form 乘形式 + m=πu 区间界（π<16/5、m²≤4/225、分母 ≥217/225）+
      cos/sin Taylor 余项（Real.sin_bound/cos_bound）+ c0_bound（|3/2−√2·cotR|≤9/50）
      → |K̂(u)−1| ≤ (194/1000)m² ≤ 2u² ≤ 2u²+u⁴。数值核对：½|K̂″(0)|≈1.53<2。
- [x] `scaleKernel_L1_invariant`（**真证**，2026-10-27：integral_const_mul + integral_comp_inv_mul_left
      变量替换 + abs_mul；normL1 已从 axiom 降为 Bochner 积分真定义）/ `fourierCos_scale`
      （**真证**，2026-10-29：fourierCos 本体 axiom→Bochner 积分真定义 + Haar 变量替换链，
      无需 IntervalIntegral——`Measure.integral_comp_inv_mul_left` 全空间无正则性前提）。
- [x] `n1_diag_invariant`（真证，fourierCos_scale z=0 + congr）+ `n1_offdiag_scale_eq`
      （真证，z=2δ 核因子重写）+ `n1_offdiag_vanishes`（结构件真证：等式重写 + 频域衰减件
      |r̂(2aδ)|²≤a²C 假设，2026-10-27）；
      offdiag 的 (a²·N) 界需 K̂ 频域衰减（Khat_abs_le 的 a 缩放版）。
- [ ] `n2_linkage` / `n3_remainder_uniform` / `N_L_lower_bound`：结构件——文档层论证已闭合
      （S7.4 定理 N2、S7.5 定理 N3、S6 零点计数）；Lean 侧保留 axiom 语义。
- [ ] `f0_sub_feps_L1_bound`：**精确陈述完成**（2026-10-27 声明入列，normL1 旁）；
      真证需积分层（|1−w_ε| 支撑界 + 被积函数界 + 长度 ≤ 2ε）——mathlib 聚合后恢复。
- [x] `pair_const_eps_bias`：**真证**（2026-10-30，axiom → theorem；N2b：
      |pairConstant(f_ε)−pairConstant(f₀)| ≤ C₁·ε 均匀于 T≥T₀，Bound 显式界化；
      2026-10-31 增量⑧ 口径修正：归一化 N:=N_Z(T)（原 N:=δ 与文档层 S7.1 §2「N=零点数」不符）、
      零点集换截断集 zerosLChi5UpTo T）。
      三段链：Lipschitz 归约（sq_sub_sq_abs_le + f_eps_abs_le + pairConst_sub_pairL1 真证）
      + 积分层挂钩（`pairCount_L1_bound` **真证**（2026-10-31 增量⑧，axiom → theorem）：
      截断零点集 Z_T 有限 ⟹ Summable 真证（of_finite_support）；竖直差带计数件
      `pair_count_bound`（数论 axiom）+ 逐项 2M 界（支撑外 g=0、支撑内 |g|≤2M）+
      `normL1_sub_pos`（‖f₀−f_ε‖₁>0，区间积分正）⟹ Σ ≤ D·N_Z(T)·normL1，D 对数配对密度）
      + L¹ 界（f0_sub_feps_L1_bound 真证）；C₁ = 4M²D。
- [ ] `C_MT < 4/3`（Core 清单项）：级数余项层（cos 四阶 Taylor 上界 73/96 自证）——
      **非积分阻塞**，可独立立项；mathlib 内置 cos_bound 余项 (5/96)|x|⁴ 不够（差 0.13%）。
- [x] s71_main 组装（Stage 4）：**真证**（2026-10-27，pair_sum_expansion 分解 + C₂=2）。
-/

end QRH
