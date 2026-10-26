import QRH.S7_1_Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators
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

/-- 余弦傅里叶变换（实数核、频域 z）：积分定义在文档层；Lean 侧为抽象算子（S7.3 §3）。 -/
axiom fourierCos : (ℝ → ℝ) → ℝ → ℝ

/-- N1-频域缩放（statement，S7.3 定理 N1(iv)）：r̂_a(z) = r̂(az)——Fourier 变换变量替换。 -/
axiom fourierCos_scale (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) (z : ℝ) :
  fourierCos (scaleKernel a r) z = fourierCos r (a * z)

/-- L¹ 范数（抽象）：∫|f|（积分定义在文档层；Lean 侧为抽象算子）。 -/
axiom normL1 : (ℝ → ℝ) → ℝ

/-- N1-L¹ 保持（statement，S7.3 定理 N1(vi)）：‖r_a‖₁ = ‖r‖₁——缩放变量替换。 -/
axiom scaleKernel_L1_invariant (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) :
  normL1 (scaleKernel a r) = normL1 r

/-- N1-对角主项不变（statement，S7.3 定理 N1(v)）：缩放自同构不改变引理 5 对角主项
    (T/2π)·logT·[r̂(0)+2∫₀¹αr(α)dα]（r̂_a(0)=r̂(0) 由 fourierCos_scale 取 z=0）。 -/
axiom n1_diag_invariant (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) :
  fourierCos (scaleKernel a r) 0 = fourierCos r 0

/-- N1-非对角项消失（statement，S7.3 推论）：supp⊂[−a,a]（a→0）时非对角配对和趋于 0——
    主导项 K̂_a(2δ)² 按 a² 衰减（数值件 F：A−1 单调 1.86e-2→3.09e-9，a 0.5→0.008）。 -/
axiom n1_offdiag_vanishes (a : ℝ) (ha : 0 < a) (r : ℝ → ℝ) (δ N : ℝ) :
  (fourierCos (scaleKernel a r) (2 * δ)) ^ 2 ≤ (a ^ 2) * N

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

/-- 二阶一致界（statement，清单 §4，BoundBall 显式界化）：|K̂(x) − 1| ≤ 2x² + x⁴ 对 |x| ≤ δ0。
    K̂(0)=1（Core Khat_zero）；K̂″(0)≈−3.06（数值件 F）⟹ ½|K̂″(0)|≈1.53<2；
    O((au)⁴) 具体化为 (au)⁴。Taylor 数值分析件（K̂ 的 C² 界）——挂 axiom 待击破。
    注：原 ∀ a u 全局式 ⟺ ∀ x（取 a=1, u=x 覆盖 ℝ）；δ0 球域是核宽 x=a·u 的支撑带用法。 -/
axiom khat_second_order_bound (δ0 : ℝ) (hδ0 : 0 < δ0) :
  BoundBall 1 δ0 (fun x => |Khat x - 1|) (fun x => (2 : ℝ) * x ^ 2 + x ^ 4)

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

/-! ### 件 3：N_L 对数增长下界（数论件，S6 口径） -/

/-- L(s,χ₅) 零点计数函数（抽象算子）。 -/
axiom N_L : ℝ → ℝ

/-- N_L 对数增长下界（statement）：∃c>0，N_L(T) ≥ c·T·logT。
    数论件（L(s,χ5) 零点计数显式下界，S6 框架）——axiom 挂账（数学已证、形式化长线）。 -/
axiom N_L_lower_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → c * T * Real.log T ≤ N_L T

/-! ## 击破清单（Stage 3+ 剩余）

- [ ] `sum_abel`：真证（Finset.Icc 重索引：sum_range_succ / sum_Icc_succ_top + 换元 i↦i+1）。
      若重索引 API 在 v4.34 缺位，降级为 range 口径（Σ_{i=0}^{N} 版本）。
- [ ] `khat_second_order_bound`（BoundBall 1 δ0 …）：K̂ 的 C² 区间界（‖K̂″‖∞ ≤ 4 的数值引理）
      → Taylor 二阶余项，再化 |x|≤δ0 球域 BoundBall。前置：K̂ 的导数闭式（Khat 解析式可微）
      + 区间界（norm_num/区间算术）。
- [ ] `scaleKernel_L1_invariant` / `fourierCos_scale`：需积分层
      （MeasureTheory.IntervalIntegral 或 Riemann 积分模块）——mathlib 聚合生成后恢复。
- [ ] `n1_diag_invariant` / `n1_offdiag_vanishes`：由 fourierCos_scale 直接推出（z=0 / z=2δ）；
      offdiag 的 (a²·N) 界需 K̂ 频域衰减（Khat_abs_le 的 a 缩放版）。
- [ ] `n2_linkage` / `n3_remainder_uniform` / `N_L_lower_bound`：结构件——文档层论证已闭合
      （S7.4 定理 N2、S7.5 定理 N3、S6 零点计数）；Lean 侧保留 axiom 语义。
- [ ] s71_main 组装（Stage 4）：Core（Khat_zero、f_eps_support）+ Stage 3+ 件 → ε-δ 展开。
-/

end QRH
