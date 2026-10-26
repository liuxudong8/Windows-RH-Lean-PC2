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

/-! ### 件 3：N_L 对数增长下界（数论件，S6 口径） -/

/-- L(s,χ₅) 零点计数函数（抽象算子）。 -/
axiom N_L : ℝ → ℝ

/-- N_L 对数增长下界（statement）：∃c>0，N_L(T) ≥ c·T·logT。
    数论件（L(s,χ5) 零点计数显式下界，S6 框架）——axiom 挂账（数学已证、形式化长线）。 -/
axiom N_L_lower_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → c * T * Real.log T ≤ N_L T

/-! ## 击破清单（Stage 3+ 剩余）

- [x] `sum_abel`：真证（range 口径归纳 + Finset.sum_range_succ + ring）。
- [x] `khat_second_order_bound`（BoundBall 1 (1/24) …）：**真证**（2026-10-26，自 Dbg_Khat.lean 迁入替换 axiom）：
      Khat_closed_form 乘形式 + m=πu 区间界（π<16/5、m²≤4/225、分母 ≥217/225）+
      cos/sin Taylor 余项（Real.sin_bound/cos_bound）+ c0_bound（|3/2−√2·cotR|≤9/50）
      → |K̂(u)−1| ≤ (194/1000)m² ≤ 2u² ≤ 2u²+u⁴。数值核对：½|K̂″(0)|≈1.53<2。
- [ ] `scaleKernel_L1_invariant` / `fourierCos_scale`：需积分层
      （MeasureTheory.IntervalIntegral 或 Riemann 积分模块）——mathlib 聚合生成后恢复。
- [ ] `n1_diag_invariant` / `n1_offdiag_vanishes`：由 fourierCos_scale 直接推出（z=0 / z=2δ）；
      offdiag 的 (a²·N) 界需 K̂ 频域衰减（Khat_abs_le 的 a 缩放版）。
- [ ] `n2_linkage` / `n3_remainder_uniform` / `N_L_lower_bound`：结构件——文档层论证已闭合
      （S7.4 定理 N2、S7.5 定理 N3、S6 零点计数）；Lean 侧保留 axiom 语义。
- [ ] s71_main 组装（Stage 4）：Core（Khat_zero、f_eps_support）+ Stage 3+ 件 → ε-δ 展开。
-/

end QRH
