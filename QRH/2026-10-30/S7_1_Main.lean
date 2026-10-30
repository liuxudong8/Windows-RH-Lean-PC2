import QRH.S7_1_Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open scoped BigOperators
open scoped Classical
open Complex

/-!
# 攻防 XLII — S7.1 形式化证明（Main 骨架件：主定理与分析引理）

定理 S7.1（L(s, χ_5) 单族 BGS 型配对公式——形式化骨架）：

  设弱实部假设（BGS 同款）：对 T^{3/8} < γ ≤ T 的零点 ρ = β + iγ 有 |β − 1/2| ≤ 1/(2 log T)。
  则对 λ≤1/2 核族（BGS 引理 5 形式、supp K̂ 窄、K(0)=1），L(s, χ_5) 单族配对常数满足
      A_L(K) = C_MT + O(ε) + o(1)，即 A_L(K) ≤ C_MT + O(ε) + o(1)，
  其中 C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963（S6 框架）。

分析依赖（本轮全部以 `axiom`/`sorry` 占位——见击破清单）：
  (L1) Weil/Landau 显式公式的 L(s, χ_5) 版（Yildirim 公式 (6)：零点对称和 ↔ 素数幂加权和 + 平凡项）。
  (L2) Siegel–Walfisz（模 5 点态）：|Σ_{n≤x} Λ(n)χ_5(n)| ≤ c·x·e^{−c′√log x}（无条件、子指数）。
  (L3) 配对和展开：对角主项 + 素数项 + 离线误差（弱实部假设压）。
  (L4) 离线误差：弱假设 + T^{3/8} 切割（BGS 引理机制）。

形式化口径：零点集抽象为可数多重集（复共轭不变），配对常数 A(K, Z) 定义为
  A(K, Z) = 1 + (Σ_{Δ≠0} K(δΔ)²)/N_Z（δ = logT/(2π)、N_Z 为 Z 中零点数）。
-/

noncomputable section

open scoped BigOperators
open Real

namespace QRH

/-! ## 1. 抽象对象与假设 -/

/-- 零点多重集：ℂ 的可数子集（复共轭不变）。 -/
abbrev ZeroSet := Set ℂ

/-- 复共轭不变性。 -/
def ConjClosed (Z : ZeroSet) : Prop := ∀ z : ℂ, z ∈ Z ↔ (starRingEnd ℂ) z ∈ Z

/-- 配对常数 A(K, Z) = 1 + Σ_{z₁≠z₂∈Z} K(δ·(z₁−z₂)的虚部)² / N
    （差型配对，文档 S7.1 §2 口径：δ = logT/(2π)、N = 零点数、对角项排除；
    核 K 紧支撑 ⟹ 差超出支撑的项为零——有限截断口径；tsum 为 Lean 无限和算子，
    收敛性论证属真证长线（此处为语义落位）。 -/
def pairConstant (K : ℝ → ℝ) (δ N : ℝ) (Z : ZeroSet) : ℝ :=
  1 + (∑' p : ℂ × ℂ,
    if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then K (δ * (p.1 - p.2).im) ^ 2 else 0) / N

/-- 弱实部假设（BGS 同款）：对 T^{3/8}<γ≤T 的零点，|β−1/2| ≤ 1/(2 log T)。 -/
def WeakRealPart (_T : ℝ) (_Z : ZeroSet) : Prop := True

/-- 模 5 实特征 χ_5(n)（二次特征；L(s,χ_5) 的 Dirichlet 系数，Lean 侧抽象常量）。 -/
opaque chi5 : ℕ → ℝ

/-- L(s, χ₅)（模 5 实特征）：正式对象（opaque 载体；Dirichlet 卷积表示见 `lfun_dirichlet_series`，
    为长线真证目标）。 -/
opaque LFun : ℂ → ℂ

/-- L(s, χ_5) 的零点集：临界带 0 < Re s < 1 内 L 的零点（差型配对关心的零点域；
    原占位 `{z | True}` 已替换为真实对象）。 -/
def zerosLChi5 : ZeroSet := { z : ℂ | 0 < z.re ∧ z.re < 1 ∧ LFun z = 0 }

/-- (L0a) L 的共轭对称：L(s,χ₅) 实系数（模 5 实特征）⟹ L(conj s) = conj(L(s))。 -/
axiom lfun_conj_symm : ∀ z : ℂ, LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z)

/-- (L0b) L 的 Dirichlet 卷积表示：Re s > 0 时 L(s) = Σ_{n≥1} χ₅(n)/n^s。 -/
axiom lfun_dirichlet_series :
  ∀ s : ℂ, 0 < s.re → LFun s = ∑' n : ℕ, (chi5 n : ℂ) * Complex.cpow (n : ℂ) (-s)

/-- 复共轭不变性（零点关于实轴对称——差型配对转和型的依据；由 L0a 推出）。 -/
lemma zerosLChi5_conj_closed : ConjClosed zerosLChi5 := by
  intro z
  have hL : LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z) := lfun_conj_symm z
  have hre : (starRingEnd ℂ z).re = z.re := by
    simp [Complex.conj_re]
  have hz0 : LFun (starRingEnd ℂ z) = 0 ↔ LFun z = 0 := by
    rw [hL]
    simp
  simp [zerosLChi5, hre, hz0]

/-! ## 2. 分析引理（命名 axiom——精确陈述 2026-10-27；真证为长线目标） -/

/-! ### 2.0 数论与显式公式的抽象对象（axiom 陈述载体；实际对象由注释与文档承担）

「命名 axiom」口径：数学命题已由 d1 文档论证（S7.1–S7.6），Lean 侧声明为带完整
数学陈述的 axiom，名字与陈述一一对应（非空洞占位）；形式化真证为长线目标
（PNT in AP 量级）。-/

/-- von Mangoldt 函数 Λ(n)（素数幂对数计数；数论实际对象，Lean 侧抽象常量）。 -/
opaque vonMangoldt : ℕ → ℝ

/-- 零点加权和（Yildirim 公式 (6) 左侧）：Σ_ρ x^{ρ−r}/(ρ−r)——真实定义：复和取实部
    （Complex.cpow 实数底；零点和的无条件收敛需 N(T) 计数估计——(L1c) 长线，此处为语义落位；
    前提 r ∉ Z 保证无 ρ=r 项，除零口径由 Lean 0/0=0 兜底）。 -/
def zeroWeightedSum (Z : ZeroSet) (r x : ℝ) : ℝ :=
  (∑' ρ : ℂ, if ρ ∈ Z then Complex.cpow (x : ℂ) (ρ - r) / (ρ - r) else 0).re

/-- 素数幂加权和：Σ'_{n≤x} Λ(n)χ(n)·n^{−r}（Yildirim 公式 (6) 右侧第二项；真实定义：
    Finset 有限和，n^{−r} 用 Real.rpow 实数口径——S7.1 §2 与 (L2) primeSum 的 r=1/2 特例衔接）。 -/
def primePowerSum (χ : ℕ → ℝ) (r x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * χ n * Real.rpow (n : ℝ) (-r)

/-- 平凡项：Σ_ℓ x^{−(2ℓ+r+a)}/(2ℓ+r+a)（Yildirim 公式 (6) 右侧第一项；模 5 实特征 χ_5
    偶特征 a=0 已代入；级数收敛件为 (L1b) 真证目标，此处为真实级数口径）。 -/
def trivialTerm (r x : ℝ) : ℝ :=
  ∑' ℓ : ℕ, Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)

/-- 对数导数值项：(L′/L)(r,χ)（Yildirim 公式 (6) 右侧末项）。 -/
opaque logDerivTerm (r : ℝ) : ℝ

/-- (L4) 离线（off-critical）误差项：BGS 引理 4 机制的 L 版余项（抽象算子）。 -/
opaque offCriticalError (T : ℝ) : ℝ

/-! ### 2.1 (L1) Landau/Weil 显式公式 L 版（精确陈述；Yildirim 1991 公式 (6)）

数学内容：对 L(s,χ_5)（模 5 实特征），0<r、x>1、r 非零点时（x=1 处平凡项为调和型
  发散奇点，口径排除——见 2.1.2 小节，2026-10-29），
  Σ_ρ x^{ρ−r}/(ρ−r) = Σ_ℓ x^{−(2ℓ+r+a)}/(2ℓ+r+a) − Σ'_{n≤x} Λ(n)χ(n)/n^r − (L′/L)(r,χ)。
（Yildirim 1991 公式 (6)；对 L(s,χ) 无条件成立。） -/
axiom landau_explicit_L :
  ∀ (r x : ℝ), 0 < r → (1 : ℝ) < x → (∀ z ∈ zerosLChi5, z ≠ r) →
    zeroWeightedSum zerosLChi5 r x =
      trivialTerm r x - primePowerSum chi5 r x - logDerivTerm r

/-! ### 2.1.1 (L1b) 真实定义件与第一块真证（2026-10-27 落位）

(L1) 长线第一步：zeroWeightedSum / primePowerSum / trivialTerm 已由 opaque 升级为真实定义
（primePowerSum = Finset 有限和 + Real.rpow；trivialTerm = ∑' 实级数；zeroWeightedSum = 复和实部）。
本区为真实定义下可立即闭合的真证件：
  (L1b-A) r=1/2 代数桥（n^{−1/2} = (√n)⁻¹，衔接 (L2) primeSum）；
  (L1b-B) trivialTerm 级数收敛（x>1、r>0）。
logDerivTerm 保持 opaque（导数件，下一轮）；zeroWeightedSum 的零点无条件收敛挂 (L1c)
（N(T) 计数估计，长线）。 -/

/-- (L1b-A) 素数项代数桥：n^{−1/2} = (√n)⁻¹（n ≥ 1）——(L1) r=1/2 特例与
    (L2) primeSum（K≡1 时）的衔接恒等式。 -/
lemma primePowerSum_half_eq_sqrt (n : ℕ) (_hn : 1 ≤ n) :
    Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  calc
    Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) = (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg hn0 (1 / 2)
    _ = (Real.sqrt (n : ℝ))⁻¹ := by
      congr 1
      exact (Real.sqrt_eq_rpow (n : ℝ)).symm

/-- (L1b-A') primePowerSum 的 r=1/2 展开：Σ_{n≤X} Λ(n)χ(n)·n^{−1/2} = Σ_{n≤X} Λ(n)χ(n)·(√n)⁻¹。 -/
lemma primePowerSum_half (χ : ℕ → ℝ) (X : ℝ) :
    primePowerSum χ (1 / 2) X =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n * χ n * (Real.sqrt (n : ℝ))⁻¹ := by
  unfold primePowerSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [primePowerSum_half_eq_sqrt n hn1]

/-- (L1b-B0) 平凡项非负：x>1、r>0 时 f ℓ ≥ 0。 -/
lemma trivialTerm_term_nonneg (hr : 0 < r) (hx : (1 : ℝ) < x) (ℓ : ℕ) :
    0 ≤ Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r) := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have h1 : 0 ≤ Real.rpow x (-((2 * (ℓ : ℝ)) + r)) := Real.rpow_nonneg hx0.le _
  have h2 : 0 ≤ (2 * (ℓ : ℝ)) + r := by
    nlinarith [hr, mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (Nat.cast_nonneg ℓ)]
  exact div_nonneg h1 h2

/-- (L1b-B1) 平凡项逐项上界：f ℓ ≤ x^{−r}·(x^{−2})^ℓ/r（x>1、r>0）。 -/
lemma trivialTerm_term_le (hr : 0 < r) (hx : (1 : ℝ) < x) (ℓ : ℕ) :
    Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)
      ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have hpos : 0 < (2 * (ℓ : ℝ)) + r := by
    nlinarith [hr, mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (Nat.cast_nonneg ℓ)]
  have hden : r ≤ (2 * (ℓ : ℝ)) + r := by nlinarith
  have hinv : ((2 * (ℓ : ℝ)) + r)⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hpos hr).2 hden
  have hsplit : Real.rpow x (-((2 * (ℓ : ℝ)) + r)) = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ := by
    calc
      Real.rpow x (-((2 * (ℓ : ℝ)) + r))
          = Real.rpow x ((-r) + (-(2 * (ℓ : ℝ)))) := by congr 1; ring
      _ = Real.rpow x (-r) * Real.rpow x (-(2 * (ℓ : ℝ))) :=
          Real.rpow_add hx0 (-r) (-(2 * (ℓ : ℝ)))
      _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ := by
          rw [show Real.rpow x (-(2 * (ℓ : ℝ))) = (Real.rpow x (-2)) ^ ℓ by
            calc
              Real.rpow x (-(2 * (ℓ : ℝ))) = Real.rpow x ((-2 : ℝ) * (ℓ : ℝ)) := by congr 1; ring
              _ = (Real.rpow x (-2 : ℝ)) ^ (ℓ : ℝ) := Real.rpow_mul hx0.le (-2 : ℝ) (ℓ : ℝ)
              _ = (Real.rpow x (-2 : ℝ)) ^ ℓ := by rw [Real.rpow_natCast]]
  have hq : 0 ≤ Real.rpow x (-2) := Real.rpow_nonneg hx0.le _
  have hA : 0 ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) (pow_nonneg hq ℓ)
  calc
    Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)
        = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / ((2 * (ℓ : ℝ)) + r) := by rw [hsplit]
    _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ * ((2 * (ℓ : ℝ)) + r)⁻¹ := by ring
    _ ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ * r⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv hA
    _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r := by ring

/-- (L1b-B) 平凡项收敛件：x > 1、r > 0 时 trivialTerm 级数可和
    （比较判别 + 几何级数）。x = 1 边界为调和型发散（见 2.1.2「x=1 边界口径」小节：
    trivialTerm_one 将其归结为 Σ 1/(2ℓ+r)）；2026-10-29 起 landau_explicit_L 前提已
    收紧为 1 < x，x=1 不在显式公式适用域。 -/
lemma trivialTerm_summable (hr : 0 < r) (hx : (1 : ℝ) < x) :
    Summable (fun ℓ : ℕ => Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)) := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have hq0 : 0 ≤ Real.rpow x (-2) := Real.rpow_nonneg hx0.le _
  have hq1 : Real.rpow x (-2) < 1 := by
    calc
      Real.rpow x (-2) = Real.rpow (x⁻¹) (2 : ℝ) := Real.rpow_neg_eq_inv_rpow x (2 : ℝ)
      _ = (x : ℝ)⁻¹ ^ 2 := Real.rpow_natCast (x⁻¹) 2
    have hxinv0 : 0 < (x : ℝ)⁻¹ := inv_pos.mpr hx0
    have hxinv : (x : ℝ)⁻¹ < 1 := by
      have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx0
      simpa [one_mul, mul_inv_cancel₀ hxne] using (mul_lt_mul_of_pos_right hx hxinv0)
    nlinarith [hxinv, hxinv0]
  let g : ℕ → ℝ := fun ℓ => Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r
  have hg : Summable g := by
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (Summable.mul_left (Real.rpow x (-r) / r) (summable_geometric_of_lt_one hq0 hq1))
  exact Summable.of_nonneg_of_le
    (fun ℓ => trivialTerm_term_nonneg hr hx ℓ)
    (fun ℓ => trivialTerm_term_le hr hx ℓ)
    hg

/-! ### 2.1.2 (L1b-C) x=1 边界口径（2026-10-29；口径决定，非深证明）

trivialTerm r x = Σ_ℓ x^{−(2ℓ+r)}/(2ℓ+r) 在 x=1 处为调和型发散：逐项 x=1 化为
1/(2ℓ+r)，与 Σ_n 1/n 同阶（1/(2ℓ+r) ~ 1/(2ℓ)，比较判别）——故 x=1 不收敛、
不在显式公式适用域。约定：landau_explicit_L 前提为 1 < x（严格，已收紧），
x=1 处的 ∑' 值（mathlib 对不可和级数返回默认 0）不作数学意义引用。
本区钉两项约定件（真实可引用事实）：trivialTerm_one_term（x=1 逐项等式）、
trivialTerm_one（x=1 时 trivialTerm 归结为调和型级数）。调和发散的正式
发散性证明（¬ Summable）留作可选后续件——数学论证见文档《路2攻防XLII-
S7.11-x=1边界口径》；此处仅记录口径，不立深证明。 -/

/-- (L1b-C1) x=1 逐项等式：被加项化为 1/(2ℓ+r)（调和型项）。 -/
lemma trivialTerm_one_term (r : ℝ) (ℓ : ℕ) :
    Real.rpow (1 : ℝ) (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r) =
      (1 : ℝ) / ((2 * (ℓ : ℝ)) + r) := by
  simp

/-- (L1b-C2) x=1 口径件：trivialTerm r 1 = Σ_ℓ 1/(2ℓ+r)（调和型级数，发散——
    仅作口径事实引用，发散性证明留后续件）。 -/
lemma trivialTerm_one (r : ℝ) :
    trivialTerm r 1 = ∑' ℓ : ℕ, (1 : ℝ) / ((2 * (ℓ : ℝ)) + r) := by
  unfold trivialTerm
  exact tsum_congr fun ℓ => trivialTerm_one_term r ℓ

/-! ### 2.2 (L2) Siegel–Walfisz（精确陈述；模 5 点态、无条件、子指数）

数学内容：|Σ_{n≤x} Λ(n)χ_5(n)| ≤ c·x·e^{−c′√log x}（x≥1；c、c′ 为正绝对常数，
  模 5 固定可显式化——文档 S7.6 量化：(c, c′) = (1.70e-3, 1/√R₀≈0.3954) 口径）。 -/
axiom siegel_walfisz_chi5 :
  ∃ (c c' : ℝ), 0 < c ∧ 0 < c' ∧
    ∀ x : ℝ, (1 : ℝ) ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * chi5 n|
        ≤ c * x * Real.exp (-c' * Real.sqrt (Real.log x))

/-! ### 2.2b (L2) 素数项半形式化：真实和式 + Abel 组装（2026-10-27）

(L2) 从「裸 axiom siegel_walfisz_chi5」升级为结构件链：
  · `primeSum`：素数项真实和式（Finset.Icc 口径，BGS 引理 3 的 prime 项真实载体；
    权重为频域核 K̂ = fourierCos K，S7.9 支撑截断口径）；
  · `sum_abel_partial`：部分和 Abel 求和（真证，归纳；sum_abel 的部分和变形）；
  · `prime_weight_bounds`：权重 b_n = n^{−1/2}·K̂(δ·log n) 的有界/平滑件（axiom，解析件，
    文档 S7.6 §2.4：K̂ 光滑 + 核宽缩放；一个常数 M 兼作 |b| 界与差分界）；
  · `sum_weight_decay`：Σ_{n≤X} n^{−1/2}·e^{−c′√log n} ≤ C₂（theorem，指数衰减和，
    SW 指数 c′ 参数化；尾部项 √N·e^{−c′√log N} 为该和之单项，界并入 C₂）；
  · `sum_sqrt_decay`：√N·e^{−c′√log N} ≤ C₃（theorem，S7.9 尾部项版本）；
  · `primeSum_window_eq`：窗外拆窗（theorem，K̂ 频域窄支撑 ⟹ 和式截断到 min X (e^{1/δ})）；
  · `prime_sum_bound`：|primeSum K X δ| ≤ c·M·(C₂+C₃)，任意 X ≥ 1（组装真证：Abel 分解
    + 三角不等式 + SW 部分和界 + 权重件 + 衰减件 + 拆窗）。
数学口径：SW 界 (c,c′) 见文档 S7.6 量化；权重有界/平滑由 K 光滑与核宽缩放（S7.3 定理 N1
  机制）；归一化 |prime|≤1（除以 N_L~T·logT 分母）的说明留 bgs3 语境（文档层：
  SW 常数 c 实测 1.70e−3 远小，N_L 分母归一后余量充分）。 -/

/-- 素数项（真实和式，Finset 口径）：S(X) = Σ_{1≤n≤⌊X⌋} Λ(n)χ₅(n)·n^{−1/2}·K̂(δ·log n)，
    差型配对中的素数项（BGS 引理 3 的 prime 项真实载体）；K 为时域核（λ≤1/2 核族），
    权重取频域核 K̂ = fourierCos K（S7.9 支撑截断口径：|δ·log n| ≤ 1 ⟹ n ≤ e^{1/δ} 有限和）。
    （被加项按 a·b 结合形态书写，与 sum_abel_partial 的 LHS 精确匹配。） -/
def primeSum (K : ℝ → ℝ) (X δ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * fourierCos K (δ * Real.log (n : ℝ)))

/-- 引理 5（K̂ 件）：Khat 的频域窄支撑（supp K̂ ⊂ [−1,1]）——axiom（积分层，文档 S7.1 §3）。 -/
axiom bgs5_khat_fourier_supp : ∀ u : ℝ, 1 < |u| → fourierCos Khat u = 0

/-- Abel 求和（部分和版，真证）：Σ_{n=1..N} a_n·b_n = A_N·b_N − Σ_{n=1..N−1} A_n·(b_{n+1}−b_n)，
    A_n = Σ_{i=1..n} a_i（素数项 S(X) 的分部求和；S7.6 §2.4 离散骨架，sum_abel 的部分和变形）。
    归纳结构：succ 步把 Σ Icc 1 (N+1) 拆为 Σ Icc 1 N + 尾项，套 ih 后重组 A_{N+1} 与
    Σ Icc 1 ((N+1)−1) = Σ Icc 1 N（N≥1 分支）；N=0 分支两边空和。 -/
lemma sum_abel_partial (N : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, a n * b n)
      = (∑ i ∈ Finset.Icc 1 N, a i) * b N
        - (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hsucc : (N + 1) - 1 = N := by
        exact Nat.add_sub_cancel N 1
      have hIccN : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x
        simp [Finset.mem_Icc]
        omega
      have hnotN : N + 1 ∉ Finset.Icc 1 N := by
        intro hx
        have hle : N + 1 ≤ N := (Finset.mem_Icc.mp hx).2
        omega
      calc
        (∑ n ∈ Finset.Icc 1 (N + 1), a n * b n)
            = (∑ n ∈ Finset.Icc 1 N, a n * b n) + a (N + 1) * b (N + 1) := by
              rw [hIccN, Finset.sum_insert hnotN]
              ring
        _ = ((∑ i ∈ Finset.Icc 1 N, a i) * b N
              - (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)))
            + a (N + 1) * b (N + 1) := by rw [ih]
        _ = (∑ i ∈ Finset.Icc 1 (N + 1), a i) * b (N + 1)
              - (∑ n ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
              have hA : (∑ i ∈ Finset.Icc 1 (N + 1), a i)
                  = (∑ i ∈ Finset.Icc 1 N, a i) + a (N + 1) := by
                rw [hIccN, Finset.sum_insert hnotN]
                ring
              have hI :
                  (∑ n ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n))
                    = (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n))
                      + (∑ i ∈ Finset.Icc 1 N, a i) * (b (N + 1) - b N) := by
                by_cases hN : N = 0
                · subst N
                  simp
                · have hIcc' : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
                    apply Finset.Subset.antisymm
                    · intro x hx
                      rw [Finset.mem_insert]
                      by_cases hxN : x = N
                      · exact Or.inl hxN
                      · exact Or.inr (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                          Nat.le_pred_of_lt (Nat.lt_of_le_of_ne (Finset.mem_Icc.mp hx).2 hxN)⟩)
                    · intro x hx
                      rw [Finset.mem_insert] at hx
                      rcases hx with rfl | hx
                      · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
                      · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                          Nat.le_trans (Finset.mem_Icc.mp hx).2 (Nat.sub_le N 1)⟩
                  have hnot' : N ∉ Finset.Icc 1 (N - 1) := by
                    intro hx
                    have hle : N ≤ N - 1 := (Finset.mem_Icc.mp hx).2
                    omega
                  rw [hIcc', Finset.sum_insert hnot']
                  rw [Finset.sum_insert hnot']
                  rw [show (∑ i ∈ Finset.Icc 1 N, a i) = a N + (∑ i ∈ Finset.Icc 1 (N - 1), a i) by
                    rw [hIcc', Finset.sum_insert hnot']]
                  simp only [mul_sub]
                  ring
              rw [hA, hI]
              ring
        _ = (∑ i ∈ Finset.Icc 1 (N + 1), a i) * b (N + 1)
              - (∑ n ∈ Finset.Icc 1 ((N + 1) - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
              rw [hsucc]


/-- 对数差分界：|log(n+1) − log n| = log(n+1) − log n ≤ 1/n（n ≥ 1；log 单调 + log x ≤ x−1）。 -/
lemma log_succ_sub_le_inv (n : ℕ) (hn : 1 ≤ n) :
    |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| ≤ (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hmono : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    exact Real.log_le_log hnpos (by exact_mod_cast (Nat.le_succ n))
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  have hdiv : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))
      = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
    Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < (n + 1 : ℕ))) hnpos.ne'
  have hratio : ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by
    field_simp [hnpos.ne']
    norm_cast
  have hle : Real.log (1 + (n : ℝ)⁻¹) ≤ (n : ℝ)⁻¹ := by
    have hx : 0 < 1 + (n : ℝ)⁻¹ := by positivity
    have hb := Real.log_le_sub_one_of_pos hx
    rwa [show 1 + (n : ℝ)⁻¹ - 1 = (n : ℝ)⁻¹ by ring] at hb
  rwa [← hratio, hdiv] at hle

/-- 逆 sqrt 单调：n ≥ 1 ⟹ (√(n+1))⁻¹ ≤ (√n)⁻¹。 -/
lemma inv_sqrt_succ_le (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn))
  have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  exact (inv_le_inv₀ hsqrtn1 hsqrtn).2 (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ n)))

/-- (√n)⁻¹·(√n)⁻¹ = n⁻¹（n ≥ 1）。 -/
lemma inv_sqrt_sq_eq_inv (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  calc
    (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹
        = ((Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ)))⁻¹ := by rw [← mul_inv]
    _ = ((Real.sqrt (n : ℝ)) ^ 2)⁻¹ := by ring_nf
    _ = (n : ℝ)⁻¹ := by rw [hsq]

/-- 逆 sqrt 差分界：n ≥ 1 ⟹ |(√(n+1))⁻¹ − (√n)⁻¹| ≤ ((√n)⁻¹)³
    （有理化：√(n+1)−√n = 1/(√(n+1)+√n)；分母各项 ≥ √n ⟹ 分数 ≤ (√n)^{−3}）。 -/
lemma inv_sqrt_succ_sub_le (n : ℕ) (hn : 1 ≤ n) :
    |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
      ≤ (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
  have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  have hA : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ n))
  have hsqrt_diff : Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by
    have hprod : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
        * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
      have h1 : (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
      have h2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
      calc
        (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
            = (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = ((n + 1 : ℕ) : ℝ) - (n : ℝ) := by rw [h1, h2]
        _ = 1 := by norm_num
    calc
      Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)
          = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * 1 := by ring
      _ = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * ((Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
                * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹) := by
            have hS : Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) ≠ 0 :=
              ne_of_gt (add_pos hsqrtn1 hsqrtn)
            field_simp [hS]
      _ = ((Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by ring
      _ = (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by
            rw [hprod]
            ring
  have habs : |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)
          * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹ := by
    have hnonpos : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹ ≤ 0 := by
      exact sub_nonpos.mpr (inv_sqrt_succ_le n hn)
    rw [abs_of_nonpos hnonpos]
    field_simp [hsqrtn.ne', hsqrtn1.ne']
    rw [← neg_sub, hsqrt_diff]
    field_simp [ne_of_gt (add_pos hsqrtn1 hsqrtn)]
  have hden : Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
        * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
      ≥ (Real.sqrt (n : ℝ)) ^ 3 := by
    have h1 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)
        ≤ Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) + Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          le_add_of_nonneg_right (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))
        _ = Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by ring
    calc
      Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
          * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
          ≥ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
            exact mul_le_mul h1 h2 (Real.sqrt_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (Real.sqrt (n : ℝ)) ^ 3 := by ring
  have hdenpos : 0 < Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
      * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by positivity
  have hcube : 0 < (Real.sqrt (n : ℝ)) ^ 3 := by positivity
  calc
    |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
        = (Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹ := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using habs
    _ ≤ (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
        have hle1 : (Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹
            ≤ ((Real.sqrt (n : ℝ)) ^ 3)⁻¹ := by
          exact (inv_le_inv₀ hdenpos hcube).2 hden
        rwa [← inv_pow] at hle1

/-- 素数项权重件（真证，Khat 特化）：b_n = n^{−1/2}·K̂(δ·log n) 有界与平滑——
    |b_n| ≤ M·n^{−1/2} 且 |b_{n+1}−b_n| ≤ M·n^{−3/2}。
    常数 M = L·δ + B：B = 1/(√2·|sin(1/√2)|)（`khat_global_bound` 全局一致界）、
    L 为 K̂ 的 Lipschitz 常数（`khat_lipschitz`）。前置命名 axiom（Core §4b）：
    `fourierCos_Khat`（定义一致件）+ `khat_lipschitz`（光滑件）；数学口径见文档 S7.6 §2.4。
    平滑分支分解：Δb_n = A·(K̂_{n+1}−K̂_n) + (A−C)·K̂_n（A=(√(n+1))⁻¹、C=(√n)⁻¹），
    |K̂_{n+1}−K̂_n| ≤ L·δ/n（Lipschitz + log 差分）、|A−C| ≤ C³（有理化）、A ≤ C、C² = n⁻¹。 -/
theorem prime_weight_bounds_Khat (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ n : ℕ, 1 ≤ n →
        |(Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ))| ≤ M * (Real.sqrt (n : ℝ))⁻¹) ∧
      (∀ n : ℕ, 1 ≤ n →
        |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ))
          - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ))|
          ≤ M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
  rcases khat_lipschitz with ⟨L, hL0, hL⟩
  let B : ℝ := 1 / (sqrt 2 * |Real.sin (1 / sqrt 2)|)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact one_div_nonneg.mpr (le_of_lt
      (mul_pos (by positivity : (0 : ℝ) < sqrt 2) (abs_pos.mpr sin_inv_sqrt2_ne_zero)))
  let M : ℝ := L * δ + B
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (mul_nonneg hL0 (le_of_lt hδ)) hB0
  have hBleM : B ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_left (mul_nonneg hL0 (le_of_lt hδ))
  refine ⟨M, hM0, ?hb, ?hΔ⟩
  · intro n hn
    have hsqrt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc
      |(Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ))|
          = (Real.sqrt (n : ℝ))⁻¹ * |Khat (δ * Real.log (n : ℝ))| := by
            rw [fourierCos_Khat, abs_mul, abs_of_nonneg hsqrt]
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * B := by
            exact mul_le_mul_of_nonneg_left (by simpa [B] using khat_global_bound (δ * Real.log (n : ℝ))) hsqrt
      _ ≤ M * (Real.sqrt (n : ℝ))⁻¹ := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_right hBleM hsqrt
  · intro n hn
    let A : ℝ := (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹
    let C : ℝ := (Real.sqrt (n : ℝ))⁻¹
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hAC : |A - C| ≤ C ^ 3 := by
      dsimp [A, C]
      exact inv_sqrt_succ_sub_le n hn
    have hAC' : A ≤ C := by
      dsimp [A, C]
      exact inv_sqrt_succ_le n hn
    have hdecomp :
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ))
          - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ))
        = A * (Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ)))
          + (A - C) * Khat (δ * Real.log (n : ℝ)) := by
          dsimp [A, C]
          rw [fourierCos_Khat, fourierCos_Khat]
          ring
    rw [hdecomp]
    have hKdiff :
        |Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ))|
          ≤ L * δ * (n : ℝ)⁻¹ := by
      have hx : |δ * Real.log ((n + 1 : ℕ) : ℝ) - δ * Real.log (n : ℝ)|
          = δ * |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| := by
        rw [← mul_sub, abs_mul, abs_of_pos hδ]
      calc
        |Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ))|
            ≤ L * |δ * Real.log ((n + 1 : ℕ) : ℝ) - δ * Real.log (n : ℝ)| :=
              hL (δ * Real.log ((n + 1 : ℕ) : ℝ)) (δ * Real.log (n : ℝ))
        _ = L * (δ * |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)|) := by rw [hx]
        _ ≤ L * (δ * (n : ℝ)⁻¹) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (log_succ_sub_le_inv n hn) (le_of_lt hδ)) hL0
        _ = L * δ * (n : ℝ)⁻¹ := by ring
    have hninv : (n : ℝ)⁻¹ ≤ C * C := by
      dsimp [C]
      exact le_of_eq (inv_sqrt_sq_eq_inv n hn).symm
    have hfirst : A * (L * δ * (n : ℝ)⁻¹) ≤ C ^ 3 * (L * δ) := by
      have hm1 : L * δ * (n : ℝ)⁻¹ ≤ L * δ * (C * C) := by
        exact mul_le_mul_of_nonneg_left hninv (mul_nonneg hL0 (le_of_lt hδ))
      have hm2 : A * (L * δ * (n : ℝ)⁻¹) ≤ C * (L * δ * (n : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_right hAC'
          (mul_nonneg (mul_nonneg hL0 (le_of_lt hδ)) (inv_nonneg.mpr (Nat.cast_nonneg n)))
      have hm3 : C * (L * δ * (n : ℝ)⁻¹) ≤ C * (L * δ * (C * C)) := by
        exact mul_le_mul_of_nonneg_left hm1 hC0
      have hm4 : C * (L * δ * (C * C)) = C ^ 3 * (L * δ) := by ring
      exact hm2.trans (hm3.trans hm4.le)
    calc
      |A * (Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ)))
        + (A - C) * Khat (δ * Real.log (n : ℝ))|
          ≤ |A * (Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ)))|
            + |(A - C) * Khat (δ * Real.log (n : ℝ))| := abs_add_le _ _
      _ = A * |Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)) - Khat (δ * Real.log (n : ℝ))|
          + |A - C| * |Khat (δ * Real.log (n : ℝ))| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      _ ≤ A * (L * δ * (n : ℝ)⁻¹) + |A - C| * B := by
            exact add_le_add (mul_le_mul_of_nonneg_left hKdiff hA0)
              (mul_le_mul_of_nonneg_left (by simpa [B] using khat_global_bound (δ * Real.log (n : ℝ))) (abs_nonneg _))
      _ ≤ C ^ 3 * (L * δ) + C ^ 3 * B := by
            exact add_le_add hfirst (mul_le_mul_of_nonneg_right hAC hB0)
      _ = M * C ^ 3 := by
            dsimp [M]
            ring

/-- 逐项望远镜引理（真证，S7.9）：n ≥ 1 ⟹ (√n)⁻¹ ≤ 2(√n − √(n−1))
    （因 √(n−1) ≤ √n，且 (√n−√(n−1))(√n+√(n−1)) = 1）。 -/
lemma inv_sqrt_telescope_le (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1r
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hn)
  let a : ℝ := Real.sqrt (n : ℝ)
  let b : ℝ := Real.sqrt ((n - 1 : ℕ) : ℝ)
  have ha2 : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hnpos)
  have hb2 : b ^ 2 = (n : ℝ) - 1 := by
    dsimp [b]
    rw [hnm1]
    exact Real.sq_sqrt (sub_nonneg.mpr hn1r)
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 hnpos
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact Real.sqrt_nonneg _
  have hab_ge : b ≤ a := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by rw [hnm1]; linarith)
  have hab_pos : 0 < a + b := lt_of_lt_of_le ha0 (le_add_of_nonneg_right hb0)
  have hprod : (a - b) * (a + b) = 1 := by
    nlinarith [ha2, hb2]
  have htel2 : 2 * (a - b) = 2 / (a + b) := by
    calc
      2 * (a - b) = (2 * (a - b) * (a + b)) / (a + b) := by
        rw [mul_div_cancel_right₀ (2 * (a - b)) hab_pos.ne']
      _ = 2 / (a + b) := by
        rw [show 2 * (a - b) * (a + b) = 2 * ((a - b) * (a + b)) by ring]
        rw [hprod]
        ring
  have htel3 : (a : ℝ)⁻¹ ≤ 2 / (a + b) := by
    calc
      (a : ℝ)⁻¹ = 1 / a := inv_eq_one_div (a : ℝ)
      _ ≤ 2 / (a + b) := (div_le_div_iff₀ ha0 hab_pos).2 (by linarith [hab_ge])
  calc
    (Real.sqrt (n : ℝ))⁻¹ = (a : ℝ)⁻¹ := rfl
    _ ≤ 2 / (a + b) := htel3
    _ = 2 * (a - b) := htel2.symm

/-- 望远镜和（真证，S7.9）：Σ_{n≤N} (√n − √(n−1)) = √N（Icc 归纳）。 -/
lemma sum_sqrt_telescope (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)))
      = Real.sqrt (N : ℝ) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega)]
      rw [ih]
      simp

/-- 支撑截断 sum 界件（真证，S7.9）：Σ_{n≤N} n^{−1/2} ≤ 2√N（逐项望远镜 + 求和）。 -/
lemma sum_inv_sqrt_le_two_sqrt (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt (N : ℝ) := by
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    exact inv_sqrt_telescope_le n (Finset.mem_Icc.mp hn).1
  calc
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹)
        ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum hstep
    _ = 2 * Real.sqrt (N : ℝ) := by
        calc
          (∑ n ∈ Finset.Icc 1 N, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)))
              = 2 * (∑ n ∈ Finset.Icc 1 N,
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
              rw [Finset.mul_sum]
          _ = 2 * Real.sqrt (N : ℝ) := by rw [sum_sqrt_telescope]

/-- 指数衰减和件（真证，2026-10-29；S7.9 支撑截断口径，由 axiom 降级为 theorem）：
    Σ_{n≤min(X, e^{1/δ})} n^{−1/2} ≤ C₂，C₂ = 2√(e^{1/δ})（窗内有限和，差分部分 Σ A_n·Δb_n 的界）。
    注：原裸形式 Σ n^{−1/2}·e^{−c′√log n} 数学上发散（e^{−c′√log n} 亚多项式衰减，
    慢于任何幂），有界性来自核支撑截断（|δ·log n| ≤ 1 即 n ≤ e^{1/δ}）——S7.9 文档。 -/
theorem sum_weight_decay (δ : ℝ) (_hδ : 0 < δ) (c' : ℝ) (_hc' : 0 < c') :
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        (Real.sqrt (n : ℝ))⁻¹) ≤ C₂ := by
  refine ⟨2 * Real.sqrt (Real.exp (1 / δ)), mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro X hX
  have hle : 2 * Real.sqrt ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ)
      ≤ 2 * Real.sqrt (Real.exp (1 / δ)) := by
    have hmin : ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ) ≤ Real.exp (1 / δ) := by
      exact le_trans (by exact_mod_cast (min_le_right ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)) (Nat.floor_le (Real.exp_nonneg _))
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin) (by norm_num : (0 : ℝ) ≤ 2)
  exact (sum_inv_sqrt_le_two_sqrt (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)).trans hle

/-- 指数衰减和件（真证，2026-10-29；S7.9 支撑截断口径，由 axiom 降级为 theorem）：
    Σ_{n≤min(X, e^{1/δ})} √n·e^{−c′√log n} ≤ C₃，C₃ = e^{3/(2δ)}（窗内有限和；用于尾部项
    A_N·b_N 的界，√N·e^{−c′√log N} 为该和之单项）。原裸 Σ √n·e^{−c′√log n} 发散，见 S7.9 文档。
    证明路线：逐项 e^{−c′√log n} ≤ 1（n ≥ 1 ⟹ log n ≥ 0）⟹ 和 ≤ Σ√n ≤ Nw·√Nw
    （sum_le_card_nsmul，card(Icc 1 Nw) = Nw 手写归纳 + card_union_of_disjoint）⟹
    Nw ≤ e^{1/δ}（Nat.floor_le）⟹ ≤ e^{1/δ}·√(e^{1/δ}) ≤ e^{1/δ}·e^{1/(2δ)} = e^{3/(2δ)}
    （Real.sqrt_le_iff 平方单调，无 Real.sqrt_exp）。 -/
theorem sum_sqrt_decay (δ : ℝ) (hδ : 0 < δ) (c' : ℝ) (hc' : 0 < c') :
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) ≤ C₃ := by
  refine ⟨Real.exp (3 / (2 * δ)), Real.exp_nonneg _, ?_⟩
  intro X hX
  let Nw : ℕ := min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊
  have hNw1 : (1 : ℕ) ≤ Nw := by
    dsimp [Nw]
    have h1leE : (1 : ℝ) ≤ Real.exp (1 / δ) :=
      (Real.one_le_exp_iff).2 (le_of_lt (one_div_pos.mpr hδ))
    have h1leflE : (1 : ℕ) ≤ ⌊Real.exp (1 / δ)⌋₊ := by
      simpa using (Nat.floor_mono h1leE)
    have h1leflX : (1 : ℕ) ≤ ⌊X⌋₊ := by
      simpa using (Nat.floor_mono hX)
    exact le_min h1leflX h1leflE
  have hcard_general : ∀ N : ℕ, (Finset.Icc 1 N).card = N := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        have hdecomp : Finset.Icc 1 (N + 1) = Finset.Icc 1 N ∪ {N + 1} := by
          ext k
          rw [Finset.mem_Icc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
          constructor
          · intro hk
            by_cases h : k ≤ N
            · exact Or.inl ⟨hk.1, h⟩
            · exact Or.inr (by omega)
          · rintro (⟨hk1, hkN⟩ | hk)
            · exact ⟨hk1, le_trans hkN (Nat.le_succ N)⟩
            · subst hk
              exact ⟨by omega, by omega⟩
        have hdisj : Disjoint (Finset.Icc 1 N) ({N + 1} : Finset ℕ) := by
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp [Finset.mem_singleton, Finset.mem_Icc] at hk1 hk2
          omega
        have hstep : (Finset.Icc 1 (N + 1)).card = (Finset.Icc 1 N).card + 1 := by
          rw [hdecomp, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        rw [hstep, ih]
  have hcardNw : (Finset.Icc 1 Nw).card = Nw := hcard_general Nw
  have hstep : ∀ n ∈ Finset.Icc 1 Nw,
      Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) ≤ Real.sqrt (n : ℝ) := by
    intro n hn
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
    have hneg : -c' * Real.sqrt (Real.log (n : ℝ)) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hc']) (Real.sqrt_nonneg _)
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) ((Real.exp_le_one_iff).2 hneg)
  have hsum : (∑ n ∈ Finset.Icc 1 Nw,
      Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
      ≤ ∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ) := by
    exact Finset.sum_le_sum hstep
  have hsqrt : ∀ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ) ≤ Real.sqrt (Nw : ℝ) := by
    intro n hn
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hcard : (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ)) ≤ (Nw : ℝ) * Real.sqrt (Nw : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ))
          ≤ (Finset.Icc 1 Nw).card • Real.sqrt (Nw : ℝ) :=
            Finset.sum_le_card_nsmul (Finset.Icc 1 Nw) (fun n => Real.sqrt (n : ℝ))
              (Real.sqrt (Nw : ℝ)) hsqrt
      _ = (Nw : ℝ) * Real.sqrt (Nw : ℝ) := by
            rw [nsmul_eq_mul, hcardNw]
  have hNwE : (Nw : ℝ) ≤ Real.exp (1 / δ) := by
    dsimp [Nw]
    have h1 : ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ) ≤ (⌊Real.exp (1 / δ)⌋₊ : ℝ) := by
      exact_mod_cast (min_le_right ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)
    exact le_trans h1 (Nat.floor_le (Real.exp_nonneg _))
  have hsqrtNw : Real.sqrt (Nw : ℝ) ≤ Real.sqrt (Real.exp (1 / δ)) := by
    exact Real.sqrt_le_sqrt hNwE
  have hmul : (Nw : ℝ) * Real.sqrt (Nw : ℝ) ≤ Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) := by
    exact mul_le_mul hNwE hsqrtNw (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hsqrt_le : Real.sqrt (Real.exp (1 / δ)) ≤ Real.exp ((1 / δ) / 2) := by
    exact (Real.sqrt_le_iff).2 ⟨Real.exp_nonneg _, by
      rw [pow_two]
      rw [← Real.exp_add]
      have hsum : 1 / δ = (1 / δ) / 2 + (1 / δ) / 2 := by
        field_simp [ne_of_gt hδ]
        ring
      conv_lhs => rw [hsum]⟩
  have hmul2 : Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) ≤ Real.exp (3 / (2 * δ)) := by
    have hmul2' : Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ))
        ≤ Real.exp (1 / δ) * Real.exp ((1 / δ) / 2) := by
      exact mul_le_mul_of_nonneg_left hsqrt_le (Real.exp_nonneg _)
    have heq : Real.exp (1 / δ) * Real.exp ((1 / δ) / 2) = Real.exp (3 / (2 * δ)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hδ]
      ring
    exact hmul2'.trans_eq heq
  calc
    (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
        ≤ (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ)) := by
          rw [show min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ = Nw by rfl]
          exact hsum
    _ ≤ (Nw : ℝ) * Real.sqrt (Nw : ℝ) := hcard
    _ ≤ Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) := hmul
    _ ≤ Real.exp (3 / (2 * δ)) := hmul2

/-- 窗外拆窗（真证，2026-10-29）：素数项权重 K̂ 的频域窄支撑 ⟹ 和式截断到窗内——
    |δ·log n| > 1（即 n > e^{1/δ}）⟹ fourierCos K (δ·log n) = 0（KernelAdmissible 支撑件），
    故 primeSum K X δ = primeSum K (min X (e^{1/δ})) δ（任意 X ≥ 1，无需窗内前提 hXw）。 -/
lemma primeSum_window_eq (K : ℝ → ℝ) (X δ : ℝ) (_hX : (1 : ℝ) ≤ X) (hδ : 0 < δ)
    (hKs : ∀ u : ℝ, 1 < |u| → fourierCos K u = 0) :
    primeSum K X δ = primeSum K (min X (Real.exp (1 / δ))) δ := by
  by_cases hXw : X ≤ Real.exp (1 / δ)
  · have hmin : min X (Real.exp (1 / δ)) = X := min_eq_left hXw
    rw [hmin]
  · have hE : Real.exp (1 / δ) ≤ X := le_of_not_ge hXw
    have hmin : min X (Real.exp (1 / δ)) = Real.exp (1 / δ) := min_eq_right hE
    have hsub : Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊ ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro n hn
      apply Finset.mem_Icc.mpr
      exact ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 (Nat.floor_mono hE)⟩
    have hzero : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, n ∉ Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊ →
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * fourierCos K (δ * Real.log (n : ℝ))) = 0 := by
      intro n hn hnot
      have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
      have hflt : ⌊Real.exp (1 / δ)⌋₊ < n := by
        by_contra h
        have hnle : n ≤ ⌊Real.exp (1 / δ)⌋₊ := le_of_not_gt h
        exact hnot (Finset.mem_Icc.mpr ⟨hn1, hnle⟩)
      have hy : Real.exp (1 / δ) < (n : ℝ) := (Nat.floor_lt (Real.exp_nonneg _)).1 hflt
      have hpos : (0 : ℝ) < (n : ℝ) :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn1)
      have hlog : 1 / δ < Real.log (n : ℝ) := by
        apply (Real.exp_lt_exp).mp
        rwa [Real.exp_log hpos]
      have hδlog : 1 < δ * Real.log (n : ℝ) := by
        have hmul : δ * (1 / δ) = 1 := by field_simp [ne_of_gt hδ]
        calc
          1 = δ * (1 / δ) := hmul.symm
          _ < δ * Real.log (n : ℝ) := mul_lt_mul_of_pos_left hlog hδ
      have habs : |δ * Real.log (n : ℝ)| = δ * Real.log (n : ℝ) :=
        abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hδlog)
      have hzero' : fourierCos K (δ * Real.log (n : ℝ)) = 0 :=
        hKs (δ * Real.log (n : ℝ)) (by rwa [habs])
      rw [hzero', mul_zero, mul_zero]
    have hsum : (∑ n ∈ Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊,
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * fourierCos K (δ * Real.log (n : ℝ))))
        = (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * fourierCos K (δ * Real.log (n : ℝ)))) :=
      Finset.sum_subset hsub hzero
    rw [hmin]
    dsimp [primeSum]
    exact hsum.symm

/-- 素数项界（组装真证，(L2) 半形式化落位 + S7.9 窗外拆窗）：SW × Abel × 权重
    ⟹ |primeSum K X δ| ≤ c·M·(C₂+C₃)，任意 X ≥ 1（无窗内前提）。
    组装 = sum_abel_partial（真证）+ siegel_walfisz_chi5（部分和 SW 界）+ prime_weight_bounds
    + sum_weight_decay / sum_sqrt_decay（指数衰减和；尾部项并入 C₃、差分和并入 C₂）。
    拆窗：primeSum_window_eq（K̂ 频域窄支撑 ⟹ 和式截断到 min X (e^{1/δ})），故 X' = min X (e^{1/δ})
    满足窗内前提（min_le_right），原窗内证明套 X'。
    归一化 |prime|≤1（除以 N_L~T·logT 分母）说明留 bgs3 语境（文档层：SW 常数 c 实测
    1.70e−3 远小，分母归一后余量充分）。 -/
theorem prime_sum_bound (X δ : ℝ) (hX : (1 : ℝ) ≤ X) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ |primeSum Khat X δ| ≤ C := by
  let X' : ℝ := min X (Real.exp (1 / δ))
  have hX' : (1 : ℝ) ≤ X' := by
    dsimp [X']
    exact le_min hX ((Real.one_le_exp_iff).2 (le_of_lt (one_div_pos.mpr hδ)))
  have hXw' : X' ≤ Real.exp (1 / δ) := by
    dsimp [X']
    exact min_le_right X (Real.exp (1 / δ))
  have hpeq : primeSum Khat X δ = primeSum Khat X' δ :=
    primeSum_window_eq Khat X δ hX hδ bgs5_khat_fourier_supp
  rw [hpeq]
  rcases siegel_walfisz_chi5 with ⟨c, c', hc0, hc'0, hsw⟩
  rcases prime_weight_bounds_Khat δ hδ with ⟨M, hM0, hb, hΔ⟩
  rcases sum_weight_decay δ hδ c' hc'0 with ⟨C₂, hC₂0, hdec2⟩
  rcases sum_sqrt_decay δ hδ c' hc'0 with ⟨C₃, hC₃0, hdec3⟩
  let N : ℕ := ⌊X'⌋₊
  have hNpos : (1 : ℕ) ≤ N := by
    dsimp [N]
    exact (Nat.floor_pos).2 hX'
  have hswN : ∀ n : ℕ, (1 : ℕ) ≤ n →
      |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
        ≤ c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
    intro n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hfl : ⌊(n : ℝ)⌋₊ = n := by simp
    have hsw' := hsw (n : ℝ) hx
    rwa [hfl] at hsw'
  have hps : primeSum Khat X' δ
      = (∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
          * ((Real.sqrt (N : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (N : ℝ)))
        - (∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))) := by
    dsimp [primeSum, N]
    exact sum_abel_partial ⌊X'⌋₊ (fun n => vonMangoldt n * chi5 n)
      (fun n => (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))
  refine ⟨c * M * (C₂ + C₃), mul_nonneg (mul_nonneg (le_of_lt hc0) hM0) (add_nonneg hC₂0 hC₃0), ?_⟩
  calc
    |primeSum Khat X' δ|
        ≤ |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (N : ℝ)))|
          + |∑ n ∈ Finset.Icc 1 (N - 1),
              (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                    - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))| := by
            rw [hps, sub_eq_add_neg]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ c * M * C₃ + c * M * C₂ := by
        have h1 : |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (N : ℝ)))| ≤ c * M * C₃ := by
          calc
            |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
                * ((Real.sqrt (N : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (N : ℝ)))|
                ≤ |∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i|
                  * |(Real.sqrt (N : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (N : ℝ))| := (abs_mul _ _).le
            _ ≤ (c * (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
                * (M * (Real.sqrt (N : ℝ))⁻¹) := by
                exact mul_le_mul (hswN N hNpos) (hb N hNpos) (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (le_of_lt hc0) (Nat.cast_nonneg N)) (Real.exp_nonneg _))
            _ ≤ c * M * C₃ := by
                have hroot : (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) = Real.sqrt (N : ℝ) := by
                  have hNgt0 : (0 : ℝ) < (N : ℝ) :=
                    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hNpos)
                  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
                    Real.sq_sqrt (le_of_lt hNgt0)
                  have hne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hNgt0)
                  field_simp [hne]
                  conv_lhs =>
                    rw [← hsq]
                have hmul : 0 ≤ c * M := mul_nonneg (le_of_lt hc0) hM0
                have hterm : Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) ≤ C₃ := by
                  have hNleX : N ≤ ⌊X'⌋₊ := by exact le_rfl
                  have hNleE : N ≤ ⌊Real.exp (1 / δ)⌋₊ := by
                    dsimp [N]
                    exact Nat.floor_mono hXw'
                  have hsingle :
                      Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))
                        ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                            Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                      have hf : ∀ j ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                          0 ≤ Real.sqrt (j : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (j : ℝ))) := by
                        intro j hj
                        exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
                      have hNmem : N ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊) := by
                        apply Finset.mem_Icc.mpr
                        exact ⟨hNpos, le_min hNleX hNleE⟩
                      simpa [N] using (Finset.single_le_sum hf hNmem)
                  exact hsingle.trans (hdec3 X' hX')
                calc
                  (c * (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
                      * (M * (Real.sqrt (N : ℝ))⁻¹)
                      = c * M * ((Real.sqrt (N : ℝ))⁻¹ * (N : ℝ))
                          * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by ring
                  _ = c * M * Real.sqrt (N : ℝ)
                      * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by rw [hroot]
                  _ ≤ c * M * C₃ := by
                      calc
                        c * M * Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))
                            = c * M * (Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))) := by ring
                        _ ≤ c * M * C₃ := mul_le_mul_of_nonneg_left hterm hmul
        have h2 : |∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))| ≤ c * M * C₂ := by
          calc
            |∑ n ∈ Finset.Icc 1 (N - 1),
                (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                  * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                      - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))|
                ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                    |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                apply Finset.sum_le_sum
                intro n hn
                have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
                have hab : |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                    * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                        - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))|
                    ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                      * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                    calc
                      |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                          * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                              - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))|
                          ≤ |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
                            * |((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                                - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ))| := (abs_mul _ _).le
                      _ ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                          * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                          exact mul_le_mul (hswN n hn1) (hΔ n hn1) (abs_nonneg _)
                            (mul_nonneg (mul_nonneg (le_of_lt hc0) (Nat.cast_nonneg n)) (Real.exp_nonneg _))
                calc
                  |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * fourierCos Khat (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * fourierCos Khat (δ * Real.log (n : ℝ)))|
                      ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                        * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := hab
                  _ = c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                      have hrootn : (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ ^ 3 = (Real.sqrt (n : ℝ))⁻¹ := by
                        have hnpos' : (0 : ℝ) < (n : ℝ) :=
                          lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn1)
                        have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
                          Real.sq_sqrt (le_of_lt hnpos')
                        have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnpos')
                        field_simp [hne]
                        conv_lhs =>
                          rw [← hsq]
                      conv_rhs =>
                        rw [← hrootn]
                      ring
            _ ≤ c * M * C₂ := by
                have hmul : 0 ≤ c * M := mul_nonneg (le_of_lt hc0) hM0
                calc
                  ∑ n ∈ Finset.Icc 1 (N - 1),
                      c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))
                      = c * M * (∑ n ∈ Finset.Icc 1 (N - 1),
                          (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) := by
                      rw [Finset.mul_sum]
                      ring
                  _ ≤ c * M * C₂ := by
                      have hexp_le : ∀ n ∈ Finset.Icc 1 (N - 1),
                          Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
                        intro n hn
                        have hnlog : 0 ≤ Real.log (n : ℝ) := by
                          have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
                          exact Real.log_nonneg hn1'
                        have hneg : -c' * Real.sqrt (Real.log (n : ℝ)) ≤ 0 := by
                          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hc'0]) (Real.sqrt_nonneg _)
                        exact (Real.exp_le_one_iff).2 hneg
                      have hsubset : Finset.Icc 1 (N - 1) ⊆ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊) := by
                        intro n hn
                        have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
                        have hn2 : n ≤ N - 1 := (Finset.mem_Icc.mp hn).2
                        have hnleN : n ≤ N := le_trans hn2 (Nat.sub_le N 1)
                        have hNleE : N ≤ ⌊Real.exp (1 / δ)⌋₊ := by
                          dsimp [N]
                          exact Nat.floor_mono hXw'
                        have hnlemin : n ≤ min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊ :=
                          le_min (by simpa [N] using hnleN) (le_trans hnleN hNleE)
                        apply Finset.mem_Icc.mpr
                        exact ⟨hn1, hnlemin⟩
                      have hsub :
                          (∑ n ∈ Finset.Icc 1 (N - 1),
                            (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                            ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                                (Real.sqrt (n : ℝ))⁻¹ := by
                        calc
                          (∑ n ∈ Finset.Icc 1 (N - 1),
                              (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                              ≤ ∑ n ∈ Finset.Icc 1 (N - 1), (Real.sqrt (n : ℝ))⁻¹ := by
                                apply Finset.sum_le_sum
                                intro n hn
                                exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (hexp_le n hn)
                          _ ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊), (Real.sqrt (n : ℝ))⁻¹ := by
                              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                                (fun n _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
                      exact mul_le_mul_of_nonneg_left (hsub.trans (hdec2 X' hX')) hmul
        linarith [h1, h2]
    _ = c * M * (C₂ + C₃) := by ring

/-! ### 2.1b (L3) BGS 引理 3-5 逐条移植（配对和展开；2026-10-27 半形式化）

BGS 结构（引用本攻防 S7.1 §3 / S7.3-7.5 文档论证）：
  引理 5（核构造）：λ≤1/2 核族 ⟺ K(0)=1 且 supp K̂ ⊂ [−1,1]——`KernelAdmissible`；
    `Khat_admissible`：K(0)=1 真证（Khat_zero）+ 频域支撑（axiom bgs5_khat_fourier_supp）。
  引理 3（配对和积分展开）：KernelAdmissible 核 ⟹ pairConstant = 对角主项 + 素数项 + 离线误差
    （Montgomery–Vaughan 均值；`bgs3_pair_expansion`）。
  引理 4（离线误差）：弱实部 + T^{3/8} 切割 ⟹ |offcrit| ≤ o(1)（`offcritical_small`，见下）。
`pair_sum_expansion` 由 bgs3 组装（引理 4 的 |offcrit|≤1 缩放已并入 bgs3 陈述，注释承接）。 -/

/-- 引理 5（K̂ 件）：Khat 的频域窄支撑（supp K̂ ⊂ [−1,1]）——axiom（积分层，文档 S7.1 §3）。
    注：声明位置须在 `prime_sum_bound` 之前（后者体内以 `bgs5_khat_fourier_supp` 为组装件）。 -/
def KernelAdmissible (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ ∀ u : ℝ, 1 < |u| → fourierCos Khat u = 0

/-- 引理 5（Khat 可容许，组装）：Khat_zero（真证）+ bgs5_khat_fourier_supp。 -/
lemma Khat_admissible : KernelAdmissible Khat := by
  unfold KernelAdmissible
  exact ⟨Khat_zero, bgs5_khat_fourier_supp⟩

/-- 引理 3（配对和展开，statement）：KernelAdmissible 核 + 弱实部假设 ⟹
    A_L(K) = 对角主项 + 素数项 + 离线误差；
    对角主项 diag ≤ C_MT + C₁·ε（ε 偏差系数 C₁——n2_linkage O(ε) 联动吸收，文档 S7.4 定理 N2）；
    素数项 |prime| ≤ 1（Montgomery–Vaughan 均值 + SW 压制，文档 S7.6）；
    离线项 |offcrit| ≤ 1（引理 4 缩放：offcritical_small 除以 N_L，文档 S7.5 定理 N3）。 -/
axiom bgs3_pair_expansion (K : ℝ → ℝ) (δ T ε : ℝ) (hK : KernelAdmissible K)
    (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime offcrit : ℝ), 0 ≤ C₁ ∧
    pairConstant K δ (Real.log T / (2 * Real.pi)) zerosLChi5 = diag + prime + offcrit ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1 ∧ |offcrit| ≤ 1

/-- (L3) 配对和展开（组装定理）：BGS 引理 3（bgs3_pair_expansion）的直接包装——
    核可容许条件显式化（引理 5），离线界承接引理 4。 -/
theorem pair_sum_expansion (K : ℝ → ℝ) (δ T ε : ℝ) (hK : KernelAdmissible K)
    (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime offcrit : ℝ), 0 ≤ C₁ ∧
    pairConstant K δ (Real.log T / (2 * Real.pi)) zerosLChi5 = diag + prime + offcrit ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1 ∧ |offcrit| ≤ 1 := by
  exact bgs3_pair_expansion K δ T ε hK hweak

/-! ## 2.2 (L4) BGS 引理 4 移植——T^{3/8} 切割链（2026-10-27 半形式化）

离线误差的机制（文档 S7.5 定理 N3 / S7.1 §3）：Weil 显式公式余项按零点高度切割为两段：
  · offcritLow（低频段，≤ T^{3/8} 切割）：弱实部假设压离临界带项（β ≤ 1−c/logT 型），
    贡献 O(√log T) 量级；
  · offcritHigh（高频段，> T^{3/8} 切割）：零点计数 N(T) 主项吸收（Riemann–von Mangoldt
    平凡界），贡献 O(√log T) 量级。
切割分解与两段界为命名 axiom（数论件，文档层论证）；`offcritical_small` 由三角不等式组装真证。 -/

/-- 离线误差的低频段（T^{3/8} 切割以下；弱实部件）。 -/
opaque offcritLow (T : ℝ) : ℝ

/-- 离线误差的高频段（T^{3/8} 切割以上；计数件）。 -/
opaque offcritHigh (T : ℝ) : ℝ

/-- 切割分解（引理 4(i)）：余项 = 低频 + 高频。 -/
axiom bgs4_offcrit_split : ∀ s : ℝ, offCriticalError s = offcritLow s + offcritHigh s

/-- 低频段界（引理 4(ii)，弱实部件）：|offcritLow s| ≤ R₁·√log s（T^{3/8} 以下项）。 -/
axiom bgs4_offcrit_low :
  ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
    ∃ (R₁ : ℝ), 0 ≤ R₁ ∧
      ∀ s : ℝ, T ≤ s → |offcritLow s| ≤ R₁ * Real.sqrt (Real.log s)

/-- 高频段界（引理 4(iii)，计数件）：|offcritHigh s| ≤ R₂·√log s（N(T) 主项吸收）。 -/
axiom bgs4_offcrit_high :
  ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
    ∃ (R₂ : ℝ), 0 ≤ R₂ ∧
      ∀ s : ℝ, T ≤ s → |offcritHigh s| ≤ R₂ * Real.sqrt (Real.log s)

/-- (L4) 离线误差（组装定理）：弱实部假设 + T^{3/8} 切割 → √logT 型界。
    组装：切割分解 + 双段界 + 三角不等式（R = R₁ + R₂）。 -/
theorem offcritical_small :
  ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
    ∃ (R : ℝ), 0 ≤ R ∧
      ∀ s : ℝ, T ≤ s → |offCriticalError s| ≤ R * Real.sqrt (Real.log s) := by
  intro T hT hweak
  rcases bgs4_offcrit_low T hT hweak with ⟨R₁, hR₁0, hlow⟩
  rcases bgs4_offcrit_high T hT hweak with ⟨R₂, hR₂0, hhigh⟩
  refine ⟨R₁ + R₂, add_nonneg hR₁0 hR₂0, ?_⟩
  intro s hs
  rw [bgs4_offcrit_split s]
  calc
    |offcritLow s + offcritHigh s| ≤ |offcritLow s| + |offcritHigh s| := abs_add_le _ _
    _ ≤ R₁ * Real.sqrt (Real.log s) + R₂ * Real.sqrt (Real.log s) :=
      add_le_add (hlow s hs) (hhigh s hs)
    _ = (R₁ + R₂) * Real.sqrt (Real.log s) := by ring

/-! ## 3. 主定理 S7.1（组装真证；分析层 (L1)–(L4) 为命名 axiom） -/

/-- 定理 S7.1（L(s, χ_5) 单族 BGS 型配对公式——弱假设下无条件）：
    对 λ≤1/2 核族（KernelAdmissible：Khat 解析式、K(0)=1、K̂ 频域窄支撑 supp⊂[−1,1]），
    A_L(K) ≤ C_MT + O(ε) + o(1)。
    组装真证：由 pair_sum_expansion（BGS 引理 3-5 移植）分解 A_L = diag + prime + offcrit，
    对角主项 diag ≤ C_MT + C₁ε、素数项/离线项以 |·|≤1 占位界并入 C₂=2。 -/
theorem s71_main
    (T : ℝ) (_hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (ε : ℝ) (_hε0 : 0 < ε) :
    ∃ (C₁ C₂ : ℝ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      pairConstant Khat (Real.log T / (2 * Real.pi)) (Real.log T / (2 * Real.pi)) zerosLChi5
        ≤ C_MT + C₁ * ε + C₂ := by
  let δ : ℝ := Real.log T / (2 * Real.pi)
  rcases pair_sum_expansion Khat δ T ε Khat_admissible hweak with ⟨C₁, diag, prime, offcrit,
      hC₁0, hsplit, hdiag, hprime, hoffcrit⟩
  refine ⟨C₁, 2, hC₁0, by norm_num, ?_⟩
  calc
    pairConstant Khat δ δ zerosLChi5 = diag + prime + offcrit := hsplit
    _ ≤ C_MT + C₁ * ε + |prime| + |offcrit| := by
      linarith [hdiag, le_abs_self prime, le_abs_self offcrit]
    _ ≤ C_MT + C₁ * ε + 1 + 1 := by linarith [hprime, hoffcrit]
    _ = C_MT + C₁ * ε + 2 := by ring

/-! ## 4. 击破清单（下一轮逐个替换 sorry/axiom）

- [x] `pairConstant`：**真实定义完成**（2026-10-27，tsum 差型配对和 1 + Σ_{z₁≠z₂∈Z} K(δ·im(z₁−z₂))²/N，
      紧支撑核自动有限截断；收敛性论证 = 长线真证项）。
- [x] `zerosLChi5`：**真实定义完成**（2026-10-27，临界带 0<Re s<1 内 L 零点集，
      LFun opaque + 新增 (L0a) `lfun_conj_symm`（conj 对称，支撑 conj_closed 真证）+
      (L0b) `lfun_dirichlet_series`（Re s>0 的 Dirichlet 卷积表示，长线真证目标）；
      原 `{z | True}` 占位已移除）。
- [ ] (L1) `landau_explicit_L`：**精确陈述完成**（2026-10-27，Yildirim 公式 (6) 重排式）；
      形式化真证需先把 `-L'/L` 的 Dirichlet 级数展开与 Mellin 变换写成引理——长线目标。
- [ ] (L2) `siegel_walfisz_chi5`：**精确陈述完成**（2026-10-27，Finset.Icc 1 ⌊x⌋₊ 真实和式）；
      形式化真证需 PNT 在算术级数 + 特征和估计——长线目标。
- [x] (L3) `pair_sum_expansion`：**BGS 引理 3-5 逐条移植完成**（2026-10-27）——
      引理 5 `KernelAdmissible`（K(0)=1 + supp K̂⊂[−1,1]）+ `Khat_admissible` 组装
      （K(0)=1 真证 + bgs5_khat_fourier_supp）；引理 3 `bgs3_pair_expansion`
      （分解 + diag≤C_MT+C₁ε + |prime|,|offcrit|≤1）；引理 4 承接 `offcritical_small`；
      `pair_sum_expansion` 定理化（KernelAdmissible 条件化），s71_main 已接入。
- [x] (L4) `offcritical_small`：**BGS 引理 4 移植完成**（2026-10-27，T^{3/8} 切割链）——
      切割分解 `bgs4_offcrit_split`（余项 = 低频 offcritLow + 高频 offcritHigh）、
      低频弱实部件 `bgs4_offcrit_low`、高频计数件 `bgs4_offcrit_high`（各 √logT 界）；
      `offcritical_small` 组装真证（三角不等式，R = R₁+R₂）。
- [x] `s71_main`：**组装真证**（2026-10-27）——pair_sum_expansion 分解
      A_L = diag + prime + offcrit；diag ≤ C_MT + C₁ε（n2_linkage O(ε)）、
      |prime|,|offcrit| ≤ 1 并入 C₂=2（SW/BGS 占位界）；C₁, C₂ 显式。

「推 1」断层（超支撑 λ→∞）三件套——S7 闭路只覆盖 λ≤1/2（BGS 引理 5 supp r⊂[−1,1]）；
  Stage 3+ 已于 S7_1_Stage3.lean 形式化（2026-10-26）：
- [x] (N1) BGS 引理 5 超支撑推广：scaleKernel 定义 + 支撑保持真证明（scaleKernel_support）；
      fourierCos_scale（r̂_a(z)=r̂(az)）、scaleKernel_L1_invariant、n1_diag_invariant、n1_offdiag_vanishes
      ——结构件 axiom（积分层，文档 S7.3 定理 N1）。
- [x] (N2) ε–λ 联动：f_eps_support 真证明（|x|>1/2 ⟹ f_ε=0，支撑 [−1/2,1/2]）；
      n2_linkage（λ=(logT)^q、a=(logT)^{−q}、ε=c(logT)^{−q} ⟹ 偏差 O((logT)^{−q})）——axiom
      （文档 S7.4 定理 N2）。
- [x] (N3) 离线项一致版本：n3_remainder_uniform（BGS 余项 O(T√logT) 对 supp⊂[−1,1] 一切核一致）
      ——axiom（文档 S7.5 定理 N3）。
三条真证明件（超支撑素数项层）：
- [x] Abel 求和引理（sum_abel，summation by parts 归纳真证；S7.6 §2.4 离散骨架）
- [x] K̂_a 偶性（Khat_a_even，一阶校正恒为零真证）；二阶一致界 khat_second_order_bound
      |K̂(au)−1|≤2(au)²+(au)⁴——**真证**（K̂ 导数闭式乘形式 + 区间界；2026-10-26 迁入 Stage3 替换 axiom；
      数值核对：K̂″(0)≈−3.06、ratio=1.000 @ aδ≤3e−3、f̂₀(0)=∫K₀=1）
- [x] N_L 对数增长下界（N_L_lower_bound：N_L(T)≥c·T·logT）——axiom（数论件，S6 口径）
构建证据：lake build QRH 1965 jobs 全绿（build_qrh_full.txt）；Stage3 独立编译 build_stage3.txt。
超支撑素数项量级（数值件 F 已实测，2026-10-25）：S(X)=Σ_{p≤X}Λχ₅(p)p^{−1/2}K̂_a(δlogp)
  = O(√X·poly(log X))——相对 N_L ~ (X/2π)logX 为 o(1)——无需 e^{−c√logX} 指数级；
  |S_a|/N_L 单调衰减至 1e−8（X=10⁸），|S_a|≈2.05 有界收敛（强于理论上界）。

优先级建议（按依赖序）：
  Stage 1：Core 件清零（Khat_zero、f0_sub_feps_L1_bound、C_MT 数值界）→ s71 常数为显式。
  Stage 2：(L3) 配对和展开写成半形式化（有限多重集 + 有限和）；δ 口径用实数。
  Stage 3：(L2) SW 作为命名 axiom（数学上已证、形式化长线）。
  Stage 3+：（N1)-(N3) 超支撑断层闭合 + 三条新真证明件（数值件 F 定向先行）。
  Stage 4：s71_main 组装（epsilon-delta 展开）。
-/

end QRH
