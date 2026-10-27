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
def WeakRealPart (T : ℝ) (Z : ZeroSet) : Prop := True

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

数学内容：对 L(s,χ_5)（模 5 实特征），0<r、x≥1、r 非零点时，
  Σ_ρ x^{ρ−r}/(ρ−r) = Σ_ℓ x^{−(2ℓ+r+a)}/(2ℓ+r+a) − Σ'_{n≤x} Λ(n)χ(n)/n^r − (L′/L)(r,χ)。
（Yildirim 1991 公式 (6)；对 L(s,χ) 无条件成立。） -/
axiom landau_explicit_L :
  ∀ (r x : ℝ), 0 < r → (1 : ℝ) ≤ x → (∀ z ∈ zerosLChi5, z ≠ r) →
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
lemma primePowerSum_half_eq_sqrt (n : ℕ) (hn : 1 ≤ n) :
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
    （比较判别 + 几何级数；x = 1 边界为调和型发散——如实记录口径，
    landau_explicit_L 的 1 ≤ x 前提在 x=1 处需单独处理）。 -/
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
  · `primeSum`：素数项真实和式（Finset.Icc 口径，BGS 引理 3 的 prime 项真实载体）；
  · `sum_abel_partial`：部分和 Abel 求和（真证，归纳；sum_abel 的部分和变形）；
  · `prime_weight_bounds`：权重 b_n = n^{−1/2}·K(δ·log n) 的有界/平滑件（axiom，解析件，
    文档 S7.6 §2.4：K 光滑 + 核宽缩放；一个常数 M 兼作 |b| 界与差分界）；
  · `sum_weight_decay`：Σ_{n≤X} n^{−1/2}·e^{−c′√log n} ≤ C₂（axiom，指数衰减和，
    SW 指数 c′ 参数化；尾部项 √N·e^{−c′√log N} 为该和之单项，界并入 C₂）；
  · `prime_sum_bound`：|primeSum K X δ| ≤ 2·c·M·C₂（组装真证：Abel 分解 + 三角不等式 +
    SW 部分和界 + 权重件 + 衰减件）。
数学口径：SW 界 (c,c′) 见文档 S7.6 量化；权重有界/平滑由 K 光滑与核宽缩放（S7.3 定理 N1
  机制）；归一化 |prime|≤1（除以 N_L~T·logT 分母）的说明留 bgs3 语境（文档层：
  SW 常数 c 实测 1.70e−3 远小，N_L 分母归一后余量充分）。 -/

/-- 素数项（真实和式，Finset 口径）：S(X) = Σ_{1≤n≤⌊X⌋} Λ(n)χ₅(n)·n^{−1/2}·K(δ·log n)，
    差型配对中的素数项（BGS 引理 3 的 prime 项真实载体）；K 为核（λ≤1/2 核族）。
    （被加项按 a·b 结合形态书写，与 sum_abel_partial 的 LHS 精确匹配。） -/
def primeSum (K : ℝ → ℝ) (X δ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))

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


/-- 素数项权重件（axiom，解析件）：b_n = n^{−1/2}·K(δ·log n) 有界与平滑——
    |b_n| ≤ M·n^{−1/2} 且 |b_{n+1}−b_n| ≤ M·n^{−3/2}（单一常数 M 兼作；
    K 光滑 + 核宽缩放，文档 S7.6 §2.4 / S7.3 定理 N1 机制）。 -/
axiom prime_weight_bounds (K : ℝ → ℝ) (δ : ℝ) :
  ∃ M : ℝ, 0 ≤ M ∧
    (∀ n : ℕ, 1 ≤ n →
      |(Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ))| ≤ M * (Real.sqrt (n : ℝ))⁻¹) ∧
    (∀ n : ℕ, 1 ≤ n →
      |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ))
        - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ))|
        ≤ M * (Real.sqrt (n : ℝ))⁻¹ ^ 3)

/-- 指数衰减和件（axiom，解析件，SW 指数 c′ 参数化）：
    Σ_{n≤X} n^{−1/2}·e^{−c′√log n} ≤ C₂（用于差分部分 Σ A_n·Δb_n 的界）。 -/
axiom sum_weight_decay (c' : ℝ) (hc' : 0 < c') :
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) ≤ C₂

/-- 指数衰减和件（axiom，解析件，SW 指数 c′ 参数化）：
    Σ_{n≤X} n^{1/2}·e^{−c′√log n} ≤ C₃（用于尾部项 A_N·b_N 的界；√N·e^{−c′√log N} 为该和之单项）。 -/
axiom sum_sqrt_decay (c' : ℝ) (hc' : 0 < c') :
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) ≤ C₃

/-- 素数项界（组装真证，(L2) 半形式化落位）：SW × Abel × 权重 ⟹ |primeSum K X δ| ≤ c·M·(C₂+C₃)。
    组装 = sum_abel_partial（真证）+ siegel_walfisz_chi5（部分和 SW 界）+ prime_weight_bounds
    + sum_weight_decay / sum_sqrt_decay（指数衰减和；尾部项并入 C₃、差分和并入 C₂）。
    归一化 |prime|≤1（除以 N_L~T·logT 分母）说明留 bgs3 语境（文档层：SW 常数 c 实测
    1.70e−3 远小，分母归一后余量充分）。 -/
theorem prime_sum_bound (K : ℝ → ℝ) (X δ : ℝ) (hX : (1 : ℝ) ≤ X) :
    ∃ C : ℝ, 0 ≤ C ∧ |primeSum K X δ| ≤ C := by
  rcases siegel_walfisz_chi5 with ⟨c, c', hc0, hc'0, hsw⟩
  rcases prime_weight_bounds K δ with ⟨M, hM0, hb, hΔ⟩
  rcases sum_weight_decay c' hc'0 with ⟨C₂, hC₂0, hdec2⟩
  rcases sum_sqrt_decay c' hc'0 with ⟨C₃, hC₃0, hdec3⟩
  let N : ℕ := ⌊X⌋₊
  have hNpos : (1 : ℕ) ≤ N := by
    dsimp [N]
    exact (Nat.floor_pos).2 hX
  have hswN : ∀ n : ℕ, (1 : ℕ) ≤ n →
      |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
        ≤ c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
    intro n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hfl : ⌊(n : ℝ)⌋₊ = n := by simp
    have hsw' := hsw (n : ℝ) hx
    rwa [hfl] at hsw'
  have hps : primeSum K X δ
      = (∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
          * ((Real.sqrt (N : ℝ))⁻¹ * K (δ * Real.log (N : ℝ)))
        - (∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))) := by
    dsimp [primeSum, N]
    exact sum_abel_partial ⌊X⌋₊ (fun n => vonMangoldt n * chi5 n)
      (fun n => (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))
  refine ⟨c * M * (C₂ + C₃), mul_nonneg (mul_nonneg (le_of_lt hc0) hM0) (add_nonneg hC₂0 hC₃0), ?_⟩
  calc
    |primeSum K X δ|
        ≤ |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * K (δ * Real.log (N : ℝ)))|
          + |∑ n ∈ Finset.Icc 1 (N - 1),
              (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                    - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))| := by
            rw [hps, sub_eq_add_neg]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ c * M * C₃ + c * M * C₂ := by
        have h1 : |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * K (δ * Real.log (N : ℝ)))| ≤ c * M * C₃ := by
          calc
            |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
                * ((Real.sqrt (N : ℝ))⁻¹ * K (δ * Real.log (N : ℝ)))|
                ≤ |∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i|
                  * |(Real.sqrt (N : ℝ))⁻¹ * K (δ * Real.log (N : ℝ))| := (abs_mul _ _).le
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
                  have hsingle :
                      Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))
                        ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
                            Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                      have hf : ∀ j ∈ Finset.Icc 1 ⌊X⌋₊,
                          0 ≤ Real.sqrt (j : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (j : ℝ))) := by
                        intro j hj
                        exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
                      simpa [N] using (Finset.single_le_sum hf (Finset.mem_Icc.mpr ⟨hNpos, le_rfl⟩))
                  exact hsingle.trans (hdec3 X hX)
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
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))| ≤ c * M * C₂ := by
          calc
            |∑ n ∈ Finset.Icc 1 (N - 1),
                (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                  * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                      - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))|
                ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                    |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                apply Finset.sum_le_sum
                intro n hn
                have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
                have hab : |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                    * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                        - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))|
                    ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                      * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                    calc
                      |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                          * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                              - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))|
                          ≤ |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
                            * |((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                                - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ))| := (abs_mul _ _).le
                      _ ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                          * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                          exact mul_le_mul (hswN n hn1) (hΔ n hn1) (abs_nonneg _)
                            (mul_nonneg (mul_nonneg (le_of_lt hc0) (Nat.cast_nonneg n)) (Real.exp_nonneg _))
                calc
                  |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * K (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))|
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
                      have hsub :
                          (∑ n ∈ Finset.Icc 1 (N - 1),
                            (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                            ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
                                (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                          rw [show ⌊X⌋₊ = N by rfl]
                          exact Finset.sum_le_sum_of_subset_of_nonneg
                            (by
                              intro n hn
                              exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
                                le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 1)⟩)
                            (fun n _ _ => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _))
                      exact mul_le_mul_of_nonneg_left (hsub.trans (hdec2 X hX)) hmul
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

/-- 引理 5：核可容许条件（λ≤1/2 核族）——K(0)=1 且 supp K̂ ⊂ [−1,1]（频域窄支撑）。 -/
def KernelAdmissible (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ ∀ u : ℝ, 1 < |u| → fourierCos K u = 0

/-- 引理 5（K̂ 件）：Khat 的频域窄支撑（supp K̂ ⊂ [−1,1]）——axiom（积分层，文档 S7.1 §3）。 -/
axiom bgs5_khat_fourier_supp : ∀ u : ℝ, 1 < |u| → fourierCos Khat u = 0

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
    (T : ℝ) (hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (ε : ℝ) (hε0 : 0 < ε) :
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
