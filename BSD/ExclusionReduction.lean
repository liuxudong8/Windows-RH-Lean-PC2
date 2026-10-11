import BSD.Main
import BSD.Stage2.RankTwoExclusion
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# 归约定理：秩 1 排除层的 Lean 形式化（BSD.ExclusionReduction）

对应分析（2026-10-11 讨论）：秩 1 反向的排除层（ord ≤ 1，排除 ord ≥ 3）
在 K = ℚ(√5) 上没有新自由度——基变换分解把它逐字归约回 ℚ 侧两个
BSD 反向特例。

## 数学结构（K = ℚ(√5)，E = 37a1）

Artin 分解 L(E/K, s) = L(E, s)·L(E⁵, s)（LSeries5 = 37a1 的 5-二次扭）：

    ord₁ L(E/K) = ord₁ L(E) + ord₁ L(E⁵)      （BSD.Stage2.zeroOrder_additivity）

排除层 = ord ≤ 1。给定消失层（ord ≥ 1，分量 Kolyvagin 逆否，定理级）后，
排除层 ⟺ L′(E/K, 1) ≠ 0；在 (1,0) 型（rank E(ℚ) = 1，rank E⁵(ℚ) = 0）下
乘积求导给出：

    L′(E/K, 1) = L′(E, 1)·L(E⁵, 1)     （因 L(E, 1) = 0）

故排除层归约到两个 ℚ 侧反向特例：

    (i)  L′(E, 1) ≠ 0   （秩 1 BSD 反向，ℚ 侧——37a1 逐曲线闭证：
         BSD.LPrime.lprime1_pos 为真定理，反射公式一阶导区间算术）
    (ii) L(E⁵, 1) ≠ 0   （秩 0 BSD 反向，ℚ 侧——37a1 的 5-扭逐曲线闭证：
         BSD.LSeries5.L_E5_one_ne_zero 为真定理，级数区间算术）

ord 级拼合（本模块 §3）：

    ord₁ L(E/K) = ord₁ L(E) + ord₁ L(E⁵) = 1 + 0 = 1

这就是秩 1 文档 4.4 中"排除层（ord ≤ 1，排除 ord ≥ 3）理论级仍开放，
是秩 1 反向剩余的核心缺口"的精确收紧：排除层的理论级障碍 = 两个
ℚ 侧 BSD 反向特例；对 37a1 两者都已逐曲线闭证，故 37a1/K 的排除层
在本框架内闭环（K 侧只依赖 Artin 加性，无额外自由度）。

## 模块分层

1. **通用 Leibniz 归约（真定理层，纯微积分）**：乘积求导的解析内容
   （"Artin 分解 + 乘积求导"此前仅是 Main.lean 注释，此处形式化）。
2. **对象层（37a1，(1,0) 型）**：`BSD.LK_prime ≠ 0` 显式分解为
   两个 ℚ 侧非零性的乘积。
3. **ord 级归约（挂账 axiom + 真定理拼合）**：
   - `zeroOrderE_eq_one_of_lprime_ne_zero`（ℚ 侧秩 1 反向桥梁，挂账 axiom，
     前件 lprime1_pos 为真定理）；
   - `exclusion_layer_reduction`：analyticZeroOrder = 1（加性 + 两判据）；
   - `analytic_rank_K_eq_zero_order`（Main 解析秩 = Stage2 零点阶，统一 axiom）；
   - `analytic_rank_K_eq_one_via_exclusion_reduction`：解析秩(E/K) = 1
     （第二条独立路线，不经 Main 的 LK_prime 桥梁 axiom）。

闭包（#print axioms 实测）：exclusion_layer_reduction 的假设面 =
Stage2 声明层（rootNumber*、parity*、zeroOrder_additivity、
zeroOrderE5_eq_zero_of_L_E5_one_ne_zero）+ LPrime/LSeries5 的解析对象
axiom（lprime1_series、L_E5_series_split）+ 本模块新 axiom
zeroOrderE_eq_one_of_lprime_ne_zero。不含 GRH、不含 bsd_formula_rank_*、
不含 Sha。Kolyvagin 内容收缩为两条非零性桥梁（实现缺口而非数学缺口）。

## 边界（后续轮次，不在本模块代码内）

- 秩 2 排除层的 Leibniz 三型（(2,0)/(0,2)/(1,1) 的二阶导公式）：
  BSD.Positivity.leibniz_artin 是挂账 axiom，可仿本模块 §1 升级为真定理。
- 实例扩列：rank E(ℚ) = 1 ∧ rank E⁵(ℚ) = 0 的曲线逐条闭证。
- 理论级：Skinner 的 Gross–Zagier–Kolyvagin 逆定理（条件路线，
  需良约化 p + E[p] 不可约 + Sha[p^∞] 有限）需外部输入，不入 Lean。
- 文档口径修正（待办）：秩 1 文档 4.1 的六条 (1,1) 曲线（E、E⁵ 解析秩
  均 1）实为秩 2 P* 的 Leibniz (1,1) 证据（L″>0）；秩 1 排除层的实例
  应取 (1,0)/(0,1) 型（如 37a1），闭 L′(E/K,1) = L′(E,1)·L(E⁵,1) > 0。
-/

namespace BSD.ExclusionReduction

noncomputable section

/-! ## 1. 通用 Leibniz 归约（真定理层：乘积求导的解析内容） -/

/-- 乘积求导：d(f·g)/ds 在 s = 1 的分解
    (f·g)′(1) = f′(1)·g(1) + f(1)·g′(1)。
    这是 `Mathlib.Analysis.Calculus.Deriv.Basic.deriv_mul` 的具名实例，
    即 Main.lean 注释中"Artin 分解 + 乘积求导"的解析形态。 -/
theorem product_deriv_decomposition {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1) :
    deriv (fun s => f s * g s) 1 = deriv f 1 * g 1 + f 1 * deriv g 1 :=
  deriv_mul hf hg

/-- Leibniz (1,0) 型归约：f(1) = 0 ⟹ (f·g)′(1) = f′(1)·g(1)。
    秩 1 排除层的解析内容：E 分量一阶零（L(E,1) = 0）+ E⁵ 分量非零
    ⟹ 乘积的一阶导 = 二者乘积。 -/
theorem leibniz_10 {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1) (hf0 : f 1 = 0) :
    deriv (fun s => f s * g s) 1 = deriv f 1 * g 1 := by
  rw [product_deriv_decomposition hf hg, hf0]
  ring

/-- Leibniz (0,1) 型归约（对称）：g(1) = 0 ⟹ (f·g)′(1) = f(1)·g′(1)。 -/
theorem leibniz_02 {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1) (hg0 : g 1 = 0) :
    deriv (fun s => f s * g s) 1 = f 1 * deriv g 1 := by
  rw [product_deriv_decomposition hf hg, hg0]
  ring

/-- 排除层非零传播（(1,0) 型）：f(1) = 0 ∧ f′(1) ≠ 0 ∧ g(1) ≠ 0
    ⟹ (f·g)′(1) ≠ 0。秩 1 排除层的通用判据。 -/
theorem leibniz_10_ne_zero {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 ≠ 0) (hg0 : g 1 ≠ 0) :
    deriv (fun s => f s * g s) 1 ≠ 0 := by
  rw [leibniz_10 hf hg hf0]
  exact mul_ne_zero hf1 hg0

/-- 排除层非零传播（(0,1) 型，对称）。 -/
theorem leibniz_02_ne_zero {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1)
    (hg0 : g 1 = 0) (hf0 : f 1 ≠ 0) (hg1 : deriv g 1 ≠ 0) :
    deriv (fun s => f s * g s) 1 ≠ 0 := by
  rw [leibniz_02 hf hg hg0]
  exact mul_ne_zero hf0 hg1

/-- 秩 2 型的一阶导消失（(2,0)/(0,2) 的一阶面）：f(1) = f′(1) = 0
    ⟹ (f·g)′(1) = 0。秩 2 时 L′(E/K,1) = 0 即此；二阶导的完整
    Leibniz 三型是 BSD.Positivity.leibniz_artin 的升级目标。 -/
theorem leibniz_20_first_vanish {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 1) (hg : DifferentiableAt ℝ g 1)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 = 0) :
    deriv (fun s => f s * g s) 1 = 0 := by
  rw [product_deriv_decomposition hf hg, hf0, hf1]
  ring

/-! ## 2. 对象层（37a1/K，(1,0) 型）：排除层的两个 ℚ 侧非零性 -/

/-- 对象级归约（(1,0) 型）：LK_prime 的定义展开。
    Main.lean 的 `BSD.LK_prime := BSD.Lprime_E1 * LSeries5.L_E5 1`
    （= L′(E,1)·L(E⁵,1)）即 Artin 分解 + 乘积求导 + L(E,1) = 0 的形态；
    本引理把该形态显式化为 `lprime1 * L_E5 1`。 -/
lemma exclusion_layer_factorization : BSD.LK_prime = LPrime.lprime1 * LSeries5.L_E5 1 := by
  rfl

/-- 排除层非零（对象级）：两个 ℚ 侧非零性相乘。
    L′(E,1) ≠ 0：`BSD.LPrime.lprime1_pos`（真定理，反射公式一阶导区间算术）；
    L(E⁵,1) ≠ 0：`BSD.LSeries5.L_E5_one_ne_zero`（真定理，级数区间算术）。
    排除层 = L′(E/K,1) ≠ 0 由此闭环。 -/
theorem exclusion_layer_nonzero : BSD.LK_prime ≠ 0 := by
  rw [exclusion_layer_factorization]
  exact mul_ne_zero (ne_of_gt LPrime.lprime1_pos) LSeries5.L_E5_one_ne_zero

/-! ## 3. ord 级归约（挂账 axiom + 真定理拼合） -/

/-- 秩 1 反向（ℚ 侧）的 ord 级桥梁：L′(E,1) ≠ 0 ⟹ ord₁ L(E) = 1。
    依据：L(E,1) = 0 由根数 ε(E) = −1 的函数方程给出（定理级，
    `BSD.Stage2.rootNumberE_eq_neg_one`），中心值零 + 一阶导数非零
    ⟹ 一阶零点（局部幂级数 / Taylor 展开）。
    前件 `lprime1 ≠ 0` 由 `BSD.LPrime.lprime1_pos`（真定理）逐曲线闭证——
    这就是"秩 1 BSD 反向在 37a1/ℚ 上成立"的形式化落点（理论级开放、
    逐曲线闭证的双重状态的精确表达）。
    升级路径：函数方程 + 解析性（Taylor 展开）的 Lean 实现。 -/
axiom zeroOrderE_eq_one_of_lprime_ne_zero :
    LPrime.lprime1 ≠ 0 → BSD.Stage2.zeroOrderE = 1

/-- 排除层的 ℚ 侧秩 1 判据：`zeroOrderE_eq_one_of_lprime_ne_zero` +
    `lprime1_pos`（真定理）⟹ ord₁ L(E) = 1。 -/
theorem zeroOrderE_eq_one : BSD.Stage2.zeroOrderE = 1 :=
  zeroOrderE_eq_one_of_lprime_ne_zero (ne_of_gt LPrime.lprime1_pos)

/-- 归约定理（ord 级）：排除层在 K 上 ⇔ 两个 ℚ 侧反向特例。
    ord₁ L(E/K) = ord₁ L(E) + ord₁ L(E⁵)（Artin 加性，
    `BSD.Stage2.zeroOrder_additivity`）
    = 1 + 0 = 1，其中 1 来自秩 1 反向（37a1/ℚ 逐曲线闭证，
    `zeroOrderE_eq_one`），0 来自秩 0 反向（E⁵/ℚ 逐曲线闭证，
    `BSD.Stage2.zeroOrderE5_eq_zero`，前件 `L_E5_one_ne_zero` 真定理）。
    即"排除层（ord ≤ 1）归约到两个 ℚ 侧非零性"的 Lean 落点。 -/
theorem exclusion_layer_reduction : BSD.Stage2.analyticZeroOrder = 1 := by
  rw [BSD.Stage2.zeroOrder_additivity, zeroOrderE_eq_one, BSD.Stage2.zeroOrderE5_eq_zero]

/-- 声明层桥：Main 的解析秩 = Stage2 的解析零点阶（同一数量，
    Stage2 注释 "BSD interpretation: analyticRankK = analyticZeroOrder"
    的形式化）。Main.analyticRank 与 Stage2.analyticZeroOrder 各自声明
    为"解析秩(E/K)"，本 axiom 显式统一二者，使两条证明路线可互相拼接。
    升级路径：单一定义替代两个 axiom。 -/
axiom analytic_rank_K_eq_zero_order :
    BSD.analyticRank BSD.Curve37a1 BSD.KFive = BSD.Stage2.analyticZeroOrder

/-- 解析秩(E/K) = 1（第二条路线：经排除层归约）。
    第一条路线：`BSD.Main.analytic_rank_K_eq_one`（LK_prime_pos 经 K 侧
    桥梁 axiom `analytic_rank_K_eq_one_of_LK_prime_ne_zero`）。
    本路线：排除层归约定理 + 声明层桥，两条路线相互独立、结论一致——
    解析秩 1 在框架内被双通道闭合。 -/
theorem analytic_rank_K_eq_one_via_exclusion_reduction :
    BSD.analyticRank BSD.Curve37a1 BSD.KFive = 1 := by
  rw [analytic_rank_K_eq_zero_order, exclusion_layer_reduction]

end

end BSD.ExclusionReduction
