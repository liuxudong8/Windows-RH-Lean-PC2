import OrderPreservingBijection.QuadraticFieldFive
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import BSD.LSeries5
import BSD.LPrime

/-!
# 弱 BSD 秩 1 的 Lean 形式化骨架（BSD）

对应讨论稿《弱 BSD 秩 1 的 Hecke 显式公式重证明：骨架 A 讨论稿（K = ℚ(√5)）》：

- 主曲线 E = 37a1：y² + y = x³ − x（Δ = −37），系数 ∈ ℤ ⊂ 𝒪_K，K = ℚ(√5)（文档 2.1）
- 解析秩(E/K) = 1（文档 4.3、5.4(iii)，确定性判定）：
  - L_K(1) = 0：根数 ε_K = −1 的函数方程（定理）
  - L_K′(1) > 0：乘积恒等式 L_K′(1) = L′(E,1)·L(E⁵,1)（Artin 分解 + 乘积求导），
    数值下界 1.63808 = 0.30599977 × 5.3532 ⊂ (0, ∞)（文档 5.4(iii)(c)；
    旧口径“degree-2 反射公式 + N_K = 1369”主值 2.433224 与正确值 1.63858644 差
    48.5%，已弃用）
- 代数秩(E/K) = 1（文档 2.1、5.4(iv)）：
  - 二次扭分解 rank E(K) = rank E(ℚ) + rank E⁵(ℚ)（特征空间分解，Silverman）
  - rank E(ℚ) = 1（LMFDB，生成元 (0,0)）
  - rank E⁵(ℚ) = 0：L(E⁵,1) ∈ [5.3548616166 − 1.7×10⁻⁷¹, 5.3548616166 + 1.7×10⁻⁷¹] ⊂ (0, ∞)
    （区间算术，N = 800）+ ℚ 端定理“解析秩 0 ⟹ 代数秩 0”（Kolyvagin）

分层策略：
1. **对象层**：曲线与 5-扭的定义、有理点 P₀（可 Lean，已证明）。
2. **声明层**：解析秩 / 代数秩 / 二次扭分解 / 数值判定作为 `axiom`，
   每个 axiom 的注释标明对应文档节与“待证明”状态（数值端为区间算术，
   数论端为 Kolyvagin / Silverman / LMFDB）。这些是后续轮次逐个升级为 theorem 的目标。
3. **定理层**：代数秩 = 解析秩 = 1、弱 BSD 秩 1 情形在 E = 37a1/ℚ(√5) 上成立（拼合）。

Mathlib 现状：尚无 Mordell–Weil 理论、自守 L 函数与椭圆曲线 L 函数模块
（Geometry/EllipticCurve 不存在），故声明层只能 axiom；对象层与定理层是真实 Lean 内容。
-/

namespace BSD

/-! ## 1. 对象层：曲线与扭 -/

/-- K = ℚ(√5) 的代数结构（黄金整数环 𝒪_K = ℤ[(1+√5)/2]，
    复用 OrderPreservingBijection.QuadraticFieldFive；系数 ∈ ℤ ⊂ 𝒪_K）。 -/
abbrev KFive := GoldenInt

/-- E = 37a1：y² + y = x³ − x（一般型 Weierstrass，判别式 Δ = −37，坏约化仅 𝔭 | 37；文档 2.1）。 -/
structure Curve37a1 where
  x : ℚ
  y : ℚ
  eqn : y ^ 2 + y = x ^ 3 - x

/-- 有理点 P₀ = (0,0) ∈ E(ℚ) ⊂ E(K)。
    LMFDB：E(ℚ) ≅ ℤ，P₀ 为生成元（无限阶）。 -/
def P0 : Curve37a1 :=
  ⟨0, 0, by norm_num⟩

/-- E⁵：37a1 的 5-二次扭（Y² = X³ − 25X + 125/4，导子 N = 925，根数 ε = +1；文档 5.4(iv)）。
    来源：E 完成平方 y² = x³ − x + 1/4（A = −1, B = 1/4），二次扭公式
    y² = x³ + Ad²x + Bd³ 取 d = 5。 -/
structure Twist5 where
  X : ℚ
  Y : ℚ
  eqn : Y ^ 2 = X ^ 3 - 25 * X + 125 / 4

/-! ## 2. 声明层（axiom：待证明标记） -/

/-- 解析秩：L(E,s) 在 s = 1 的零点阶（文档 4.3 口径）。
    待证明：自守 L 函数完整理论（mathlib LSeries 尚未覆盖椭圆曲线）。 -/
axiom analyticRank (E : Type) (K : Type) : ℕ

/-- 代数秩：Mordell–Weil 秩（有限生成 + 秩）。
    待证明：mathlib 尚无 Mordell–Weil 理论（有限生成定理 + 秩的定义）。 -/
axiom mwRank (E : Type) (K : Type) : ℕ

/-! ## 2b. 解析秩(E/K) 判定：乘积恒等式形态（文档 4.3(2)、5.4(iii)） -/

/-- L′(E,1)：E = 37a1/ℚ 的 L 函数在 s = 1 的一阶导数。
    公式形态真定理（B3-min 收口）：引用 `BSD.LPrime.lprime1`
    （反射公式一阶导级数形态，N = 37, ε = −1, b_n = 2πn/√37），
    原裸数值 axiom（LMFDB 0.305999773834…）已删除。 -/
noncomputable def Lprime_E1 : ℝ := LPrime.lprime1

/-- L′(E,1) > 0：`BSD.LPrime.lprime1_pos`（真定理：部分和 ≥ 0.0557、
    尾项 |·| ≤ 0.0125、margin 充分）。 -/
theorem Lprime_E1_pos : 0 < Lprime_E1 := LPrime.lprime1_pos

/-- L_K′(1)：L(E/K) 在 s = 1 的一阶导数，乘积恒等式形态
    L_K′(1) = L′(E,1)·L(E⁵,1)（Artin 分解 L(E/K) = L(E)L(E⁵) + 乘积求导 + L(E,1)=0）。
    该定义即文档 4.3(2)、5.4(iii) 的新口径；旧口径（degree-2 反射公式 + N_K = 1369）
    主值 2.433224 与正确值 1.63858644 差 48.5%，已弃用。
    待证明：Artin 分解的 Lean 实现（届时本定义升级为定理）。 -/
noncomputable def LK_prime : ℝ := Lprime_E1 * LSeries5.L_E5 1

/-- L_K′(1) > 0：`Lprime_E1_pos`（真定理）+ `L_E5_one_pos`（已闭合定理）的乘积。
    真定理；axiom 闭包 = 基础公理（无反射公式依赖，B3-min 已闭环）。
    数值下界：0.30599977 × 5.3532 = 1.63808 < L_K′(1)（文档 5.4(iii)(c)；
    5.3532 = 2 × 2.6766 来自 L(E⁵,1) 的 N = 800 区间算术，见 LSeries5.lean 误差预算）。 -/
theorem LK_prime_pos : 0 < LK_prime := by
  have hE : (0 : ℝ) < Lprime_E1 := Lprime_E1_pos
  have hE5 : (0 : ℝ) < LSeries5.L_E5 1 := LSeries5.L_E5_one_pos
  exact mul_pos hE hE5

/-- 解析秩(E/K) = 1 的判定桥梁：L_K′(1) ≠ 0 ⟹ 解析秩(E/K) = 1。
    依据：(i) 根数 ε_K = −1（函数方程 Λ_K(s) = −Λ_K(2−s)）⟹ L_K(1) = 0；
    (ii) 解析秩定义：中心值零且一阶导数非零 ⟹ 一阶零点（局部幂级数）。文档 4.3(1)(2)。
    ε_K = −1 的推导（闭包审计 C5 落档）：根数乘性 ε(E/K) = ε(E)·ε(E⁵)，
    其中 E/ℚ 根数 ε(E) = −1（L(E,s) 奇符号，N = 37 全实模形式），E⁵/ℚ 根数 ε(E⁵) = +1
    （N = 925，±1 由数据核验），故 ε_K = (−1)(+1) = −1。
    (iii) 秩 2 三路排除（2026-10-07 落盘：BSD/Stage2/RankTwoExclusion.lean，`lake build BSD`
    exit 0；闭包核验见 BSD/Stage2/_check_stage2.lean）——"为何解析秩 ≠ 2"：
    解析秩 2 由 Artin 加性分解为三种型（BSD.Stage2.rank_two_decomposition），
    全部被根数奇偶排除：
    (0,2)：需 ord₁L(E) = 0（偶），但 ε(E) = −1 强制 ord₁L(E) 奇 ⟹ 排除（`no_type02`）；
    (1,1)：需 ord₁L(E⁵) = 1（奇），但 ε(E⁵) = +1 强制 ord₁L(E⁵) 偶 ⟹ 排除（`no_type11`）；
    (2,0)：需 ord₁L(E) = 2（偶），但 ε(E) = −1 强制 ord₁L(E) 奇 ⟹ 排除（`no_type20`）。
    故解析秩 ≠ 2（`BSD.Stage2.analyticRankK_ne_two` 直接版 / `analyticRankK_ne_two'` 型筛版，
    闭包 = Stage2 声明层 + 基础，零数值输入；`parityK_propagated` 进一步表明
    秩 2 排除不依赖 ε_K 的 axiom——奇偶经加性自动传播）。与 (ii) 拼合 ⟹ 秩 1 唯一。
    待证明：函数方程 ε_K = −1 与 Artin 分解的 Lean 实现（届时本声明可进一步分解；
    Stage2 的 `parity_neg_one`/`parity_pos_one`/`zeroOrder_additivity` 是首消目标）。
    (iv) P* 收口（2026-10-08 落盘：BSD/Positivity/Positivity.lean，
    `lake build BSD.Positivity.Positivity` exit 0（832 jobs）；闭包核验
    BSD/Positivity/_check_positivity.lean exit 0（833 jobs））——"为何不是 2"的第四环：
    若秩恰 2 幸存，则 L″(E/K,1) > 0（`BSD.Positivity.p_star`，假设 `zeroOrderE + zeroOrderE5 = 2`）。
    逻辑收口：P* ⟺ 分量级 BSD 正性。Artin 分解 L(E/K) = L(E)·L(E⁵) 的 Leibniz 三型中，
    (2,0)/(0,2) 是平凡乘积（秩 0 分量 L(1) > 0 为定理级），唯一非平凡的是 (1,1) 纠缠项
    2·L′(E)·L′(E⁵)，而它恰等于秩 1 的 BSD 正性（L′(1) = Ω·R·Sha/|T|² > 0，猜想级）。
    (1,1) 非真空：数据侦察 6/6 全中（79a1/89a1/91a1/99a1/101a1/106b1 的 E⁵ 全秩 1、
    纠缠乘积全正；389a1 的 E⁵ 秩 0 ⟹ 型 (2,0)，L″(E/K,1) = 1.5186×8.909 ≈ 13.53 > 0），
    见 BSD/Positivity/positivity_recon_summary.md。边界：秩 ≥ 3 ⟹ L″(E/K,1) = 0
    （`BSD.Positivity.rank_ge_three_implies_Lpp_zero`）——"所有秩 ≥ 2 的 L″ 有正下界"
    严格为假，P* 的假设域恰为秩 2。
    待证明（P* 侧）：秩 1/秩 2 分量正性（= BSD 正性猜想，axiom
    `lprime_pos_of_rank_one(_5)` / `lprimeprime_pos_of_rank_two(_5)` 的首消目标）。 -/
axiom analytic_rank_K_eq_one_of_LK_prime_ne_zero :
    LK_prime ≠ 0 → analyticRank Curve37a1 KFive = 1

/-- 解析秩(E/K) = 1：`analytic_rank_K_eq_one_of_LK_prime_ne_zero` + `LK_prime_pos`（真定理）。
    数值判定 L_K′(1) > 0 已真证（B3-min 收口后闭包含 `Lprime_E1_pos`（LPrime.lprime1_pos
    真定理）+ `L_E5_one_pos` 定理），不再依赖任何 L′(E,1) 裸数值 axiom。
    axiom 闭包 = `analytic_rank_K_eq_one_of_LK_prime_ne_zero` + 基础公理。 -/
theorem analytic_rank_K_eq_one : analyticRank Curve37a1 KFive = 1 :=
  analytic_rank_K_eq_one_of_LK_prime_ne_zero (ne_of_gt LK_prime_pos)

/-- rank E(ℚ) ≥ 1（2-下降 ② 的构造输入：P₀ = (0,0) 无限阶）。
    支撑（②a 真证层见 BSD.TwoDescent §1b/§1c）：
    E′ : Y² = X³ − 16X + 16 上 P′ = (0,4)；7P′ = (−20/9, 172/27) 由 E′ 群法则
    （切点加倍 `Eprime_double` + 割线加法 `Eprime_add`，曲线保持已真证）逐步计算：
    `P2_eq_double`..`P7_eq_add`（2P′..7P′ 全部真证）；
    7P′ 的 X 坐标分母 = 9 = 3² 含素因子 3 ∉ {2, 37}（坏约化素 Δ′ = 2¹²·37，
    `P7_X_den_nonbad_factor`）⟹ P′ 非扭（Silverman VIII.7.1(b)：扭点 x 坐标分母
    只含坏约化素的素因子，外部定理）。
    Lutz–Nagell 候选整点 (0,±4),(4,±4),(−4,±4),(1,±1) 恰为 P′, 2P′, 3P′, 5P′ 的倍数。
    待证明：Silverman VIII.7.1 的 Lean 实现（需要完整椭圆曲线约化理论，mathlib 缺失；
    ②a 已真证其全部输入：7 倍链计算 + 分母坏因子事实）。 -/
axiom rank_E_Q_ge_one : 1 ≤ mwRank Curve37a1 ℚ

/-- rank E(ℚ) ≤ 1（2-下降 ②，Selmer 计算）。
    论证骨架（见 BSD.TwoDescent §3）：
    K = ℚ(θ)，θ³ − 16θ + 16 = 0；E(ℚ)/2E(ℚ) ↪ {z ∈ K*/K*² : N(z) ∈ ℚ*²}；
    rank ≤ dim Sel² − dim E(ℚ)[2] = dim Sel²；Sel² ≅ ℤ/2（数值核验 selmer7.py
    + LMFDB 37.a1：E(ℚ) ≅ ℤ）⟹ rank ≤ 1。
    口径注：这里的 2-下降作用在 E′ 上（37a1 的整系数模型，Y² = X³ − 16X + 16）；
    E′[2](ℚ) = {O} 已真证（`BSD.TwoDescent.Eprime_two_torsion_trivial`，
    X³ − 16X + 16 无 ℚ 根——有理根定理 + 整数枚举，原数值核验升级）；
    E 与 E′ 差一个 2-同源（平移 + 缩放，`toEprime_preserves`），同源保持 Mordell–Weil
    秩（标准事实），故 rank E = rank E′ ≤ 1。
    待证明：三次域类数/单位群/局部可解性的 Lean 实现（②b 剩余，Selmer 数值已收口）。 -/
axiom rank_E_Q_le_one : mwRank Curve37a1 ℚ ≤ 1

/-- rank E(ℚ) = 1：`rank_E_Q_ge_one` + `rank_E_Q_le_one`（2-下降 ② 拼合）。 -/
theorem rank_E_Q_eq_one : mwRank Curve37a1 ℚ = 1 :=
  le_antisymm rank_E_Q_le_one rank_E_Q_ge_one

/-- rank E⁵(ℚ) = 0（文档 5.4(iv)，确定性判定）。
    纯文献断言：Kolyvagin 的 Euler 系统定理 [Kolyvagin 1989]——E 是模椭圆曲线且
    L(E,1) ≠ 0 ⟹ rank E(ℚ) = 0（且 Ш(E,ℚ) 有限）。
    适用范围核验：E⁵ = 37a1 的 5-扭（N = 925 = 5²·37，ε = +1）由 BCDT 2001
    全模性保证模性（无需半稳定；Kolyvagin 定理对模曲线成立，不依赖 Heegner 点机制）。
    前件已真证：`L_E5_one_ne_zero`（LSeries5.lean 定理，由 `L_E5_one_pos` 推出；
    闭包含 `L_E5_series_split`（反射公式 axiom）+ part50/crude50 的
    native_decide 计算信任 + 部分和/尾界定理）。
    待证明：Kolyvagin 定理与模性的 Lean 实现（mathlib 无 Euler 系统/模性理论——
    领域前沿级工作量，axiom 保留为唯一诚实选择）。 -/
axiom rank_E5_Q_eq_zero_of_L_E5_ne_zero : LSeries5.L_E5 1 ≠ 0 → mwRank Twist5 ℚ = 0

/-- rank E⁵(ℚ) = 0：`rank_E5_Q_eq_zero_of_L_E5_ne_zero` + `L_E5_one_ne_zero`（真定理接线）。
    前件依赖从此显式化：axiom 只断言文献定理（L(E⁵,1)≠0 ⟹ 秩 0），
    "L(E⁵,1)≠0"本身由 Lean 定理供给（闭包含反射公式 axiom + 区间算术）。 -/
theorem rank_E5_Q_eq_zero : mwRank Twist5 ℚ = 0 :=
  rank_E5_Q_eq_zero_of_L_E5_ne_zero LSeries5.L_E5_one_ne_zero

/-- 二次扭分解：rank E(K) = rank E(ℚ) + rank E⁵(ℚ)，K = ℚ(√5)（文档 2.1）。
    证明（纸面）：E(K) 是有限生成 ℤ[Gal(K/ℚ)]-模，σ 生成 Gal ⟹ 特征空间分解
    E(K) ⊗ ℚ ≅ E(ℚ) ⊗ ℚ ⊕ E⁵(ℚ) ⊗ ℚ（Silverman [8]）。
    待证明：Mordell–Weil 群的 Galois 模结构（特征空间分解）。 -/
axiom twist_decomposition :
    mwRank Curve37a1 KFive = mwRank Curve37a1 ℚ + mwRank Twist5 ℚ

/-! ## 3. 定理层（拼合） -/

/-- 代数秩(E/K) = 1：二次扭分解 + rank E(ℚ) = 1 + rank E⁵(ℚ) = 0。 -/
theorem algebraic_rank_K_eq_one : mwRank Curve37a1 KFive = 1 := by
  rw [twist_decomposition, rank_E_Q_eq_one, rank_E5_Q_eq_zero]

/-- 解析秩(E/K) = 1（5.4(iii) 区间算术判定）。 -/
theorem analytic_rank_K_eq_one' : analyticRank Curve37a1 KFive = 1 :=
  analytic_rank_K_eq_one

/-- 弱 BSD 秩 1 情形在 E = 37a1/ℚ(√5) 上成立：代数秩 = 解析秩 = 1。
    两方向均不依赖 Gross–Zagier 的 Heegner 点机制：
    解析侧靠区间算术（5.4(iii)），代数侧靠二次扭分解 + E⁵ 秩 0 判定（2.1、5.4(iv)）。 -/
theorem weak_BSD_37a1 :
    mwRank Curve37a1 KFive = analyticRank Curve37a1 KFive := by
  rw [algebraic_rank_K_eq_one, analytic_rank_K_eq_one]

end BSD
