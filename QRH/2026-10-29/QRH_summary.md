# QRH 项目总结（攻防 XLII「干到 1」主线 + Lean 形式化）

> 2026-10-27 定稿。数学层 S0–S7.6 已闭环落档 d1；Lean 形式化 Main (L3)(L4) 已落位、2604 jobs 全绿；S7.7 击破清单四连已落档；(L1)(L2) 长线攻坚第一轮已落档 S7.8（真实定义件 + Abel–SW 组装真证 + trivialTerm 收敛件，2604 全绿）。
> 2026-10-29 增量：Core 清单项 `C_MT<4/3` 纯有理链真证确认（sin_lower_five + cos_upper_four + C_MT_lt_four_thirds；√2 全程消去、无积分、无聚合依赖）；真证链 26→29；build_verify_cmt43.txt 增量全绿。
> 2026-10-29 增量②：`prime_weight_bounds` axiom 降为真证定理 `prime_weight_bounds_Khat`（Khat 特化）——Core 增 `abs_sin_div_two_mul_le_half` + `khat_global_bound`（全局一致界 |K̂u| ≤ 1/(√2·|sin(1/√2)|)，用 |sin t| ≤ |t| 绕开 `Khat_abs_le` 分母 |√2±2πu| 零点）；Main 真证四引理（log_succ_sub_le_inv / inv_sqrt_succ_le / inv_sqrt_sq_eq_inv / inv_sqrt_succ_sub_le）→ `prime_weight_bounds_Khat`（M = L·δ + B）→ `prime_sum_bound` 特化 K := Khat（bgs5 前移）；新挂账命名 axiom `fourierCos_Khat`（连接件）+ `khat_lipschitz`（光滑件）；全量 **2704 jobs 绿**（dbg_build.txt），无 warning（清理 6 处历史 unused）。落档 d1 S7.10（中英，audit 0 errors、渲染逐页通过）。
> 2026-10-29 增量③：**(L1) x=1 边界口径闭环（S7.11）**——trivialTerm 在 x=1 为调和型发散（Σ 1/(2ℓ+r) ~ ½Σ 1/ℓ），`landau_explicit_L` 前提由 1 ≤ x 收紧为 1 < x（防假命题陷阱：原宽松前提在 x=1 断言 trivialTerm(1) = −logDeriv(r)，而发散点 ∑' 默认值 0 无数学意义）；新增约定件 `trivialTerm_one_term` + `trivialTerm_one`（真证，simp / tsum_congr）；发散性正式证明（¬ Summable）留可选后续。真证链 +2（31+→33+）；全量 **2704 绿**（dbg_build_x1.txt）。落档 d1 S7.11（中英，audit 0 errors、渲染 3+3 页逐页通过）。
> 2026-10-29 增量④：**arXiv 英文草稿《QRH-arXiv-draft-single-family-pairing-constant-L(s,chi5).docx》（d1\en）六处统一口径，C_MT<4/3 已证首次入稿**——摘要（35+ lemmas / 2704 jobs passing (2026-10-29), including the proved constant bound C_MT < 4/3）、引言贡献 (iii)（同口径）、§3 变分机制段尾（"The bound C_MT < 4/3 is proved in Lean (Section 9; pure rational chain, 2026-10-29)"）、§9 Lean 章节（2704/35+ + C_MT_lt_four_thirds 纯有理链细节：cos 四阶上界 73/96、sin 下界 11/(12√2)−√2/800 在 x₀=1/√2 处 ⟹ cot < 1825/(1097√2) ⟹ C_MT < 2922/2194 < 4/3，无积分层、无聚合依赖；fourierCos Bochner 真定义 + fourierCos_scale 真证入稿）、Conclusion（35+/2704 + C_MT < 4/3）、参考文献 [11]（dbg_build_fourier.txt 2704 jobs green, 2026-10-29）。旧口径（26 lemmas / 2604 jobs / main_l2_full.txt）全文清零。audit --source 对比 0 errors（新增 run 格式继承一致）、render 8 页逐页通过、catalogue 无 TOC 不动作。编辑脚本 s712_work\edit_arxiv_cmt.py（含 add_run_after_last 继承末个 w:r rPr），SOURCE 备份 s712_work\SOURCE_arxiv_draft.docx。
> 口径基准：7/8 为既定目标（31/32 被否）；A 是数据而非定理；「证到 1」≠ 接近 RH（统计口径 vs 实际描述）。

## 1. 项目定位

目标：证明 L(s, χ₅) 单族配对常数 A(λ) → 1。这是 QRH（拟随机假设）常数机制攻坚的唯一现实通道：
QRH 常数 0.6725 → 7/8 需要 A ≤ 1.125。A→1 远强于 A ≤ 1.125，故「干到 1」一次性打通 7/8。

## 2. 判定链

- 配对常数：A_L(K) = 1 + (Σ_{Δ≠0} K(δΔ)²)/N_Z，δ = logT/(2π)。
- 常数机制：C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963；0.6725 = 2 − C_MT（QRH 常数）。
- 定理 S7.1（L 版 BGS 型配对公式，弱实部假设下）：A_L(K) ≤ C_MT + O(ε) + o(1)。
- A ≤ 1.125 ⟺ 7/8 成立（0.6725 → 7/8 通道）；A → 1 为最强情形。
- 现阶段数值：Fejer 窄核 λ→0 极限 A → 1.0079（T = 6×10⁵）；窄核专项推进后 A ≈ 0.990；5 子区间漂移 ≤ 0.005。

## 3. 数学主线（攻防 XLII S0–S7.6，d1 已落档）

| 阶段 | 内容 | 判定 |
|---|---|---|
| S0 | 全尺度 GUE 配对与在线比例 1−o(1) 数值定向；口径修正与超 GUE 排斥 | 生死门：A→1 在数值上可见 |
| S1a | Parseval 归因：δF/δR 分解与核依赖 | 配对常数残差结构归因 |
| S1b | λ(T) 构造与核依赖常数 p 的量化（定理骨架） | 干到 1 的定理框架 |
| S2(i) | Weil 显式公式实部口径注入敏感性（与 S1 左尾威胁闭合链） | 威胁窗收窄 |
| S2(ii) | 跨 T 衰减律判别（配对常数误差律） | S1b 速率标度钉死 |
| S3 | Δ 常数指纹排除交叉验证（同虚部成对注入爆炸响应） | 威胁排除 |
| S4 | 正向构造：窄核实测与配对常数残差结构 | λ(T) 构造数值定锚 |
| S5 | ε 定理级控制：跨族 f(0) 形态实测与并集配对公式无条件化构造 | 并集公式无条件化 |
| S6 | λ_eff ≤ 1 卡点解除：λ ≤ 1/2 最优核族的 0.6725 严格化判定 | 唯一硬卡点解决 |
| S7 | Yildirim 方法移植闭路：L(s,χ₅) 单族 BGS 型配对公式存在性判定 | H2 闭路 |
| S7.1 | 形式化证明 Lean 落地（Yildirim 公式 (7) L 版展开 + BGS 引理 3–5 逐条移植） | 见 §5 |
| S7.2 | 数值件 F：超支撑素数项可忽略性实测 | S(X) = O(√X·poly(log X)) |
| S7.3 | 骨头 1（N1）：BGS 引理 5 超支撑推广（缩放自同构） | A→1 路径 |
| S7.4 | 骨头 2（N2）：ε–λ 联动（正则化撑宽与有效核宽标度律） | 撑宽缺口闭合 |
| S7.5 | 骨头 3（N3）：离线项一致版本（BGS 余项跨 λ 一致） | 跨 λ 一致性 |
| S7.6 | SW 常数显式化：L(s,χ₅) 素数项显式界 (C,c) | 常数显式 |
| S7.7 | 击破清单四连：BGS 引理 3–5 移植（Main）+ N1/L1 真证（Stage3）+ BGS 引理 4 T^{3/8} 切割链（Main）+ 落档 | (L3)(L4) 落位 |

## 4. 三硬骨头与 SW 常数（推 1 断层闭合）

「推 1」撞上的理论断层：XLII 路线要求 λ_eff(T) = (logT)^q → ∞（核越来越窄、谱支撑无限扩大），而 S7 闭路只覆盖 λ ≤ 1/2（BGS 引理 5 硬条件）。λ → ∞ 时实空间核宽 a → 0，差型配对中 ĥK(δ·log p) 支撑变宽，素数项 S(X) 可能失去频域窄支撑保护。三个硬骨头：

- **N1（BGS 引理 5 超支撑推广）**：缩放自同构 scaleKernel a r 支撑保持；λ→∞ 超支撑下素数项仍被 χ₅ 振荡抵消，A→1 路径打通。
- **N2（ε–λ 联动）**：λ = (logT)^q、a = (logT)^{−q}、ε = c·(logT)^{−q} ⟹ 偏差 O((logT)^{−q})——正则化撑宽与有效核宽联动。
- **N3（离线项一致版本）**：BGS 余项 O(T√logT) 对 supp⊂[−1,1] 一切核一致（外层 ∃R 对 K 一致）。
- **SW 常数显式化（S7.6）**：Siegel–Walfisz 素数项界 |Σ_{n≤x} Λ(n)χ₅(n)| ≤ C·x·e^{−c√log x}，理论 c = 1/√R₀ ≈ 0.3954（Kadiri R₀ = 6.3970）；实测 C_obs = 1.70e−3 另记；L(1,χ₅) = 0.430409 > 0；β ≥ 0.9029。

数值件 F 实测：S(X) = Σ_{p≤X} Λ(n)χ₅(p)p^{−1/2}·K̂_a(δ·log p) = O(√X·poly(log X))，相对 N_L ~ (X/2π)·logX 为 o(1)，**无需** e^{−c√logX} 指数级；|S_a| ≈ 2.05 有界收敛（强于理论上界），|S_a|/N_L 单调衰减至 1e−8（X = 10⁸）。

## 5. Lean 形式化状态（C:\proj2\QRH，mathlib v4.34.0-rc2）

构建：`lake build QRH` **2604 jobs 全绿**（exit=0；2026-10-27，build_qrh_l4b.txt）；Windows 侧 mathlib 聚合 Mathlib.olean 未生成，仅具体模块 import。**架构（2026-10-27）**：为打破 import 环（Stage3⇄Main），fourierCos 与 normL1 迁至 Core 新增 4b 节，依赖链 Core→Main→Stage3 单向；Core 增 import `MeasureTheory.Measure.Haar.NormedSpace`（积分变量替换引理系，Bochner 无条件）。

**误差界宏（弃 Asymptotics.IsBigO 与 ε–N）**：`Bound C T0 err f := 0≤C ∧ ∀T≥T0, |err T| ≤ C·f T`；`BoundBall C δ err f := 0≤C ∧ ∀|x|≤δ, |err x| ≤ C·f x`。

**真证链（2026-10-29 现状，35+ 件）**：

- Core（S7_1_Core.lean）：`sin_inv_sqrt2_ne_zero`（分母良定义）、`Khat_neg`（偶性）、`Khat_zero`（K̂(0)=1，sin/x 极限延拓）、`Khat_abs_le`（频域衰减三角不等式界）、`f0_continuous`；**`normL1`（Bochner 积分真定义 ‖f‖₁=∫|f|，axiom 降级）**；**`sin_lower_five`/`cos_upper_four`/`C_MT_lt_four_thirds`（C_MT<4/3 纯有理链：cos 四阶上界 73/96 经 cos x=1−2sin²(x/2)+平方单调自证，sin 五阶损失并入，√2 消去，无积分依赖）**；**`abs_sin_div_two_mul_le_half`/`khat_global_bound`（S7.10，2026-10-29：|sin t/(2t)| ≤ 1/2（|sin t| ≤ |t|，t=0 分支 subst）→ 全局一致界 |K̂u| ≤ 1/(√2·|sin(1/√2)|)——`Khat_abs_le` 分母 |√2±2πu| 在 u=±√2/(2π) 为零、非全局界，故换道）**。
- Stage3（S7_1_Stage3.lean）：`scaleKernel_support`（N1 支撑保持）、`f_eps_support`（N2 支撑 [−1/2,1/2]）、`Khat_a_even`（一阶校正恒零）、`sum_abel`（Abel 求和归纳）、`khat_second_order_bound`（K̂ 二阶一致界真证，2026-10-26 迁入替换 axiom）、**`n1_diag_invariant`**（r̂_a(0)=r̂(0)，z=0 取点真证）、**`n1_offdiag_scale_eq`**（K̂_a(2δ)²=r̂(2aδ)²，两层 congr 1 真证）、**`n1_offdiag_vanishes`**（结构件真证：scale_eq 重写 + 频域衰减件 |r̂(2aδ)|²≤a²C 假设闭合）、**`scaleKernel_L1_invariant`**（abs_mul + integral_const_mul + integral_comp_inv_mul_left + field_simp，Haar 变量替换链）、**`fourierCos_scale`**（**真证，2026-10-29**：fourierCos 本体 axiom→Bochner 真定义后，四段 calc——integral_const_mul 提 1/a → div_eq_inv_mul 重构 x/a=a⁻¹·x → Measure.integral_comp_inv_mul_left Haar 变量替换（全空间、无正则性前提，任意 r 成立）→ cos 参数 ring + field_simp 消 |a|；**推翻旧判断"需 IntervalIntegral"**——v4.34 Bochner 重构至 Integral/Bochner/ 子目录，缩放律无需聚合，n1_diag_invariant/n1_offdiag_scale_eq 使用点无损）。
- Main（S7_1_Main.lean）：**`Khat_admissible`**（K(0)=1 真证 Khat_zero + 频域支撑件）、**`pair_sum_expansion`**（由大 axiom 降为 bgs3_pair_expansion 组装定理）、**`offcritical_small`**（由 axiom 降为 bgs4_offcrit_split/low/high 组装真证，R=R₁+R₂）、`s71_main` 组装真证（2026-10-27，接实参 Khat_admissible）；**(L2) 区（2026-10-27 晚）**：`sum_abel_partial`（Icc 口径部分和版 Abel，hIcc' = insert N 分解真证）、`prime_sum_bound`（量子项组装真证，C = c·M·(C₂+C₃)）；**(S7.10 prime_weight_bounds 降定理，2026-10-29)**：`log_succ_sub_le_inv`（|log(n+1)−log n| ≤ 1/n）、`inv_sqrt_succ_le`（(√(n+1))⁻¹ ≤ (√n)⁻¹）、`inv_sqrt_sq_eq_inv`（C·C = n⁻¹）、`inv_sqrt_succ_sub_le`（|A−C| ≤ C³，有理化 √(n+1)−√n = 1/(√(n+1)+√n)）→ **`prime_weight_bounds_Khat`**（theorem：有界 |b_n| ≤ M·(√n)⁻¹ + 平滑 |Δb_n| ≤ M·C³，M = L·δ + B，L 来自 `khat_lipschitz`、B 来自 `khat_global_bound`）→ **`prime_sum_bound` 特化 K := Khat**（签名去 K/hKs、体内 rcases prime_weight_bounds_Khat δ hδ、`bgs5_khat_fourier_supp` 前移到 primeSum 后）；**(L1) 区**：`primePowerSum_half_eq_sqrt`（n^{−1/2} = (√n)⁻¹）、`primePowerSum_half`（r=1/2 展开，衔接 primeSum K≡1 特例）、`trivialTerm_term_nonneg`、`trivialTerm_term_le`、`trivialTerm_summable`（x>1、r>0 收敛：rpow 分解 + inv 界 + 几何级数比较）。

**khat_second_order_bound 真证链**（BoundBall 1 (1/24)）：K̂(u) 乘形式闭式 Khat_closed_form = [cos m − √2·m·cotR·sin m]/(1 − 2m²)，m = πu；|u| ≤ 1/24、π < 16/5 ⟹ |m| ≤ 2/15 ⟹ m² ≤ 4/225 ⟹ 分母 1−2m² ≥ 217/225 > 0；分子拆分 N = m²(3/2 − √2·cotR) + cos 二阶余项 − √2·m·cotR·(sin 一阶余项)；cos/sin 余项用 Real.cos_bound/sin_bound、c0_bound（|3/2 − √2·cotR| ≤ 9/50，cotR ∈ [1, 237/200]）；拼接得 |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴。数值核对：½|K̂″(0)| ≈ 1.53 < 2（2u² 系数来源）。

**主定理 s71_main（组装真证，2026-10-27，替代 sorry）**：A_L(K) ≤ C_MT + C₁ε + C₂，C₂ = 2 显式。证明链 = pair_sum_expansion 分解 A_L = diag + prime + offcrit → diag ≤ C_MT + C₁ε（n2_linkage O(ε)）+ |prime|,|offcrit| ≤ 1 并入 C₂（linarith + ring）；(L3) axiom 语义已强化（diag 界入陈述）。全量 **2604 jobs 全绿**（build_qrh_l4b.txt）。2026-10-27 更新：pair_sum_expansion 由大 axiom 降为 bgs3_pair_expansion 组装定理，核可容许谓词 KernelAdmissible（K(0)=1 ∧ supp K̂⊂[−1,1]，λ≤1/2 核族）显式进入主定理链，s71_main 增加实参 Khat_admissible。

**长线 (L1)(L2) 攻坚第一轮（2026-10-27 晚，2604 全绿 main_l2_full.txt）**：
- **(L2) 半形式化落位完成**：`sum_abel_partial`（Icc 口径部分和版 Abel，真证）、`prime_sum_bound`（量子项组装真证：primeSum → Abel → SW 部分和 → 权重/衰减件，C = c·M·(C₂+C₃)）；`siegel_walfisz_chi5` 仍命名 axiom（PNT-in-AP 量级），内部结构已由 `prime_weight_bounds_Khat`（**真证，2026-10-29 降定理**，单常数 M 兼 |b_n|≤Mn^{−1/2} 与 |Δb_n|≤Mn^{−3/2}）、`sum_weight_decay`（C₂）、`sum_sqrt_decay`（C₃）三件显式化——裸 axiom 升级为「真实素数项 + Abel 组装」，SW 本体为下一步击破目标。
- **(S7.9 支撑截断口径 + 窗外拆窗，2026-10-29，两衰减件 axiom 降级 theorem）**：原裸 Σ n^{∓1/2}·e^{−c′√log n} 数学上发散（e^{−c′√log n} 亚多项式衰减，积分检验 u=√log x 发散），根因三层：K̂ 频域窄支撑截断（|δ log p|≤1 ⟹ p≤e^{1/δ}，有限和）+ χ₅ SW 振荡 + Abel 差分。新口径：`sum_weight_decay` theorem（C₂ = 2√(e^{1/δ})，链 = 逐项望远镜 `inv_sqrt_telescope_le`（(a−b)(a+b)=1）+ `sum_sqrt_telescope`（Icc 归纳）+ `sum_inv_sqrt_le_two_sqrt`（Σ_{n≤N} n^{−1/2} ≤ 2√N））；`sum_sqrt_decay` theorem（C₃ = e^{3/(2δ)}，链 = 逐项 e^{−c′√log n} ≤ 1 + `sum_le_card_nsmul`（card(Icc 1 N)=N 手写归纳：Icc∪{N+1} 分解 + `card_union_of_disjoint`）+ `mul_le_mul` + `Real.sqrt_le_iff` 平方单调（√(e^{1/δ}) ≤ e^{1/(2δ)}，无 Real.sqrt_exp 需绕））。**窗外拆窗（同轮完成）**：拆窗暴露出权重/支撑件空间错位——primeSum 权重原为时域 K(δ log n)，而窗外零性（|δ log n|>1 ⟹ 权重=0）只能由频域支撑件 `∀u, 1<|u| → fourierCos K u = 0` 给出，故全局改权重为频域核 `fourierCos K (δ log n)`（=K̂，与 S7.9 文档「素数项=K̂(δ log p)」口径一致，prime_weight_bounds 注释同步）；新增真证 `primeSum_window_eq`（by_cases min 拆窗：窗内 rw [hmin]；窗外 `Finset.sum_subset` + `Nat.floor_lt` + `Real.exp_lt_exp` + `mul_lt_mul_of_pos_left` ⟹ 窗外项 K̂=0 ⟹ 和式收缩到 ⌊e^{1/δ}⌋₊）。`prime_sum_bound` 去窗内前提 hXw：X' = min X (e^{1/δ}) 自动满足窗内（min_le_right），签名改 `(hKs : ∀ u, 1<|u| → fourierCos K u = 0)`，对任意 X ≥ 1 成立，C = c·M·(C₂+C₃)。真证链 +3（含拆窗），挂账 axiom −2。**落档**：S7.9 文档补拆窗小节（§6，含 6.1 空间错位口径 / 6.2 拆窗引理 / 6.3 无窗内版 / 6.4 验证），d1 惯例，audit errors=0，5 页渲染逐页通过。
- **(L1) 真实定义件**：`zeroWeightedSum`（复和取实部 Complex.cpow）/ `primePowerSum`（Finset 有限和 + Real.rpow）/ `trivialTerm`（∑' 实级数，χ₅ 偶特征 a=0）由 opaque 升级为真实定义；`logDerivTerm` 保持 opaque（导数件，下一轮）。
- **(L1b) 真证两件**：`primePowerSum_half_eq_sqrt` + `primePowerSum_half`（r=1/2 代数桥：n^{−1/2} = (√n)⁻¹，衔接 (L2) primeSum K≡1 特例）；`trivialTerm_summable`（x>1、r>0 级数可和：rpow 分解 x^{−(2ℓ+r)} = x^{−r}·(x^{−2})^ℓ + inv 界 + 几何级数比较）。
- **(L1b-C) x=1 边界口径（S7.11，2026-10-29）**：trivialTerm 在 x=1 为调和型发散（Σ 1/(2ℓ+r) ~ ½Σ 1/ℓ）；`landau_explicit_L` 前提由 1 ≤ x 收紧为 1 < x（防假命题陷阱：x=1 时 primePowerSum/zeroWeightedSum 为 0 而 logDerivTerm 一般非零，发散点 ∑' 默认值 0 无数学意义）；约定件 `trivialTerm_one_term`（x=1 逐项等式，simp）+ `trivialTerm_one`（trivialTerm r 1 = Σ 1/(2ℓ+r)，tsum_congr）真证；发散性正式证明（¬ Summable）留可选后续（"口径决定，非深证明"）。

**(L3)(L4) 移植（2026-10-27，Main 击破清单核心，已落位）**：
- 引理 5（核构造）→ KernelAdmissible + axiom bgs5_khat_fourier_supp（频域支撑，积分层件）+ Khat_admissible 组装。
- 引理 3（配对和展开）→ axiom bgs3_pair_expansion（A_L = diag+prime+offcrit；diag ≤ C_MT+C₁ε；|prime|,|offcrit| ≤ 1，Montgomery–Vaughan 均值口径）。
- 引理 4（离线误差）→ T^{3/8} 切割链：opaque offcritLow/offcritHigh + bgs4_offcrit_split/low/high（|·| ≤ R₁√log s / R₂√log s），offcritical_small 组装真证（abs_add_le + add_le_add + ring，R = R₁+R₂）。
- **数学诚实修正**：N1 vanishing 原 ∀N 陈述过宽（r̂(0)=1 不消失，fourierCos_scale 只给等式），改为带正参数 C 的显式衰减件假设。

**挂账 axiom（2026-10-29 现状，如实记录）**：
- Core 清单项：`C_MT<4/3`——**已真证出账**（2026-10-29；sin_lower_five + cos_upper_four + C_MT_lt_four_thirds；cos 四阶上界 73/96 经 cos x=1−2sin²(x/2) 自证，避开 mathlib cos_bound 余项 (5/96)|x|⁴ 不足；纯有理链、无积分、无聚合依赖）。**`fourierCos` 本体已真定义出账（2026-10-29）**：axiom → Bochner 积分真定义 fourierCos K z := ∫ x, K(x)·cos(2πzx) dx（不可积惯例 0，与 normL1 同机制；调用签名未变，primeSum/prime_weight_bounds 使用点无损）。**2026-10-29 新增命名 axiom**：`fourierCos_Khat`（连接件：fourierCos Khat = Khat 解析式挂钩——prime_weight_bounds 必须特化 K:=Khat 的根因）、`khat_lipschitz`（光滑件：∃L 全局 Lipschitz；L 由解析式可算，下一步导数件可真证）。
- Stage3：`n2_linkage`、`n3_remainder_uniform`、`N_L`、`N_L_lower_bound`（数论件，陈述完整；真证挂 mathlib 聚合 Mathlib.olean）；`f0_sub_feps_L1_bound`（**精确陈述声明入列 2026-10-27**：‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹；真证挂聚合）；`pair_const_eps_bias`（待 pairConstant 真实定义，Stage 2 后由 L¹ 界 + Lipschitz 推出）。已真证出账：`n1_diag_invariant`、`n1_offdiag_scale_eq`、`n1_offdiag_vanishes`（结构件，衰减件为带 C 假设）、`scaleKernel_L1_invariant`、**`fourierCos_scale`（2026-10-29，真证；其"需 IntervalIntegral/聚合"旧判断已实证否决——v4.34 Bochner 重构后 Measure.integral_comp_inv_mul_left 全空间可用）**。
- Main：`siegel_walfisz_chi5`（命名 axiom——PNT-in-AP 量级；内部三件显式化，2026-10-27 晚）；`landau_explicit_L`（组成项三件真实定义完成 + (L1b) 两件真证出账 + **(L1b-C) x=1 边界口径闭环**（S7.11，前提 1≤x→1<x，约定件两件真证）；logDerivTerm 仍 opaque、零点无条件收敛挂 (L1c) N(T) 计数）；`bgs5_khat_fourier_supp`、`bgs3_pair_expansion`、`bgs4_offcrit_split/low/high`（命名 axiom，2026-10-27 落位）；`offcritLow/offcritHigh` opaque。已真证出账：`pair_sum_expansion`（组装定理）、`offcritical_small`（组装真证）、`sum_abel_partial`、`prime_sum_bound`、**`prime_weight_bounds_Khat`（2026-10-29）**、`primePowerSum_half_eq_sqrt`、`primePowerSum_half`、`trivialTerm_term_nonneg`、`trivialTerm_term_le`、`trivialTerm_summable`、**`trivialTerm_one_term`/`trivialTerm_one`（2026-10-29，S7.11）**。

**文件结构**：C:\proj2\QRH.lean（根，import Core/Main/Stage3）；QRH\S7_1_Core.lean（4b 节：fourierCos **Bochner 积分真定义**（2026-10-29，axiom 降级）+ normL1 Bochner 定义 + fourierCos_Khat/khat_lipschitz 命名 axiom；import Haar.NormedSpace）；QRH\S7_1_Stage3.lean（N1/L1 真证链）；QRH\S7_1_Main.lean（zerosLChi5、pairConstant、WeakRealPart 抽象 + (L3)(L4) 移植 + s71_main 组装真证）；QRH\Dbg_Khat.lean（khat 真证开发档案）。编译证据：build_core1..12.txt、build_main1..9.txt、build_stage3.txt、build_qrh_full{,2,3,_khat,_khat2,_s71}.txt、dbg_khat.txt、dbg_probe3.txt（IntervalIntegral.olean 缺失确认）、main_precise.txt、stage3_precise.txt、build_qrh_precise.txt、build_qrh_l1.txt、**build_qrh_l4b.txt（2026-10-27 全量 2604 绿）**、**main_l2_full.txt（2026-10-27 晚 (L1)(L2) 全量 2604 绿）**、**build_verify_cmt43.txt（2026-10-29 C_MT<4/3 增量全绿）**、**dbg_build.txt（2026-10-29 prime_weight_bounds 降定理全量 2704 绿）**、**dbg_build_x1.txt（2026-10-29 x=1 口径全量 2704 绿）**、**dbg_build_fourier.txt（2026-10-29 fourierCos 真定义 + fourierCos_scale 真证全量 2704 绿）**。

## 6. 下一步（按依赖序）

1. **Stage 4 已达成**（2026-10-27）：s71_main 组装真证 + (L3)(L4) 移植落位（Main 击破清单仅剩 (L1)(L2) 长线）——Lean 侧可核查的最远合理点已达。
2. **条件封口（2026-10-29 推进）**：积分层剩余——Stage3 `fourierCos_scale`（频域变量替换）**已于 2026-10-29 真证出账**（fourierCos 本体同步 axiom→Bochner 真定义；Measure.integral_comp_inv_mul_left 全空间变量替换，无需聚合；"需 IntervalIntegral"旧判断否决）；`f0_sub_feps_L1_bound` 仍挂聚合（精确陈述已入列）。`C_MT<4/3` **已于 2026-10-29 真证出账**（纯有理链，√2 消去）。
3. **长线（第一轮攻坚完成 2026-10-27 晚；x=1 口径闭环 2026-10-29）**：(L1) 真实定义件 + (L1b) 两件真证出账（r=1/2 代数桥、trivialTerm 收敛）+ (L1b-C) x=1 边界口径（前提收紧 1<x、约定件两件真证）；(L2) Abel–SW 组装真证出账、SW 本体仍命名 axiom = PNT-in-AP 量级工程；下一步候选：logDerivTerm 导数件（deriv LFun）、SW 本体击破（挂 Ben Green 5 页证明机制核验）。
4. **prime_weight_bounds 降定理已闭环（2026-10-29）**：`prime_weight_bounds_Khat` 真证 + `prime_sum_bound` 特化 K:=Khat（2704 jobs 绿、无 warning）；残余命名 axiom `fourierCos_Khat`（连接件）+ `khat_lipschitz`（光滑件）+ `bgs5_khat_fourier_supp`（积分层窄支撑）。下一步：`khat_lipschitz` 的 L 由解析式可算（K̂ 带限整函数），用导数件可真证（khat_second_order_bound 同款：K̂′ 闭式 + 区间界），并入 S7.1 Stage 3+ 清单。
5. **GitHub**：2026-10-27 已推送 7d77e55（QRH 快照 + d1 文档 + 数值件）；summary 随新提交同步。

## 7. 文件索引

- 文档（d1 根 C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\）：XLII 系列 22 份（S0–S7.12，含 S1a/S1b/S2(i)/S2(ii)/S3/S4/S5/S6 与「全尺度 GUE 配对 S0」）；英文 d1\en\（XLI、XLII-S0、S7.10、S7.11、S7.12 已译 + **arXiv 草稿**（C_MT 已证六处口径，2026-10-29 改进））；前置攻防 XL/XLI（0.6725→7/8 常数机制闭合）。**公式格式惯例（2026-10-27 起）**：d1 文档公式一律 Word 原生 OMML（LaTeX→MathML→OMML 管线，可编辑），禁 LaTeX 源码文本。
- 数值件（qrh_work\、new-chat\xlii_work\）：xlii_s7g_sw_constant.py/json/log、xlii_s7g_fig.py/png、xlii_s7f_bone1/2.py/json/fig、xlii_s7f_supersupport.py/json、xlii_s7_prime.json、xlii_s6_lambda.py/json；s7X 文档生成脚本（gen_s7_7_doc.py 含 OMML 支持）+ render-s7X\ 权威渲染。
- Lean：见 §5。
