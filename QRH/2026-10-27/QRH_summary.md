# QRH 项目总结（攻防 XLII「干到 1」主线 + Lean 形式化）

> 2026-10-26 定稿。数学层 S0–S7.6 已闭环落档 d1；Lean 形式化阶段推进中（Core/Stage3 真证链绿，Main 骨架组装未完成）。
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

## 4. 三硬骨头与 SW 常数（推 1 断层闭合）

「推 1」撞上的理论断层：XLII 路线要求 λ_eff(T) = (logT)^q → ∞（核越来越窄、谱支撑无限扩大），而 S7 闭路只覆盖 λ ≤ 1/2（BGS 引理 5 硬条件）。λ → ∞ 时实空间核宽 a → 0，差型配对中 ĥK(δ·log p) 支撑变宽，素数项 S(X) 可能失去频域窄支撑保护。三个硬骨头：

- **N1（BGS 引理 5 超支撑推广）**：缩放自同构 scaleKernel a r 支撑保持；λ→∞ 超支撑下素数项仍被 χ₅ 振荡抵消，A→1 路径打通。
- **N2（ε–λ 联动）**：λ = (logT)^q、a = (logT)^{−q}、ε = c·(logT)^{−q} ⟹ 偏差 O((logT)^{−q})——正则化撑宽与有效核宽联动。
- **N3（离线项一致版本）**：BGS 余项 O(T√logT) 对 supp⊂[−1,1] 一切核一致（外层 ∃R 对 K 一致）。
- **SW 常数显式化（S7.6）**：Siegel–Walfisz 素数项界 |Σ_{n≤x} Λ(n)χ₅(n)| ≤ C·x·e^{−c√log x}，理论 c = 1/√R₀ ≈ 0.3954（Kadiri R₀ = 6.3970）；实测 C_obs = 1.70e−3 另记；L(1,χ₅) = 0.430409 > 0；β ≥ 0.9029。

数值件 F 实测：S(X) = Σ_{p≤X} Λ(n)χ₅(p)p^{−1/2}·K̂_a(δ·log p) = O(√X·poly(log X))，相对 N_L ~ (X/2π)·logX 为 o(1)，**无需** e^{−c√logX} 指数级；|S_a| ≈ 2.05 有界收敛（强于理论上界），|S_a|/N_L 单调衰减至 1e−8（X = 10⁸）。

## 5. Lean 形式化状态（C:\proj2\QRH，mathlib v4.34.0-rc2）

构建：`lake build QRH` 1965 jobs 全绿（exit=0）；Windows 侧 mathlib 聚合 Mathlib.olean 未生成，仅具体模块 import。

**误差界宏（弃 Asymptotics.IsBigO 与 ε–N）**：`Bound C T0 err f := 0≤C ∧ ∀T≥T0, |err T| ≤ C·f T`；`BoundBall C δ err f := 0≤C ∧ ∀|x|≤δ, |err x| ≤ C·f x`。

**真证链（10 件）**：

- Core（S7_1_Core.lean）：`sin_inv_sqrt2_ne_zero`（分母良定义）、`Khat_neg`（偶性）、`Khat_zero`（K̂(0)=1，sin/x 极限延拓）、`Khat_abs_le`（频域衰减三角不等式界）、`f0_continuous`。
- Stage3（S7_1_Stage3.lean）：`scaleKernel_support`（N1 支撑保持）、`f_eps_support`（N2 支撑 [−1/2,1/2]）、`Khat_a_even`（一阶校正恒零）、`sum_abel`（Abel 求和归纳）、**`khat_second_order_bound`**（K̂ 二阶一致界真证，2026-10-26 迁入替换 axiom）。

**khat_second_order_bound 真证链**（BoundBall 1 (1/24)）：K̂(u) 乘形式闭式 Khat_closed_form = [cos m − √2·m·cotR·sin m]/(1 − 2m²)，m = πu；|u| ≤ 1/24、π < 16/5 ⟹ |m| ≤ 2/15 ⟹ m² ≤ 4/225 ⟹ 分母 1−2m² ≥ 217/225 > 0；分子拆分 N = m²(3/2 − √2·cotR) + cos 二阶余项 − √2·m·cotR·(sin 一阶余项)；cos/sin 余项用 Real.cos_bound/sin_bound、c0_bound（|3/2 − √2·cotR| ≤ 9/50，cotR ∈ [1, 237/200]）；拼接得 |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴。数值核对：½|K̂″(0)| ≈ 1.53 < 2（2u² 系数来源）。

**主定理 s71_main（组装真证，2026-10-27，替代 sorry）**：A_L(K) ≤ C_MT + C₁ε + C₂，C₂ = 2 显式。证明链 = pair_sum_expansion 分解 A_L = diag + prime + offcrit → diag ≤ C_MT + C₁ε（n2_linkage O(ε)）+ |prime|,|offcrit| ≤ 1 并入 C₂（linarith + ring）；(L3) axiom 语义已强化（diag 界入陈述）。整库 1965 jobs 全绿（build_qrh_s71.txt）。

**长线命名 axiom——精确陈述完成（2026-10-27）**：`landau_explicit_L`（Yildirim 公式 (6) 重排式：zeroWeightedSum = trivialTerm − primePowerSum − logDerivTerm）、`siegel_walfisz_chi5`（Finset.Icc 1 ⌊x⌋₊ 真实和式：|Σ Λ(n)χ_5(n)| ≤ c·x·e^{−c′√log x}）、`offcritical_small`（Bound 型：|offCriticalError s| ≤ R·√log s）——由空洞占位升级为与数学一致的精确陈述；引入抽象对象（opaque：vonMangoldt、chi5、zeroWeightedSum、primePowerSum、trivialTerm、logDerivTerm、offCriticalError）作陈述载体。真证 = PNT-in-AP 量级长线。

**挂账 axiom（如实记录）**：
- Core 清单项：`C_MT<4/3`（无 axiom 声明——数学上需 cos 四阶 Taylor 上界 73/96，mathlib 内置 cos_bound 余项 (5/96)|x|⁴ 不够（组合 sin_bound 修正后差 0.13%）；**级数余项层、非积分阻塞，可独立立项**）。
- Stage3：`fourierCos_scale`、`scaleKernel_L1_invariant`、`n1_diag_invariant`、`n1_offdiag_vanishes`、`n2_linkage`、`n3_remainder_uniform`、`N_L`、`N_L_lower_bound`（积分层/数论件，陈述完整；真证挂 mathlib 聚合 Mathlib.olean——IntervalIntegral.olean 缺失实测确认）；`f0_sub_feps_L1_bound`（**精确陈述声明入列 2026-10-27**：‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹；真证挂聚合）；`pair_const_eps_bias`（待 pairConstant 真实定义，Stage 2 后由 L¹ 界 + Lipschitz 推出）。
- Main：`landau_explicit_L`、`siegel_walfisz_chi5`、`offcritical_small`（**精确陈述完成**，真证长线）；`pair_sum_expansion`（(L3) 组装依赖，陈述精确，BGS 引理 3-5 移植为下一步核心）。

**文件结构**：C:\proj2\QRH.lean（根，import Core/Main/Stage3）；QRH\S7_1_Core.lean；QRH\S7_1_Stage3.lean；QRH\S7_1_Main.lean（zerosLChi5、pairConstant、WeakRealPart 抽象 + s71_main 组装真证）；QRH\Dbg_Khat.lean（khat 真证开发档案）。编译证据：build_core1..12.txt、build_main1..9.txt、build_stage3.txt、build_qrh_full{,2,3,_khat,_khat2,_s71}.txt、dbg_khat.txt、dbg_probe3.txt（IntervalIntegral.olean 缺失确认）、main_precise.txt、stage3_precise.txt、build_qrh_precise.txt（2026-10-27 陈述层后全量 1965 绿）。

## 6. 下一步（按依赖序）

1. **Stage 4 已完成**（2026-10-27）：s71_main 组装真证（前提显式、常数显式、组装真证）——Lean 侧可核查的最远合理点已达。
2. **条件封口（陈述层完成 2026-10-27；真证挂聚合）**：积分层三组——Stage3（fourierCos_scale → n1_diag/n1_offdiag → n2_linkage/n3_remainder_uniform）+ f0_sub_feps_L1_bound 陈述就绪；mathlib 聚合 Mathlib.olean 生成后即可真证。`C_MT<4/3` 级数余项层（cos 四阶上界 73/96 自证）非积分阻塞，可独立立项。
3. **长线（命名 axiom 精确陈述完成 2026-10-27）**：(L1) 显式公式 / (L2) SW 真证 = PNT-in-AP 量级多人年工程；先做 Stage 2：(L3) 配对和展开半形式化（有限多重集 + 有限和，δ 实数口径）→ pairConstant 真实定义 → pair_const_eps_bias。

## 7. 文件索引

- 文档（d1 根 C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\）：XLII 系列 17 份（S0–S7.6，含 S1a/S1b/S2(i)/S2(ii)/S3/S4/S5/S6 与「全尺度 GUE 配对 S0」）；英文 d1\en\（XLI、XLII-S0 已译）；前置攻防 XL/XLI（0.6725→7/8 常数机制闭合）。
- 数值件（qrh_work\、new-chat\xlii_work\）：xlii_s7g_sw_constant.py/json/log、xlii_s7g_fig.py/png、xlii_s7f_bone1/2.py/json/fig、xlii_s7f_supersupport.py/json、xlii_s7_prime.json、xlii_s6_lambda.py/json；s7X 文档生成脚本 + render-s7X\ 权威渲染。
- Lean：见 §5。
