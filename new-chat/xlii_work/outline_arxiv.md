# outline_arxiv.md — arXiv 论文大纲（QRH「干到 1」整理稿）

## 论文形态
- 标题：On the single-family pairing constant for L(s, χ₅): conditional bounds, numerical evidence, and a Lean 4 formalization
- 分类：Mathematics – Number Theory (math.NT)
- 载体：英文（docx OMML 公式 → 后续可转 LaTeX/PDF 提交 arXiv）
- 作者：Liu Xudong Wangfang （占位，合作者待定）；背书由用户联系合作者
- 定位：conditional theorem 论文——主定理显式声明依赖假设，数值 + 形式化作附录；诚实披露所有 axiom 挂账

## 结构
0. Abstract（目的/方法/结果/诚实边界）
1. Introduction
   - QRH 常数机制：0.6725 = 2 − C_MT；7/8 目标；A ≤ 1.125 ⟺ 7/8 通道
   - 战略：单族配对常数 A(λ) → 1（统计水平结构；≠ 接近 RH，口径声明）
   - 贡献三件：条件定理（Thm 1）、数值证据链、Lean 4 形式化（2604 绿）
2. Notation and standing assumptions
   - A_L(K) = 1 + Σ_{Δ≠0} K(δΔ)²/N_Z，δ = logT/(2π)；核族 λ≤1/2（BGS 引理 5 支撑）；K(0)=1
   - 假设 H1（L 族 BGS 型配对公式——文献无无条件版，显式假设，诚实披露）；H2（Siegel–Walfisz 模 5，Kadiri/Bordignon 无条件显式）；H3（Landau 显式公式 L 版 + 弱实部假设 |β−1/2|<1/(2logT)）
3. The pairing constant and the kernel family
   - Lamzouri Prop 2.1（N₀ˢ ≥ 2Σ1 − ΣK²，无条件不等式）；C_MT = 1/2 + (1/√2)cot(1/√2) = 1.3274992963；Lemma 3.2 最优核 f₀ = cos(√2x)/(√2 sin(1/√2))；Remark 3.4（C_η ≥ C_MT 最优性）
   - Fejér 窄核（fejer_a0.5）合法性说明（防「窄核自欺欺人」质询）
4. Main theorem
   - Thm 1（s71_main 形态）：弱实部假设 + H1–H3 ⟹ A_L(K) ≤ C_MT + C₁ε + C₂，C₂ = 2 显式
   - Corollary（0.6725 严格化）：并集在线比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K ≥ 2 − (C_MT+O(ε)) − o(1)；A≤1.125 ⟹ ≥ 7/8
5. Proof skeleton
   - pair_sum_expansion：A_L = diag + prime + offcrit；diag ≤ C_MT + C₁ε（n2_linkage）；|prime|,|offcrit| ≤ 1 并入 C₂
   - Yildirim (6) L 版（Landau 型显式公式，无条件）；(7) 积分形式（弱实部假设下）
   - 素数项：SW（模 5，c = 1/√6.3970 = 0.3954，C 由 Bordignon 表 2）→ O(e^{−c√logT}) 子指数
   - 离线项：T^{3/8} 切割（BGS 引理 4 机制）→ o(1)
6. Numerical evidence
   - 表 1：核族×尺度扫描（fejer_a0.5 最优：A_ζ=1.0079、A_L=1.0114、A_union=1.2859）；MT 最优核 1.1868/1.2494 < C_MT
   - 窄核专项推进 A ≈ 0.990；5 子区间漂移 ≤ 0.005；外推假设声明
   - 件 E：|S| ≤ 0.128，相对 N_L ~4×10⁻⁸（X=10⁷ 双 T）；件 G：|ψ(X,χ₅)|/X ≤ 1.70×10⁻³；件 F：|S_a| ≈ 2.05，|S_a|/N_L → 1×10⁻⁸
7. Robustness checks（威胁排除）
   - S2(i) 实部口径注入敏感性（N_off·δ²·λ² 累积可测性）；S3 Δ 常数指纹爆炸响应；左尾 224 审计
   - 跨族独立（换族频率 0.7533 vs GUE 混合 0.761）；并集亚泊松（var −4σ）
8. The super-support regime and A→1
   - 理论断层：λ_eff = (logT)^q → ∞ vs S7 闭路 λ≤1/2；N1（引理 5 超支撑推广）、N2（ε–λ 联动）、N3（离线项一致版本）
   - SW 常数显式化定理（N3.5）：c = 0.3954、C 显式、L(1,χ₅) = 0.430409 > 0、无 Siegel 零点
9. Lean 4 formalization（附录 A）
   - 工程：C:\proj2\QRH，Core→Main→Stage3；26 件真证；挂账 axiom 清单（landau_explicit_L / siegel_walfisz_chi5 / bgs3-5 / fourierCos_scale 等）；2604 jobs 全绿；诚实披露：主定理链在命名 axiom 下成立，axiom 清零为长线
10. Conclusion（贡献、诚实边界、下一步：logDerivTerm、SW 本体、PCC→A→1）

## 引用核查表（全部已联网核实 2026-10-27）
| 引用 | 核实状态 | 来源 URL |
|---|---|---|
| Yildirim 1991, manuscripta math 72(1): 325–334 | 已核实（CORE PDF；作者 C. Yalin Yildirim） | https://core.ac.uk/download/52936553.pdf |
| Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, arXiv:2306.04799 | 已核实（摘要：61.7% 简单、弱假设、T^{3/8}） | https://arxiv.org/pdf/2306.04799 |
| Murty–Zaharescu, Forum Math. 14 (2002) 65–83 | 已核实（Queen's PDF 直达） | https://mast.queensu.ca/~murty/Murty-Zaharescu.pdf |
| Lamzouri, arXiv:2609.02882v2 | 已核实（Prop 2.1、Lemma 3.2、Remark 3.4） | https://arxiv.org/pdf/2609.02882 |
| Bordignon, arXiv:2101.08610（Thm 1: R₀=6.3970, R₁=2.0452） | 已核实（原文精读） | https://arxiv.org/pdf/2101.08610 |
| Kadiri（经 Bordignon Thm 1 引用；Mathematika 2018 版 R=5.60 为更新常数） | 已核实（Bordignon 引用口径为准） | https://arxiv.org/pdf/math/0510570 |
| Ramaré–Rumely, Math. Comp. 65(213): 397–425 | 已核实 | https://ramare-olivier.github.io/Maths/rumely.pdf |
| Kandhil–Languasco–Moree, arXiv:2411.19762 | 已核实 | https://arxiv.org/pdf/2411.19762 |
| Carneiro–Milinovich–Ramos, arXiv:2310.01913 | 已核实（XLI 引用） | https://arxiv.org/abs/2310.01913 |
| Montgomery 1973, Proc. Sympos. Pure Math. 24: 181–193 | 经典文献（公开可查） | — |
| Ben Green 5 页证明 | 未核实到篇目（5 页简化版实为 Bryce Kerr arXiv:2610.21099）——**不引用** | — |

## 诚实边界（必须写入）
- 主定理依赖 H1（L 族 BGS 型配对公式无文献无条件版，显式假设）
- A 是数据非定理；数值外推依赖「全局均值不剧变」假设
- Lean 侧 axiom 挂账清单如实披露
