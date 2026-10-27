# -*- coding: utf-8 -*-
"""攻防 XLI 英文版：复制原 docx 为 EN 目标，逐段/单元格翻译，替换图 1 为英文版图"""
import re, shutil
from docx import Document
from docx.shared import Cm
from docx.oxml.ns import qn

SRC = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"
DST = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证-EN.docx"
EN_IMG = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work\fig1_A_scan_en.png"

shutil.copy(SRC, DST)

T = {
"路2攻防XLI—拟随机并集定理的常数机制闭合：":
"Offense XLI—Closure of the Constant Mechanism of the Pseudorandom Union Theorem:",
"QRH 攻坚 0.6725→7/8 的最优核数值构造":
"Numerical Construction of the Optimal Kernel in the QRH Push 0.6725→7/8",
"与前提可靠性三层论证":
"and a Three-Tier Reliability Argument for the Premise",
"——《谱对偶论证》系列（d1）：弱前提条件定理形态":
"—Spectral Duality Arguments series (d1): weak-premise conditional theorem form",
"2026 年 10 月 24 日": "October 24, 2026",
"摘要：": "Abstract:",
"攻防 XLI 闭合 QRH 常数机制攻坚第一阶段（数值定向 #1-#8）。三件判定：(i) 变分机制（Lamzouri Proposition 2.1 全文回读）：在线比例 N₀ˢ/N ≥ 2−A，A=ΣK²/Σ1 为配对常数；C_MT=1.3275 是谱支撑 λ≤1/2 核族内的无条件极小（Lemma 3.2、Remark 3.4）；Z_T 元素实值确认配对和是实轴口径。(ii) 最优核数值构造（audit6 核族×尺度扫描）：单族 A 最小 =1.0079（ζ）/1.0114（L），核为 fejer_a0.5（最近邻尺度窄核）——低于 C_MT=1.3275 且低于 7/8 门槛 1.125，余量 0.11-0.12；MT 最优核实测 1.1868/1.2494 亦低于 C_MT——GUE 排斥压低配对常数在数据层面成立；并集 A 最小 =1.2859>1.125——并集直接论证判负，必须走分解论证（两族分别 Proposition 2.1 + 加权，并集拟随机在线比例 ≈0.990）。(iii) 前提可靠性三层（audit8+#7 文献核实）：前提从不可验证的 GUE 整体假设弱化为可直接数值检验的 A≤1.125；5 段子区间统计量单调稳定、最优核 A 漂移 ≤0.005；最近邻分布与 Wigner 在 ~5% 内吻合、长尾无异常；Odlyzko（10²² 高度 GUE 确认）、Rubinstein（Katz–Sarnak 数值验证）、Özlük（GRH 下 Dirichlet L 11/12 简单）构成文献先例。L 族配对公式存在性在文献中无无条件版（BGS 推广为框架内开放构造）——定理形态定为纯假设（弱前提）。":
"Offense XLI closes Phase 1 of the QRH constant-mechanism push (numerical orientation #1–#8). Three findings: (i) Variational mechanism (full re-reading of Lamzouri Proposition 2.1): online proportion N₀ˢ/N ≥ 2−A, with A=ΣK²/Σ1 the pair-correlation constant; C_MT=1.3275 is the unconditional minimum within the kernel family of spectral support λ≤1/2 (Lemma 3.2, Remark 3.4); the real-valuedness of the Z_T elements confirms that the pair sum is a real-axis quantity. (ii) Optimal-kernel numerics (audit6 kernel family × scale scan): minimal single-family A = 1.0079 (ζ) / 1.0114 (L), with kernel fejer_a0.5 (narrow kernel at nearest-neighbor scale) — below C_MT=1.3275 and below the 7/8 threshold 1.125, margin 0.11–0.12; the measured MT optimal kernel, 1.1868/1.2494, is likewise below C_MT — GUE repulsion lowering the pair constant holds at the data level; minimal union A = 1.2859 > 1.125 — the direct union argument fails, and the decomposition argument is mandatory (Proposition 2.1 applied to the two families separately plus weighting; pseudorandom union online proportion ≈0.990). (iii) Three-tier premise reliability (audit8 + #7 literature check): the premise is weakened from the unverifiable global GUE hypothesis to A≤1.125, directly checkable numerically; the 5-segment subinterval statistics are monotone-stable, optimal-kernel A drift ≤0.005; the nearest-neighbor distribution matches Wigner within ~5%, no anomalous tail; Odlyzko (GUE confirmation at height 10²²), Rubinstein (numerical verification of Katz–Sarnak), and Özlük (11/12 simplicity for Dirichlet L under GRH) form the literature precedents. No unconditional version of the pair-correlation formula for the L family exists in the literature (the BGS generalization is an open construction within the framework) — the theorem takes the purely conditional (weak-premise) form.",
"关键词：": "Keywords:",
"配对常数；Montgomery–Taylor 变分；拟随机前提；分解论证；弱前提条件定理；可靠性三层":
"pair-correlation constant; Montgomery–Taylor variational problem; pseudorandom premise; decomposition argument; weak-premise conditional theorem; three-tier reliability",
"1　承接与任务": "1　Context and Task",
"攻防 XL 判定 θ_K≥7/8 的缺口在常数（0.6725→0.875 差 0.2025），属 QRH 机制。用户拍板「按实质用处最大化——转 (b) QRH 常数机制攻坚（0.6725→7/8 的唯一现实通道）」，并坚持先做数值定向。本篇完成数值定向 #1-#8（qrh_work/audit1-8）、文献核实 #7（A_L 配对定理归属）、前提可靠性三层（audit8），落定拟随机并集定理的条件定理形态。":
"Offense XL judged that the gap in θ_K≥7/8 lies in the constant (0.6725→0.875, difference 0.2025), of QRH-mechanism type. The user decision: \u201cmaximize substantive utility — switch to (b) QRH constant-mechanism push (the only realistic channel from 0.6725 to 7/8)\u201d, with numerical orientation insisted upon first. This paper completes numerical orientation #1–#8 (qrh_work/audit1-8), literature check #7 (attribution of the A_L pair-correlation theorem), and the three-tier premise reliability argument (audit8), settling the conditional-theorem form of the pseudorandom union theorem.",
"2　变分机制与实轴口径确认": "2　Variational Mechanism and Real-Axis Convention",
"Lamzouri（arXiv:2609.02882v2）Proposition 2.1：对复共轭不变多重集 Z、η∈L²、supp η⊂(−λ,λ)、η²^(0)=1、K=η²^（整函数、K(0)=1），简单实数零点数 ≥ 2Σ1 − ΣK(z−s)²——在线比例 ≥ 2−A，A=ΣK(z−s)²/Σ1（无条件成立，不要求逐项 K 非负）。常数 C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963 是该方法族内的最优（极小）配对常数：Lemma 3.2 构造最优核 η_ε（f₀(x)=cos(√2x)/(√2sin(1/√2))，支撑 [−1/2,1/2]），配对常数 C=Q(0)+2∫₀¹αQ(α)dα（Q=f*f）；Remark 3.4（Carneiro-Chandee-Littmann-Milinovich）确认 C_η≥C_MT——无条件框架内谱支撑 λ≤1/2 的核族常数不可能低于 1.3275。":
"Lamzouri (arXiv:2609.02882v2), Proposition 2.1: for a conjugation-invariant multiset Z, η∈L², supp η⊂(−λ,λ), η²^(0)=1, K=η²^ (entire, K(0)=1), the number of simple real zeros is ≥ 2Σ1 − ΣK(z−s)² — online proportion ≥ 2−A, A=ΣK(z−s)²/Σ1 (unconditional; no termwise nonnegativity of K required). The constant C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963 is the optimal (minimal) pair-correlation constant in this method family: Lemma 3.2 constructs the optimal kernel η_ε (f₀(x)=cos(√2x)/(√2sin(1/√2)), support [−1/2,1/2]), pair constant C=Q(0)+2∫₀¹αQ(α)dα (Q=f*f); Remark 3.4 (Carneiro–Chandee–Littmann–Milinovich) confirms C_η≥C_MT — within the unconditional framework no kernel constant in the family of spectral support λ≤1/2 can fall below 1.3275.",
"实轴口径确认：Z_T={i(ρ−1/2)logT/2π} 对 ρ=1/2+iγ 给出 z=−γ·logT/2π∈ℝ——Proposition 2.1 的配对和 ΣK(z−s)² 在实轴计算（K 偶）。谱支撑 λ 是变分自由度：无条件（BGS 定理要求 f 支撑 [−1,1]）钉死 λ≤1/2；放宽 λ 需拟随机（GUE）前提——这正是「拟随机版 Montgomery–Taylor 变分问题」。":
"Real-axis confirmation: Z_T={i(ρ−1/2)logT/2π} gives z=−γ·logT/2π∈ℝ for ρ=1/2+iγ — the pair sum ΣK(z−s)² of Proposition 2.1 is computed on the real axis (K even). Spectral support λ is the variational degree of freedom: the unconditional case (the BGS theorem requires f of support [−1,1]) pins λ≤1/2; relaxing λ requires the pseudorandom (GUE) premise — precisely the \u201cpseudorandom version of the Montgomery–Taylor variational problem\u201d.",
"3　数值证据链：拟随机前提成立与配对常数压低": "3　Numerical Evidence Chain: The Pseudorandom Premise Holds and the Pair Constant Is Suppressed",
"数值定向 #1-#4（audit1-4，T=6×10⁵，剔除 t<300）：两族族内最近间距统计 GUE 兼容——ζ mean=1.0000/var=0.1651/s-exp=2.03/p(0+)=0.009；L mean=0.9197/var=0.1365/s-exp=1.86/p(0+)=0.012（密度口径 ρ_L=(1/2π)[log(t/2π)+log5−1]）。跨族独立：无共同值（tol=1e-6）、g(r) 逐点归一化 ≈1.05-1.09（无聚集）；换族频率实测 0.7533 vs 独立 GUE 混合模拟 0.7610±0.0066（R=40，z=−1.1σ）/0.7606±0.0057（R=30，z=−1.3σ）——0.753 是两族独立+各自 GUE 排斥的自然值，非拉链伪影。并集整体对照（audit4）：并集最近邻 var=0.4405 vs 独立 GUE 混合 0.4755±0.0088（z=−4.0σ）、p(0+)=0.5396 vs 0.5581±0.0053（z=−3.5σ）——并集比独立 GUE 混合更亚泊松（微弱但显著，方向与 Δ 定律同向）。":
"Numerical orientation #1–#4 (audit1-4, T=6×10⁵, discarding t<300): the within-family nearest-neighbor statistics of both families are GUE-compatible — ζ mean=1.0000/var=0.1651/s-exp=2.03/p(0+)=0.009; L mean=0.9197/var=0.1365/s-exp=1.86/p(0+)=0.012 (density convention ρ_L=(1/2π)[log(t/2π)+log5−1]). Cross-family independence: no common value (tol=1e-6), g(r) pointwise normalized ≈1.05–1.09 (no clustering); observed family-switch frequency 0.7533 vs independent GUE-mixture simulation 0.7610±0.0066 (R=40, z=−1.1σ) / 0.7606±0.0057 (R=30, z=−1.3σ) — 0.753 is the natural value for two independent families each with its own GUE repulsion, not a zipper artifact. Union overall comparison (audit4): union nearest-neighbor var=0.4405 vs independent GUE mixture 0.4755±0.0088 (z=−4.0σ), p(0+)=0.5396 vs 0.5581±0.0053 (z=−3.5σ) — the union is more sub-Poisson than the independent GUE mixture (weak but significant, same direction as the Δ law).",
"数值定向 #5（audit5，固定核）：Fejér 核 A_ζ=1.0565、A_L=1.0808、A_union=1.6230（跨族贡献 0.5535/零点）；sinc A_ζ=1.1880、A_L=1.2473；gauss A_ζ=1.6146、A_L=1.7864——单族实测 A 显著低于 C_MT=1.3275；并集 A_union≫1.125（在线比例仅 0.377）——Proposition 2.1 直接应用于并集被跨族配对压垮（Q(0) 判负的数值版）。":
"Numerical orientation #5 (audit5, fixed kernel): Fejér kernel A_ζ=1.0565, A_L=1.0808, A_union=1.6230 (cross-family contribution 0.5535 per zero); sinc A_ζ=1.1880, A_L=1.2473; gauss A_ζ=1.6146, A_L=1.7864 — single-family measured A significantly below C_MT=1.3275; union A_union≫1.125 (online proportion only 0.377) — direct application of Proposition 2.1 to the union is crushed by cross-family pairings (the numerical version of the Q(0) verdict).",
"表 1　核族 × 尺度扫描的配对常数 A（audit6，δ=logT/2π=2.1175，直方图口径）":
"Table 1　Pair-correlation constant A from the kernel family × scale scan (audit6, δ=logT/2π=2.1175, histogram convention)",
"核": "Kernel",
"在线比例 2−A_ζ": "Online prop. 2−A_ζ",
"判定": "Verdict",
"fejer_a0.5（最优）": "fejer_a0.5 (optimal)",
"单族达标": "Single family OK",
"MT 最优核（数值）": "MT optimal kernel (num.)",
"低于 C_MT": "Below C_MT",
"C_MT（无条件参照）": "C_MT (uncond. ref.)",
"定理界": "Theorem bound",
"图 1　配对常数 A 的核族 × 尺度扫描（audit6）：单族低于 C_MT 与 7/8 门槛，并集直接论证判负":
"Fig. 1　Pair-correlation constant A from the kernel family × scale scan (audit6): single families lie below C_MT and the 7/8 threshold; the direct union argument fails",
"如图 1 所示，读数：(i) 最优核在最近邻尺度（fejer_a0.5，谱支撑 λ_eff≈0.5 类），单族 A_min≈1.008-1.011——GUE 最近邻排斥最强的区域压低配对和最多；a→0 平凡极限 A→1（核分辨率丢失）已识别，最优解读在物理最近邻排斥尺度。(ii) MT 最优核实测 1.1868（ζ）/1.2494（L）< C_MT=1.3275——GUE 数据对紧谱核同样压低配对常数（无条件主项 vs 实测数据的差距）。(iii) 并集 A 最小 =1.2859>1.125——并集直接论证判负确认。":
"As shown in Fig. 1, readings: (i) The optimal kernel sits at the nearest-neighbor scale (fejer_a0.5, spectral support λ_eff≈0.5 type), with single-family A_min≈1.008–1.011 — the region where GUE nearest-neighbor repulsion is strongest suppresses the pair sum the most; the trivial limit A→1 as a→0 (kernel loses resolution) is identified, and the optimal reading lies at the physical nearest-neighbor repulsion scale. (ii) The measured MT optimal kernel, 1.1868 (ζ) / 1.2494 (L) < C_MT=1.3275 — GUE data likewise suppress the pair constant for compact-spectrum kernels (the gap between the unconditional leading term and the measured data). (iii) Minimal union A = 1.2859 > 1.125 — the failure of the direct union argument is confirmed.",
"表 2　单族拟随机在线比例与 7/8 余量（audit6 最优核）":
"Table 2　Single-family pseudorandom online proportion and 7/8 margin (audit6 optimal kernel)",
"族": "Family",
"A_min（核）": "A_min (kernel)",
"在线比例 2−A_min": "Online prop. 2−A_min",
"7/8 门槛 0.875": "7/8 threshold 0.875",
"余量": "Margin",
"1.0079（fejer_a0.5）": "1.0079 (fejer_a0.5)",
"1.0114（fejer_a0.5）": "1.0114 (fejer_a0.5)",
"达标": "met",
"表 2：拟随机（GUE）前提下单族在线比例 ≈0.989-0.992，7/8 余量 ~0.11-0.12——比 audit5 固定核口径（余量 0.04-0.07）更强。常数机制闭合的定量现实性确认。":
"Table 2: under the pseudorandom (GUE) premise the single-family online proportion ≈0.989–0.992, with 7/8 margin ~0.11–0.12 — stronger than the audit5 fixed-kernel convention (margin 0.04–0.07). The quantitative reality of the closure of the constant mechanism is confirmed.",
"4　分解论证与并集在线比例": "4　Decomposition Argument and Union Online Proportion",
"并集 Z_K=Z_ζ∪Z_L 的零点互异（跨族共同值 =0，数值核实）——N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L。分解论证：两族分别应用 Proposition 2.1（谱支撑 λ≤1/2 核族、常数 C_MT），再按零点数加权——并集在线比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K。拟随机前提下（audit6 最优核）：(999354×0.9921+1149836×0.9886)/2149190 ≈ 0.990 ≥ 0.875=7/8——并集达标。跨族配对（交织、无排斥，audit5 的 A_cross_extra≈0.55-1.48）在分解论证中完全绕开——这正是并集直接论证（A_union=1.29-1.62，在线比例 0.377-0.714）与分解论证的本质区分。":
"The zeros of the union Z_K=Z_ζ∪Z_L are mutually distinct (cross-family common values =0, verified numerically) — N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L. Decomposition argument: apply Proposition 2.1 to the two families separately (kernel family of spectral support λ≤1/2, constant C_MT), then weight by zero counts — union online proportion ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K. Under the pseudorandom premise (audit6 optimal kernel): (999354×0.9921+1149836×0.9886)/2149190 ≈ 0.990 ≥ 0.875=7/8 — the union meets the threshold. Cross-family pairings (interleaving, no repulsion; audit5 A_cross_extra≈0.55–1.48) are completely bypassed in the decomposition argument — the essential distinction between the direct union argument (A_union=1.29–1.62, online proportion 0.377–0.714) and the decomposition argument.",
"5　前提可靠性三层说明": "5　Three-Tier Reliability of the Premise",
"第一层（弱化前提）：": "Tier 1 (weakened premise):",
"条件定理前提从「GUE 配对相关（整体、不可验证）」降为「A_ζ,A_L≤1.125（配对常数假设）」——GUE 是充分非必要，配对常数是 audit6 直接数值验证的对象。A≤1.125 门槛数值全段通过（最优核 1.008-1.014）。":
"The conditional-theorem premise is downgraded from \u201cGUE pair correlation (global, unverifiable)\u201d to \u201cA_ζ, A_L≤1.125 (pair-correlation-constant hypothesis)\u201d — GUE is sufficient but not necessary; the pair constant is the object directly verified numerically by audit6. The A≤1.125 threshold passes numerically over the whole range (optimal kernel 1.008–1.014).",
"第二层（子区间收敛 + 反驳扫描）：": "Tier 2 (subinterval convergence + rebuttal scan):",
"表 3　配对常数 A 与最近邻方差随高度收敛（audit8，5 段）":
"Table 3　Pair-correlation constant A and nearest-neighbor variance vs height (audit8, 5 segments)",
"高度段": "Height segment",
"全区间": "Full range",
"判定：所有统计量随高度单调微调、无发散；最优核 A 段间漂移 ≤0.005（A0.5），7/8 余量 0.11-0.12 远大于有限 T 修正。反驳扫描：ζ 最近邻间距带计数 vs GUE Wigner 分布 obs/pred 比值 0.86-1.05（相对偏差 ≤5%，方向为中峰略集中——与精确 GUE/有限 T 修正方向兼容，不作证伪）；长尾 max_s≈3.1-3.4（ζ）≈√(log n) 尺度、无异常长间距；L 受归一化常数影响（nn_mean=0.92）不作精确 band 对照，靠 var/s_exp/A 佐证。跨族独立（audit3/4）+ 并集额外亚泊松（var −4σ，与 Δ 定律同向）——系统性反驳扫描未发现偏离拟随机框架的结构性证据。":
"Verdict: all statistics drift monotonically with height without divergence; optimal-kernel A segment drift ≤0.005 (A0.5), and the 7/8 margin 0.11–0.12 far exceeds finite-T corrections. Rebuttal scan: ζ nearest-neighbor gap-band counts vs GUE Wigner distribution give obs/pred ratio 0.86–1.05 (relative deviation ≤5%, direction slightly central-peaked — compatible with the exact-GUE/finite-T correction direction, not a falsification); tail max_s≈3.1–3.4 (ζ) at ≈√(log n) scale, no anomalous long gaps; L, affected by the normalization constant (nn_mean=0.92), is not used for a precise band comparison, supported by var/s_exp/A. Cross-family independence (audit3/4) plus union extra sub-Poissonity (var −4σ, same direction as the Δ law) — the systematic rebuttal scan finds no structural evidence against the pseudorandom framework.",
"第三层（文献佐证 + 反证框架）：": "Tier 3 (literature support + rebuttal framework):",
"独立文献证据：Odlyzko（10²² 高度、10¹⁰ 个零点）数值验证 GUE 配对相关（「confirmed the GUE connection」）；Rubinstein 数值验证 Katz–Sarnak 猜想；Özlük（1982，GRH 下）证明 Dirichlet L 函数至少 11/12≈0.917 简单——配对方法先例链。反证框架：跨族独立与并集亚泊松（audit4）均与 GUE 拟随机 + Δ 定律一致，未出现算术结构指纹。":
"Independent literature evidence: Odlyzko (height 10²², 10¹⁰ zeros) numerically verifies GUE pair correlation (\u201cconfirmed the GUE connection\u201d); Rubinstein numerically verifies the Katz–Sarnak conjecture; Özlük (1982, under GRH) proves that Dirichlet L-functions have at least 11/12≈0.917 simple zeros — the precedent chain for the pairing method. Rebuttal framework: cross-family independence and union sub-Poissonity (audit4) are both consistent with GUE pseudorandomness + the Δ law; no arithmetic-structure fingerprint appears.",
"6　拟随机并集定理（条件定理形态）": "6　Pseudorandom Union Theorem (Conditional Form)",
"定理（弱前提拟随机并集定理，条件形态）：设 ζ 与 L(χ₅) 的零点在归一化尺度上的配对常数满足 A_ζ,A_L≤1.125（拟随机前提，含 L 族配对公式存在性假设；数值最优核实测 A_ζ=1.0079、A_L=1.0114）。则并集在线简单零点比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K ≥ 7/8。":
"Theorem (weak-premise pseudorandom union theorem, conditional form). Let the pair-correlation constants of the zeros of ζ and L(χ₅) on the normalized scale satisfy A_ζ, A_L≤1.125 (pseudorandom premise, including the existence hypothesis of the pair-correlation formula for the L family; measured optimal kernels A_ζ=1.0079, A_L=1.0114). Then the union online simple-zero proportion is ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K ≥ 7/8.",
"证明骨架：(i) N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L（零点互异，已核实）；(ii) 两族分别应用 Proposition 2.1：N₀ˢ_ζ≥2N_ζ−ΣK²_ζ、N₀ˢ_L≥2N_L−ΣK²_L（无条件不等式，K=η²^、K(0)=1）；(iii) 拟随机前提 ⟹ ΣK²_ζ≤A_ζN_ζ、ΣK²_L≤A_LN_L；(iv) 代入加权即得。分解论证的关键：跨族配对完全不进入（与并集直接论证的 A_union=1.29-1.62 判负形成对照）。":
"Proof skeleton: (i) N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L (zeros distinct, verified); (ii) apply Proposition 2.1 separately: N₀ˢ_ζ≥2N_ζ−ΣK²_ζ, N₀ˢ_L≥2N_L−ΣK²_L (unconditional inequalities, K=η²^, K(0)=1); (iii) the pseudorandom premise ⟹ ΣK²_ζ≤A_ζN_ζ, ΣK²_L≤A_LN_L; (iv) substitute and weight. The key point of the decomposition argument: cross-family pairings never enter (in contrast with the failing direct union argument, A_union=1.29–1.62).",
"7　诚实边界": "7　Honest Boundaries",
"① A 的实测值是数据（T=6×10⁵）非定理——A≤1.125 前提未证明，定理为纯假设形态。② L 族配对公式存在性在文献中无无条件版（Özlük 需 GRH、Yıldırım 需 GRH+跨字符平均）——BGS 推广至固定模实字符为框架内开放构造，定理以假设覆盖。③ band 检验的 z 值因归一化常数效应不作精确判定（量级佐证）。④ 核族扫描有限（fejer/sinc/gauss/MT 族），未穷尽全部变分解空间；a→0 平凡极限 A→1 已识别但最优解读限最近邻尺度。⑤ δ 尺度与 R 截断的有限 T 效应已部分标定（子区间收敛），跨 T 外推需更大数据。⑥ 并集分解论证的加权系数 N_ζ/N_K=0.465、N_L/N_K=0.535 来自 T=6×10⁵ 实测。":
"\u2460 The measured A is data (T=6×10⁵), not a theorem — the premise A≤1.125 is unproved; the theorem is purely conditional. \u2461 No unconditional version of the L-family pair-correlation formula exists in the literature (Özlük needs GRH; Yıldırım needs GRH + cross-character average) — the BGS generalization to a fixed-modulus real character is an open construction within the framework, covered by hypothesis in the theorem. \u2462 The band-test z-values are not used for precise verdicts because of the normalization-constant effect (order-of-magnitude support only). \u2463 The kernel-family scan is finite (fejer/sinc/gauss/MT families), not exhausting the full variational solution space; the trivial limit A→1 as a→0 is identified, but the optimal reading is restricted to the nearest-neighbor scale. \u2464 Finite-T effects of the δ scale and the R truncation are partially calibrated (subinterval convergence); extrapolation in T requires larger data. \u2465 The weights N_ζ/N_K=0.465, N_L/N_K=0.535 in the union decomposition come from the T=6×10⁵ measurement.",
"8　判定总结": "8　Verdict and Summary",
"攻防 XLI 闭合 QRH 攻坚第一阶段。(1) 变分机制确认：C_MT=1.3275 是 λ≤1/2 核族无条件极小，0.6725 是配对常数路径的无条件极限；(2) 最优核数值构造：拟随机下单族 A_min≈1.008-1.011（fejer_a0.5）、在线比例 ≈0.99、7/8 余量 0.11-0.12——常数机制闭合的定量现实性确认；(3) 并集直接论证判负（A_union_min=1.286）、分解论证达标（并集 ≈0.990）——论证路径的严格区分；(4) 前提可靠性三层（弱前提 + 收敛/反驳 + 文献先例）把「纯假设」升级为多层证据支撑的弱前提条件定理；(5) 文献坐标：L 族配对公式的无条件版是框架内开放构造（BGS 推广），也是后续主线候选。主线下一步候选：(a) 分解论证严格化（两族 Proposition 2.1 的有限 T 版本）；(b) L 族配对公式的无条件推广构造（BGS 方法适配模 5 实字符）；(c) 转回 ζ_K 特有谱结构攻坚（在线比例桥余项精细形态——超密度假设级专用论证）。":
"Offense XLI closes Phase 1 of the QRH push. (1) Variational mechanism confirmed: C_MT=1.3275 is the unconditional minimum of the λ≤1/2 kernel family; 0.6725 is the unconditional limit of the pair-correlation-constant path. (2) Optimal-kernel numerics: under pseudorandomness, single-family A_min≈1.008–1.011 (fejer_a0.5), online proportion ≈0.99, 7/8 margin 0.11–0.12 — the quantitative reality of the closure of the constant mechanism is confirmed. (3) The direct union argument fails (A_union_min=1.286) while the decomposition argument meets the threshold (union ≈0.990) — a strict separation of argument paths. (4) The three-tier premise reliability (weak premise + convergence/rebuttal + literature precedents) upgrades \u201cpurely conditional\u201d to a weak-premise conditional theorem supported by multiple tiers of evidence. (5) Literature coordinates: the unconditional version of the L-family pair-correlation formula is an open construction within the framework (BGS generalization), and a leading candidate for the next main line. Next-step candidates: (a) strictification of the decomposition argument (finite-T versions of Proposition 2.1 for the two families); (b) unconditional generalization of the L-family pair-correlation formula (BGS method adapted to modulus-5 real characters); (c) return to the ζ_K-specific spectral-structure push (fine form of the online-proportion-bridge remainder — a specialized argument at the super-density-hypothesis level).",
"参考文献": "References",
"[1] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（Proposition 2.1（N₀ˢ≥2Σ1−ΣK²）、Lemma 3.2（最优核 f₀(x)=cos(√2x)/(√2sin(1/√2))、C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963）、Remark 3.4（C_η≥C_MT 最优性））——全文回读.":
"[1] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2 (Proposition 2.1 (N₀ˢ≥2Σ1−ΣK²), Lemma 3.2 (optimal kernel f₀(x)=cos(√2x)/(√2sin(1/√2)), C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963), Remark 3.4 (C_η≥C_MT optimality)) — read in full.",
"[2] Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（Lemma 5：无条件配对公式、误差 O_f(1/√logT)、权 w(z)=4/(4−z²)；BGS 推广至固定模 L(χ) 为开放构造）.":
"[2] Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799 (Lemma 5: unconditional pair-correlation formula, error O_f(1/√logT), weight w(z)=4/(4−z²); the BGS generalization to fixed-modulus L(χ) is an open construction).",
"[3] Özlük A E. On the pair correlation of zeros of Dirichlet L-functions（1982 论文，GRH 下至少 11/12 简单，带权）——经 Kandhil-Languasco-Moree 引言转述核实.":
"[3] Özlük A E. On the pair correlation of zeros of Dirichlet L-functions (1982; at least 11/12 simple under GRH, with weight) — verified via the introduction of Kandhil–Languasco–Moree.",
"[4] Kandhil N, Languasco A, Moree P. Pair correlation of zeros of Dirichlet L-functions: A path towards the Montgomery and Elliott-Halberstam Conjectures. arXiv:2411.19762（Yıldırım 定理/Conjecture 1：跨字符平均配对相关，GRH 前提）——全文精读.":
"[4] Kandhil N, Languasco A, Moree P. Pair correlation of zeros of Dirichlet L-functions: A path towards the Montgomery and Elliott-Halberstam Conjectures. arXiv:2411.19762 (Yıldırım theorem / Conjecture 1: cross-character-average pair correlation, GRH premise) — read in full.",
"[5] Carneiro E, Milinovich M B, Ramos A P. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913（F 平均 0.9303-1.3208、含 Dirichlet L 函数族）.":
"[5] Carneiro E, Milinovich M B, Ramos A P. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913 (F-average 0.9303–1.3208, including Dirichlet L-function families).",
"[6] Odlyzko A M. The 10^22-nd zero of the Riemann zeta function（10¹⁰ 个零点数值验证 RH 与 GUE 配对相关——「confirmed the GUE connection」）.":
"[6] Odlyzko A M. The 10^22-nd zero of the Riemann zeta function (10¹⁰ zeros; numerical verification of RH and GUE pair correlation — \u201cconfirmed the GUE connection\u201d).",
"[7] QRH 攻坚数值件（本工作，Anaconda python 可复跑）：qrh_work/qrh_audit1-8.py/.json（拟随机前提统计、跨族独立、并集亚泊松、配对常数核族扫描、子区间收敛）；零点数据 zeros_T6e5.npz（T=6×10⁵、ζ 999492/L 1150050 根）.":
"[7] QRH-push numerical package (this work; reproducible with Anaconda python): qrh_work/qrh_audit1-8.py/.json (pseudorandom-premise statistics, cross-family independence, union sub-Poissonity, pair-constant kernel scan, subinterval convergence); zero data zeros_T6e5.npz (T=6×10⁵, ζ 999492 / L 1150050 roots).",
"[8] 攻防 XL（d1 已交付）：配对侧无条件界理论构造——0.6725 常数缺口 0.2025 属 QRH 机制；攻防 XXXIX（S4）：在线比例桥余项精细形态.":
"[8] Offense XL (d1 delivered): theoretical construction of the unconditional bound on the pairing side — the 0.6725 constant gap 0.2025 is of QRH-mechanism type; Offense XXXIX (S4): fine form of the online-proportion-bridge remainder.",
}

def norm(s):
    return re.sub(r"\s+", " ", s.strip())

T = {norm(k): v for k, v in T.items()}

def set_para_text(p, new_text):
    runs = p.runs
    if not runs:
        p.add_run(new_text)
        return
    first = runs[0]
    first.text = new_text
    for r in runs[1:]:
        r._r.getparent().remove(r._r)

doc = Document(DST)

# ---- 1. 图片替换（含 drawing 的段落）----
img_done = 0
for p in list(doc.paragraphs):
    for r in list(p.runs):
        if r._r.find(qn("w:drawing")) is not None:
            p._p.remove(r._r)
            img_done += 1
    if img_done and p._p.find(qn("w:drawing")) is None and p.text == "":
        # 原图片段已清空：加入英文图（段落格式居中/keep_with_next 保留）
        p.add_run().add_picture(EN_IMG, width=Cm(12.9))
        img_done = 0
        break
print("image replaced: 1" if img_done == 0 else "image NOT replaced")

# ---- 2. 正文段落翻译 ----
matched = 0
unmatched_cjk = []
for p in doc.paragraphs:
    txt = p.text
    if not txt.strip():
        continue
    key = norm(txt)
    if key in T:
        set_para_text(p, T[key])
        matched += 1
    else:
        import unicodedata
        if any("\u4e00" <= ch <= "\u9fff" for ch in txt):
            unmatched_cjk.append(key)

# ---- 3. 表格单元格翻译 ----
for tb in doc.tables:
    for row in tb.rows:
        for cell in row.cells:
            for p in cell.paragraphs:
                txt = p.text
                if not txt.strip():
                    continue
                key = norm(txt)
                if key in T:
                    set_para_text(p, T[key])
                    matched += 1
                else:
                    import unicodedata
                    if any("\u4e00" <= ch <= "\u9fff" for ch in txt):
                        unmatched_cjk.append(key)

doc.save(DST)
print("matched paragraphs/cells:", matched)
print("unmatched CJK paragraphs:", len(unmatched_cjk))
for u in unmatched_cjk:
    print("  MISS:", u[:80])
print("SAVED", DST)
