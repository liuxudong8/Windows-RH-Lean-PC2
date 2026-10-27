# 攻防 XLI 落档大纲（d1 惯例 · 无模板新建）

## 任务
用户拍板：QRH 攻坚（0.6725→7/8）已完成数值定向 #1-#8（qrh_work/audit1-6/8），#7 文献核实判定 A_L 归属，"d1 惯例落档"攻防 XLI。
本文档：拟随机并集定理的常数机制闭合——弱前提条件定理形态 + 前提可靠性三层论证。

## 交付
- 目标：`D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx`
- 管线：xxx11_work/gen_docx_xli.py → run_all.py（generate+audit+render+catalogue+read）
- 风格：论文级排版（可读纯文本+下标、禁 LaTeX）；标题 18pt 黑体三行拆分（XL 教训：避免超版心折行）；黑体标题/宋体正文/Times New Roman 西文；页码脚注居中

## 章节结构与数值依据（全部回读 qrh_work JSON）
1. 承接与任务：XL 判定（常数缺口 0.2025 属 QRH 机制）→ audit1-8 链条 → 本篇落定条件定理形态
2. 变分机制与实轴口径确认：Lamzouri Prop 2.1（N₀ˢ≥2Σ1−ΣK²）、C_MT=1.3275 最优（Lemma 3.2/Remark 3.4）、Z_T 实值⟹实轴口径、λ 支撑自由度（无条件 λ≤1/2 钉死 C_MT；放宽 λ 需拟随机）
3. 数值证据链：audit1-4（两族族内 GUE、跨族独立 z=−1.3σ、并集亚泊松 var −4σ）；audit5 固定核（fejer A_ζ=1.0565/A_L=1.0808/A_union=1.6230）；audit6 最优核扫描（A_min=1.0079/1.0114；MT 核 1.1868/1.2494<1.3275；union 1.2859>1.125）
4. 分解论证：N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L（common=0）⟹ 并集 ≥ 加权(2−A_ζ,2−A_L)≈0.990
5. 前提可靠性三层：①弱化前提（A≤1.125 直接数值验证）②子区间收敛+反驳扫描（5 段 A 漂移≤0.005、band ~5% 内吻合、max_s≈√(log n)）③文献佐证+反证框架（Odlyzko/Rubinstein/Özlük；跨族独立+并集亚泊松）
6. 拟随机并集定理（条件定理正式形态：前提/结论/骨架/边界）
7. 诚实边界：A 数值非定理、L 配对公式存在性假设、band z 不作精确判定、T=6e5、a→0 平凡极限
8. 判定总结与主线下一步

## 表格（数值=audit6/audit8 JSON 精确值）
- 表1 核族扫描 A：fejer_a0.5（ζ 1.0079/L 1.0114/union 1.2859）、sinc_a0.5（1.0492/1.0639/1.4720）、fejer_a1.0（1.0565/1.0807/1.6227）、gauss_a0.5（1.1269/1.1773/1.8902）、MT 核（1.1868/1.2494/2.0562）
- 表2 单族在线比例与余量：ζ A_min=1.0079→0.9921、L=1.0114→0.9886；7/8 余量 0.1171/0.1136
- 表3 子区间收敛：5 段 ζ/L 的 A0.5、A1.0、nn_var（audit8 full/segs）

## 引用核查表（均已核实，来源 URL 为搜索/精读证据）
| 引用 | 编号 | 年份 | 核实状态 | 来源 URL |
|---|---|---|---|---|
| Lamzouri: more than 2/3 zeros simple & critical | arXiv:2609.02882v2 | 2026 | 已核实（全文回读：Prop 2.1、Lemma 3.2、C_MT、Remark 3.4）| https://arxiv.org/html/2609.02882v2 |
| Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh: unconditional Montgomery | arXiv:2306.04799 | 2023 | 已核实（Lemma 5：无条件配对公式、误差 O_f(1/√logT)）| https://arxiv.org/html/2306.04799v1 |
| Özlük: Dirichlet L 配对相关（GRH 下 11/12 简单）| 1982 thesis | 1982 | 已核实（经 2411.19762 引言转述）| https://arxiv.org/html/2411.19762v1 |
| Kandhil-Languasco-Moree: pair correlation Dirichlet L-functions | arXiv:2411.19762 | 2024 | 已核实（全文精读：Yıldırım 定理/Conjecture 1、GRH 前提）| https://arxiv.org/html/2411.19762v1 |
| Carneiro-Milinovich-Ramos: Fourier optimization & PCC | arXiv:2310.01913 | 2023 | 已核实（F 平均 0.9303-1.3208、含 Dirichlet 族）| https://arxiv.org/pdf/2310.01913 |
| Odlyzko: The 10^22-nd zero（10¹⁰ 零点 GUE 数值验证）| — | 2000s | 已核实（搜索确认：confirmed the GUE connection）| https://mfeapp.baruch.cuny.edu/math/wp-content/uploads/2018/08/zeta.10to22.pdf |
| 数值件：qrh_audit5/6/8.py/.json | 本工作 | 2026-10 | 已核实（Anaconda python 复跑）| 本地路径 |

## 边界
- 无目录（短文 4-5 页）
- 全表格 cantSplit + 表头 tblHeader（XL 惯例）
- 标题三行拆分、18pt 黑体
- 最终回复 ≤300 字、≤8 行（word skill 规则）
