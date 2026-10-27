# outline.md — 攻防 XLII S7.8 落档（(L1)(L2) 长线攻坚第一轮）

## 交付物
- 文件名：路2攻防XLII-S7.8-(L1)(L2)长线攻坚第一轮-真实定义件与Abel-SW组装真证.docx
- 目录：C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1（d1 惯例；公式 OMML 原生）
- 体裁：学术论证记录（内部系列文档），无模板创建（python-docx + latex2mathml→mathml2omml OMML 管线，母本 gen_s7_7_doc.py）

## 结构（章节 → 事实依据 → 公式）
1. 概览：两线并进 + 编译状态
   - 依据：本轮工程执行记录（Main.lean 改动、main_l2_full.txt 2604 绿）
2. (L2) 半形式化落位（完成）：sum_abel_partial（Icc 口径 Abel 真证，hIcc' = insert N 分解、succ insert 路线）、prime_sum_bound（组装真证：primeSum → Abel → SW 部分和 → 三 axiom 件）、siegel_walfisz_chi5 本体仍挂账（PNT-in-AP 量级）
   - 公式：primeSum 定义；Abel 部分和；SW 界
3. (L1) 真实定义件（opaque → def）：primePowerSum = Finset 有限和 + Real.rpow；trivialTerm = ∑' 实级数（χ₅ 偶特征 a=0）；zeroWeightedSum = 复和取实部（Complex.cpow）；logDerivTerm 保持 opaque（导数件）
   - 公式：Yildirim (6)；三个真实定义
4. (L1b) 真证两件
   - (L1b-A) r=1/2 代数桥：n^{−1/2} = (√n)⁻¹；primePowerSum χ(1/2)X = Σ Λχ·(√n)⁻¹（衔接 (L2) primeSum K≡1 特例）
   - (L1b-B) trivialTerm 收敛件：x>1、r>0 级数可和（x^{−(2ℓ+r)} = x^{−r}·(x^{−2})^ℓ 分解 + inv 界 + 几何级数比较 Summable.of_nonneg_of_le）
5. 挂账与边界：x=1 调和型发散（landau_explicit_L 的 1≤x 前提需单独口径）；零点无条件收敛挂 N(T) 计数（(L1c)）；L 版 BGS 的 SW 常数显式化
6. 编译证据与下一步：2604 绿；下一步 = logDerivTerm 导数件 / SW 本体 / 推 GitHub（待指令）

## 引用核查表（内部工程与系列文档，无需外网核实）
| 引用名称 | 标识 | 核实状态 | 来源 |
|---|---|---|---|
| Yildirim 1991 公式 (6) | Main.lean 注释 116-118 | 已核实（工程注释原文） | C:\proj2\QRH\S7_1_Main.lean |
| landau_explicit_L / siegel_walfisz_chi5 精确陈述 | QRH_summary.md 68 行 | 已核实 | C:\proj2\QRH\QRH_summary.md |
| (L2) 组装件（primeSum/sum_abel_partial/prime_sum_bound） | Main.lean 2.2b 区 | 已核实 | 同上 |
| (L1b) 真证（primePowerSum_half_eq_sqrt/trivialTerm_summable） | Main.lean 2.1.1 区 | 已核实 | 同上 |
| 编译证据 2604 jobs 全绿 | main_l2_full.txt | 已核实 | C:\proj2\main_l2_full.txt |
| 系列文档 S7.1–S7.7 | d1 目录 | 已核实 | C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1 |

## 关键约束
- 公式全部 OMML 原生（latex2mathml + mathml2omml），禁 LaTeX 源码文本；代码标识符保持文本
- 中文正文单引号；无 emoji；d1 系列排版风格（Title 16pt 黑体、正文 10.5pt 宋体 1.5 倍行距、Heading 1 12pt 黑体、表头浅灰）
- 交付前 audit（audit.py）退出码 0 + render.py 渲染逐页检查
