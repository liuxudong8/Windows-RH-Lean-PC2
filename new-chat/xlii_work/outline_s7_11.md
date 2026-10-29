# S7.11 落档大纲：x=1 边界口径（trivialTerm 调和发散 + landau_explicit_L 前提收紧）

## 体裁与格式
- 体裁：学术攻坚记录（内部 d1 惯例文档，非期刊论文）；中文 d1 + 英文 d1\en
- 格式：无模板新建；Unicode 数学文本（可读纯文本 + 上下标，禁 LaTeX 源码）；A4、2.5cm 边距、标题黑体、正文宋体 12pt、1.5 倍行距、首行缩进
- 引用核查表：**不适用**——本文档为内部数学口径记录，无法规/标准/外部文献引用

## 结构（中英同构）
1. 任务与结论
2. 数学口径
   - 2.1 trivialTerm 定义与收敛域
   - 2.2 x=1 调和发散
   - 2.3 约定与前提收紧（防假命题陷阱）
   - 2.4 与 (L1b)/(L2) 的衔接
3. Lean 实现
   - 3.1 陈述改动（landau_explicit_L 前提 1≤x → 1<x）
   - 3.2 约定件（trivialTerm_one_term / trivialTerm_one）
   - 3.3 编译证据（dbg_build_x1.txt，2704 绿）
4. 边界与后续

## 事实依据（均来自本项目 Lean 源码与构建日志）
- trivialTerm r x = Σ_ℓ x^{−(2ℓ+r)}/(2ℓ+r)（S7_1_Main.lean 114-115 行真实定义；Yildirim 公式 (6) 右侧第一项，χ₅ 偶特征 a=0）
- trivialTerm_summable（真证，1<x、r>0 ⟹ Summable；比较判别 + 几何级数）
- x=1 逐项：x^{−(2ℓ+r)} = 1，项 = 1/(2ℓ+r)；Σ 1/(2ℓ+r) 与 Σ 1/n 同阶发散（1/(2ℓ+r) ~ 1/(2ℓ)）
- landau_explicit_L 原前提 (1:ℝ) ≤ x（129 行）→ 收紧为 (1:ℝ) < x
- 假命题陷阱：若保留 1≤x，x=1 时 axiom 断言 trivialTerm(1) = −logDeriv(r)（primeSum/zeroWeightedSum 在 x=1 为 0），而 trivialTerm(1) 发散——∑' 默认值 0 不可作数学意义引用
- 新增约定件：trivialTerm_one_term（simp 真证）、trivialTerm_one（tsum_congr 真证）
- 构建：lake build QRH，2704 jobs，exit=0，无 error 无 warning（dbg_build_x1.txt）
- 发散性正式证明（¬ Summable）留可选后续件；此处仅记录口径（"口径决定，非深证明"）

## 验收
- 中英 audit 0 errors；渲染逐页通过；catalogue 无 TOC 域不动
