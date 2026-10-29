# S7.7 落档大纲（d1 惯例）

## 任务
落档本轮四连（BGS 引理 3-5 移植 + N1 真证 + L1 不变 + L4 切割链）到 d1。

## 体裁与格式
- 体裁：学术/技术攻防记录（同 S7.6 惯例；母本 gen_s7_6_doc.py 样式链）。
- 交付：docx，路径 d1\路2攻防XLII-S7.7-击破清单四连-BGS引理3-5移植与N1-L1-L4真证.docx。
- 公式：^{}/_{} 上标/下标 run（禁 LaTeX 源码）；正文宋体 10.5pt、1.5 行距、首行缩进 2 字符；标题黑体；表 1/表 2 用 add_table 三线式；页脚页码。

## 结构与内容（事实来源 = 本轮 Lean 工程执行记录）
1. 标题块：Title「路2攻防XLII—S7.7：击破清单四连」+ 副题 + 系列行 + 日期 2026 年 10 月 27 日。
2. 摘要：四连内容 + 2604 jobs 全绿 + 清单状态。
3. 关键词：BGS 引理；配对和展开；核可容许；Bochner 积分；变量替换；T^{3/8} 切割。
4. 1　概览与编译状态：表 1（模块/动作/状态：Core、Main、Stage3、全量编译）。
5. 2　架构重构：fourierCos/normL1 从 Stage3 迁 Core 4b 节（打破 import 环 Core→Main→Stage3）；v4.34 实证 integral_comp_mul_left 系在 MeasureTheory.Measure 命名空间、无条件、olean 已编译。
6. 3　(L3) BGS 引理 3–5 移植（Main）：3.1 引理 5 KernelAdmissible（K(0)=1 ∧ supp K̂⊂[−1,1]）+ bgs5_khat_fourier_supp + Khat_admissible 组装（Khat_zero 真证）；3.2 引理 3 bgs3_pair_expansion（分解 + diag≤C_MT+C₁ε + |prime|,|offcrit|≤1）；3.3 pair_sum_expansion 定理化 + s71_main 接入。
7. 4　N1 真证（Stage3）：4.1 n1_diag_invariant（z=0）；4.2 n1_offdiag_scale_eq（z=2δ）+ n1_offdiag_vanishes 结构件；含诚实修正（原 ∀N 陈述过宽；vanishing 归因核因子缩放 + 频域衰减件）。
8. 5　L1 不变真证：5.1 normL1 降为 Bochner 积分定义 ‖f‖₁=∫|f|；5.2 scaleKernel_L1_invariant 证明链（abs_mul + integral_const_mul + integral_comp_inv_mul_left + field_simp）。
9. 6　(L4) BGS 引理 4 移植（Main）：6.1 T^{3/8} 切割机制（offcritLow 弱实部件 / offcritHigh 计数件）；6.2 bgs4_offcrit_split/low/high；6.3 offcritical_small 组装真证（abs_add_le + add_le_add + ring）。
10. 7　清单状态与下一步：表 2（Main (L1)-(L4)、Stage3 剩余）；下一步候选（(L2) SW 显式公式件、超支撑素数项层、GitHub 推送待指示）。
11. 参考文献：内部 d1 文档 [1]-[6] + Lean 工程文件 [7]。

## 引用核查表
| 引用名称 | 文号/位置 | 发布/修订 | 现行有效性 | 核实状态 | 来源 |
|---|---|---|---|---|---|
| 攻防 XLII-S7.1~S7.6（d1 已交付文档） | d1 目录 | 2026-10-25~26 | 内部档案 | 已核实（本会话落档） | d1 |
| BGS 引理 3-5 / Montgomery–Vaughan 均值 / 显式公式 | 文档层论证（S7.1 §3、S7.5、S7.6） | — | 内部论证 | 已核实（既有文档层） | d1 |
| Lean 工程三文件 + mathlib v4.34.0-rc2 | C:\proj2\QRH | 2026-10-27 | 编译全绿 2604 jobs | 已核实（本轮 lake build） | build_qrh_l4b.txt |
注：本文无外部法规/标准/期刊引用，全部事实来自本轮工程执行记录与既有 d1 文档层论证；不触发联网核查。
