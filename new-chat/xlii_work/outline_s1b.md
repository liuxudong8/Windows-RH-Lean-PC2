# outline.md — 攻防 XLII S1b 落档（λ(T) 构造 + p 量化两段）

## 任务与体裁
- 交付：中文 Word（无模板创建），d1 目录，攻防系列论文级学术文档
- 体裁：学术论文规范写作（academics.md）
- 读者：数学/数论同行（内部谱对偶论证系列）

## 文档目标
将 S1b 定理构造（λ(T) 方案，攻防 XLII.1 条件式）与 p 量化两段（文献复核 + 数值标定）合并落档。

## 结构
1. 承接与主线（XLI 坐标、S0 通过、S1a 归因结果、S1b 任务）
2. S1b 定理构造（(H2′_λ) 显式化、核–误差平衡、λ(T) 选择与速率、定理+证明骨架、结构重零点排除）
3. p 量化：文献侧复核（BGS Lemma 5 精确陈述、三个硬约束、超支撑核=强配对截断版）
4. p 量化：数值标定（方法、表 1 结果、图 1、判定）
5. 诚实披露与开放问题
参考文献

## 事实依据（数据源）
- BGS Lemma 5 陈述：qrh_work/xl_read0.txt 行 27–31（f 支撑⊂[−1,1]、O_f(1/√logT)、w(z)=4/(4−z²)）
- S0 关键数值：qrh_work/xlii_s0_v3.json（A_zeta_fine/A_L_fine/A_GUE2、s<0.01 计数 0、min_gap）
- S1a 数值：qrh_work/xlii_s1a.json（D_actual、decay 未决、核族）
- p 标定（本次计算）：log|Δ| vs log(λ_eff) 回归，ζ −2.261(r²0.97)、L −2.792(r²0.94)；C 标定 a=0.5→0.0101/0.0121、a=1.0→0.0453/0.0549、a=2.0→0.0776/0.109
- 速率：p=1 保守 q=1/4 → A−1=O((logT)^{−1/4})；实测 p_eff=−2.3 平衡 q=5/7 → (logT)^{−15/7}

## 引用核查表
| 引用名称 | 编号 | 发布年份 | 核实状态 | 来源URL |
|---|---|---|---|---|
| Lamzouri, A new proof that more than 2/3 of the zeros ... are simple and on the critical line | arXiv:2609.02882v2 | 2026-09-08 (v2) | 已核实 | https://arxiv.org/abs/2609.02882 |
| Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh, An unconditional Montgomery theorem for pair correlation ... | arXiv:2306.04799 | 2023-06-07 | 已核实 | https://arxiv.org/abs/2306.04799 |

## 边界
- 定理为条件式（(H2′_λ) 前提），p_λ 数值标定为证据非定理前提——诚实披露
- 衰减律判别明确挂 S2 后续（不在本文判定）
- 速率升级按实测 p_eff 给出为"若标定成立"，正文区分保守/标定两档
