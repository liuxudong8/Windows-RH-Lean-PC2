# 骨架 A 讨论稿 outline（弱 BSD 秩 1 的 Hecke 显式公式重证明）

## 交付物
- Word 文档（学术讨论稿，阿拉伯小数层级 1 → 1.1），动态 TOC，页脚页码
- 路径：`D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx`
- 体裁：学术论文规范（academics.md）：正文五号宋体、章标题小四黑体、二级五号黑体、1.5 倍行距、首行缩进 2 字符

## 结构规划

1. 引言：目标与已知边界
   1.1 弱 BSD 的已知状态（解析秩 ≤ 1 已证：Gross–Zagier、Kolyvagin；全实域 Zhang）
   1.2 未证方向与本文目标（代数秩 ≥ 1 ⟹ 解析秩 ≥ 1；代数秩 1 ⟹ L′(E,1) ≠ 0）
   1.3 谱对偶路线的承接（G7 判死 K-GRH 谱↔零点权重坍缩；BSD 落点是 s=1 局部整数不变量）
   1.4 路线总览（Hecke 标签 + 链 2 + 显式公式分解 + 反证；数值支撑）
2. 对象与模性
   2.1 主曲线 E = 37a1 over K = ℚ(√5)（y²+y = x³−x；代数秩 ≥ 1 构造性：(0,0) 无限阶）
   2.2 模性（Freitas–Le Hung–Siksek 2015：实二次域椭圆曲线全模；f 为权 2 全纯 Hilbert 模形式；L(E,s) = L(f,s)）
3. 无条件输入
   3.1 Ramanujan（权 2 全纯：|a_𝔭| ≤ 2√Nm，Eichler–Shimura/Deligne，无条件——非 Selberg 谱隙）
   3.2 链 2（log Nm(𝔭) = ℓ₁+ℓ₂ 逐点恒等——定理 10 核心成果，Hecke 加权显式公式的算术–几何接口）
4. 显式公式分解（骨架核心）
   4.1 L(f,s) 的 Weil 显式公式（Hecke 加权；零点侧 = 主项 − 素数项 + Γ/常数项；标注 G7 形式教训）
   4.2 一阶 Taylor：L′(E,1) 的分解（主项 − Hecke 素数项 + Γ′项 + 余项；系数待按标准 Weil 公式钉死）
   4.3 反证骨架（假设 L′(E,1) = 0 ⟹ 全消条件；矛盾源候选：Ramanujan + 链 2 计数的素数项主项不可消；**卡点诚实标注**）
   4.4 与 G7 对比（解析秩局部性规避权重坍缩；但显式公式形式闭合问题仍在）
5. 数值支撑
   5.1 Hecke 端表（E=37a1 over ℚ(√5)：1142 素理想、Ramanujan 0 违反、惰性素理论核对全 ✓）
   5.2 欧拉积闭合（Re s > 3/2 收敛域：L_cut(2.0)=0.894、L_cut(1.5)=0.700）
   5.3 方法学修正（ν(s) 素数项探针不判秩——s=1 零点在解析延拓层）
   5.4 待补清单（degree-2 数值延拓；显式公式精确形态核对）
6. 结论与下一步
参考文献

## 引用核查表
| 引用名称 | 发布信息 | 核实状态 | 搜索来源 URL |
|---|---|---|---|
| Gross–Zagier, Heegner points and derivatives of L-series, Invent. Math. 84 (1986) | 已核实（弱 BSD 解析秩 ≤1 已证的组成之一） | 已核实 | https://arxiv.org/pdf/math/0611423.pdf |
| Kolyvagin, Euler systems (1990) | 已核实（弱 BSD 解析秩 ≤1 已证） | 已核实 | https://terrytao.wordpress.com/2007/05/03/distinguished-lecture-series-ii-shou-wu-zhang-%E2%80%9Cgross-zagier-formula-and-birch-and-swinnerton-dyer-conjecture-%E2%80%9D/ |
| Zhang S-W, Gross–Zagier formula for GL₂, Asian J. Math. 5 (2001) 183–290 | 已核实（全实域推广） | 已核实 | https://annals.math.princeton.edu/2018/187-2/p04 ; https://web.math.princeton.edu/~shouwu/publications/gl2-ajm.pdf |
| Freitas–Le Hung–Siksek, elliptic curves over real quadratic fields are modular, 2015 | 已核实（实二次域全模） | 已核实 | https://warwick.ac.uk/fac/sci/maths/people/staff/box/phd_65.pdf |
| Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974) | 已核实（权 ≥2 全纯 Ramanujan） | 已核实 | https://arxiv.org/pdf/1003.0559.pdf |
| LMFDB 37.a1 rank 1 | 已核实 | 已核实 | https://www.lmfdb.org/EllipticCurve/Q/37a/ |
| E(ℚ) = ⟨(0,0)⟩ rank 1（37a1 生成元） | 已核实 | 已核实 | https://arxiv.org/pdf/1608.08672v3 |
| FLHS 2015 卷期页码 | 待核（正文标年份与期刊名） | 待核 | - |

## 关键事实依据（不引外部，来自本项目）
- G7 核验（2026-10-05）：ζ/ζ_K 真实零点求和 ~6e-4，pt5c 右侧 −0.066 是 O(1) 组合——"7% 系统差"伪差；谱↔零点在 (1+t²)⁻ᵏ 权重下坍缩
- 链 2（定理 10）：长度 = ℓ₁+ℓ₂ = log Nm(𝔭) 逐点恒等，保序配对数值验证
- Hecke 端数值（2026-10-05 a1/a4.py）：37a1 over ℚ(√5) 1142 素理想、Ramanujan 违反 0、惰性素 a_{p²}=a_p²−2p 全 ✓（好约化，p=37 坏约化排除）、L_cut(2.0)=0.894、L_cut(1.5)=0.700
- ν(s) 探针（a2/a3.py）：37a1 秩 1 也收敛——素数项探针不判秩

## 生成要点
- 无模板创建（Option 2）
- 动态 TOC（Heading 1–2）、页脚页码、A4、2.5cm 边距
- 表格：数值表用浅灰表头、cantSplit、tblHeader、表内文字无缩进
- 公式用 Unicode 数学文本（|a_𝔭| ≤ 2√Nm、L(E,s)、ℓ₁+ℓ₂、L′(E,1)）
- 中文段落禁用英文双引号
- 参考文献 GB/T 7714 数字编码；[4] FLHS 卷页标待核
