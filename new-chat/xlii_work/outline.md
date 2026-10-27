# 攻防 XLII 文档 outline（S0 数值定向落档）

体裁：学术论文规范写作（攻防系列 d1 惯例，中文单版）
交付：D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLII-全尺度GUE配对与在线比例1-o(1)-S0数值定向-口径修正与超GUE排斥.docx
临时目录：C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xlii_work\
数据源：qrh_work\xlii_s0_v3.json（终版数值）、xlii_s0_gue_sim.json（GUE 模拟）、xlii_s0_fig1/2.png（图，300dpi 重渲染）
风格基准：XLI v6（read0_zh_v6.txt）——标题+副标题+系列+日期、摘要+关键词、# N　编号、三线表、图题图下、参考文献格式

## 章节结构与事实依据

### 标题
路2攻防XLII—全尺度GUE配对与在线比例1−o(1)：S0数值定向（口径修正、超GUE排斥与理论对应）
——《谱对偶论证》系列（d1）：S0 生死门判定
2026 年 10 月 24 日

### 摘要（报道性 ~400 字）
- 目的：承接 XLI 主线"干到 1"——(H2) 升级为 λ(T)→∞ 全尺度 GUE 配对（强 Montgomery 型对固定模实特征 L(s,χ₅)），Prop 2.1 直接给出 A→1、在线比例 1−o(1)；S0 数值定向为生死门。
- 方法：T=6×10⁵ 零点（ζ 999354/L 1149836 根）；核 K_a(u)=sinc²(πu/a)，谱支撑 λ_eff=π/a；A=1+ΣK²/N（有序全对）；局部归一化 u=|Δ|·ρ(t_mid)；双侧 GUE/泊松对照。
- 结果：A(λ) 全曲线（λ_eff∈[0.39,31.4]）实测紧贴双侧 GUE 预测、窄端单调逼近 1 无反弹（a=0.5→0.1：A−1 从 1.49e-2 到 1.3e-4）；重零点无信号（s_min=0.0123/0.0133，s<0.01 计数 0）；实测系统性低于 GUE（超 GUE 排斥），GUE 模拟排除有限 N 伪影，段间漂移显示随 T 收敛；三项口径修正（λ_eff 换算、L 密度 −1 项、全局 δ vs 局部 ρ、双侧因子 2）。
- 结论：S0 通过、全尺度 GUE 有数据支持；理论对应三层（GUE 普适类、β=2 排斥 O(a³)、有限 T 算术项负偏差归因）；S1 拆为 S1a（算术项归因）与 S1b（λ(T) 构造）。

### 关键词
全尺度 GUE 配对；在线简单零点比例 1−o(1)；配对常数；超 GUE 排斥；口径修正

### 1 承接与主线
1.1 XLI 坐标与"干到 1"路线（7/8 门槛、fejer_a0.5 A≈1.0079/1.0114、余量 0.1171/0.1136、并集加权比例≈0.990；路线 = λ(T)→∞ 全尺度 GUE 配对，Prop 2.1 → A→1 → 比例 1−o(1)；文献坐标"强配对猜想 ⟹ 几乎全部零点简单"）
1.2 四阶段规划 S0-S3（步骤表：S0 数值定向生死门/S1 理论构造/S2 数值验证/S3 闭环落档；判定门）

### 2 数值口径与方法
2.1 数据与零点密度：T=6×10⁵、剔除 t<300、ζ 999354/L 1149836；ρ_ζ=(1/2π)log(t/2π)；L 密度校准（−1 项错误 → 去 −1 后 nn_mean 0.9197→1.0027）
2.2 核族与谱支撑换算：K_a(u)=sinc²(πu/a)；谱支撑 λ_eff(a)=π/a（Fourier 严格计算，e^{-2πiuξ} 约定）；表 1 换算表；XLI"λ_eff≈0.5"倒挂口径修正（fejer_a0.5 实际 λ_eff=6.28）
2.3 配对常数与归一化：A=1+ΣK²/N（有序全对 i≠j 两侧）；局部归一化 u=|Δ|·ρ(t_mid)（ρ 逐点；全局 δ=logT/2π 口径在宽带数据下 u 平均≈1.74≠1，宽核放大误差）；双侧 GUE/泊松对照（因子 2：GUE2=1+2∫(1−sinc²)sinc⁴du、Poi2=1+2a/3；v1/v2"超 Poisson"为单侧约定伪影）
2.4 三项口径修正总结（λ_eff 换算、L 密度、δ vs ρ + 因子 2）——影响 XLI 数值声明（1.0079→1.0150 局部口径，结论不翻转）

### 3 S0 结果
3.1 A(λ) 全曲线：表 2（17 行：a、λ_eff、Aζ、AL、GUE2、Poi2、ζ−GUE2）；图 1；读数：窄端单调→1 无反弹、实测贴 GUE2 下方、宽端负偏差平台 −0.02
3.2 极小间距与重零点：表 3（ζ/L：n、s_min、s<0.05/0.01/0.005/0.001 计数、GUE 预测）；无重零点迹象
3.3 有限 T 涨落标定：表 4（4 a × 2 族 × 5 段 A 值 + 相邻max + 极差）；窄端信号远超漂移；负偏差超漂移 ~3 倍为系统
3.4 GUE 模拟对照：N=4000×12、校准后 nn_mean=1.0000；A_sim≈GUE2（偏差 +0.001~+0.006）；实测负偏差非有限 N 伪影

### 4 判定与理论对应
4.1 S0 生死门判定：通过（A 单调逼近 1 无反弹、全曲线贴 GUE、重零点无信号、涨落可控）
4.2 三层理论对应：
  (i) 曲线整体贴 GUE = Montgomery 配对猜想/RMT 普适类（ζ 猜想级、L(χ₅) 固定模开放 = (H2)/(H2′)）；
  (ii) 窄端 O(a³) = GUE β=2 水平排斥普适形状（ρ₂~u²、Dyson 对数气体；数据独立读出 β=2，排除 β=0/β=4）；
  (iii) 负偏差 = 有限 T 算术项（BGS 误差 O_f(1/√logT) 核依赖；Montgomery F(α)≥|α| 同源素数项结构；段间漂移显示随 T 收敛 = 算术项签名；GUE 模拟排除有限 N）
4.3 诚实边界：数据 T=6×10⁵/λ_eff≤31.4 有限；λ(T)→∞ 全尺度是假设 (H2′)；超 GUE 排斥边缘显著（窄端相对 18%、绝对 −0.0037，超段间漂移 ~2 倍）不作前提；XLI 旧口径数值需披露

### 5 下一步：S1 拆解
5.1 S1a 算术项归因：Parseval 把 A 偏差翻译成 F(α)−|α|（对照 Montgomery 下界超出量）；5 段 Δ(a;T) 衰减律拟合（1/logT vs 1/√logT）；三族核依赖常数（fejer/sinc/gauss）
5.2 S1b λ(T) 方案构造：(H2′) 显式化、A=1+O(λ^{-1}) 收敛推导、重零点项并入、并集加权 → 定理形态 1−o(1)

### 参考文献（全部已核实，沿用 XLI + 本工作数值件）
[1] Lamzouri Y. arXiv:2609.02882v2（Prop 2.1/Lemma 3.2/Remark 3.4）
[2] Baluyot D, Goldston D, Suriajaya A I, et al. arXiv:2306.04799（Lemma 5 无条件配对公式 O_f(1/√logT)；BGS 推广开放）
[3] Özlük A E. 1982（GRH 下 ≥11/12 简单）
[4] Kandhil N, Languasco A, Moree P. arXiv:2411.19762（Yıldırım 跨字符平均、GRH 前提）
[5] Carneiro E, Milinovich M B, Ramos A P. arXiv:2310.01913（Fourier optimization）
[6] Odlyzko A M. 10^22-nd zero（GUE 数值验证）
[7] 攻防 XLII 数值件（本工作）：qrh_work/xlii_s0.py~xlii_s0_v3.py、xlii_s0_check.py、xlii_s0_gue.py、xlii_s0_plot.py、xlii_s0_v3.json、xlii_s0_gue_sim.json；零点数据 zeros_T6e5.npz
[8] 攻防 XLI（d1 已交付）：拟随机并集定理条件形态、7/8 门槛
[9] 攻防 XL（d1 已交付）：配对侧无条件界理论构造

## 引用核查表
| 引用 | 身份 | 核实状态 | 来源 |
| Lamzouri arXiv:2609.02882v2 | Prop 2.1/Lemma 3.2/Remark 3.4 | 已核实 | XLI read0_zh_v6.txt refs[1] |
| BGS arXiv:2306.04799 | Lemma 5 | 已核实 | XLI refs[2] |
| Özlük 1982 | ≥11/12 简单 | 已核实（转述） | XLI refs[3] |
| Kandhil et al. arXiv:2411.19762 | Yıldırım | 已核实 | XLI refs[4] |
| Carneiro et al. arXiv:2310.01913 | Fourier optimization | 已核实 | XLI refs[5] |
| Odlyzko | GUE 验证 | 已核实 | XLI refs[6] |
| 本工作数值件 | xlii_s0*.py/.json | 自产可复跑 | 本次运行 |
| 攻防 XLI/XL | d1 已交付 | 自产 | XLI v6 |

## 验收条件
- audit（无 source）退出码 0
- render 逐页核验（标题/编号/表格三线表/图题图下/字体统一/分页）
- 数据与 xlii_s0_v3.json/gue_sim.json 逐值一致（表 2/3/4 抽样核对）
- 无 TOC 域（catalogue 仅提示）
- 中文纯文本公式、无 emoji、无占位符
