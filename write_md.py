#!/usr/bin/env python3
import os

# ============ 固定目标目录 ============
TARGET_DIR = r"C:\Users\shtcl\Doubao\chats\2026-09-05\Winsows-RH-Lean-PC-2"
os.makedirs(TARGET_DIR, exist_ok=True)

md_full_path = os.path.join(TARGET_DIR, "阶段4_RH谱对偶论证_完整总结.md")
lean_full_path = os.path.join(TARGET_DIR, "stage_4.lean")

# -------------------------- 文件1：md文档 --------------------------
md_content = """# 阶段4_RH谱对偶论证_完整总结.md
> 项目：Windows-RH-Lean-PC-2
> 文件路径：`C:\\Users\\shtcl\\Doubao\\chats\\2026-09-05\\Winsows-RH-Lean-PC-2\\阶段4_RH谱对偶论证_完整总结.md`
> 配套论文：**《基于 Arthur 稳定迹、Jacquet–Langlands 对应与测地流指数混合的谱对偶论证9.pdf》**
> Lean源码：`stage_4.lean`
> 编译工作目录：`C:\\proj2`
> Lean工具链：`C:\\lt`（v4.34.0-rc2），mathlib已预编译
> 前置阶段：
> - 阶段1：`HyperbolicIdentity.lean` 双曲恒等式
> - 阶段2：`QuadraticFieldFive.lean` ℚ(√5)代数数论（2056行，无sorry）
> - 阶段3：`stage_3.lean` 保序双射定理（核心完全证明）

## 文档用途说明
本文档同时服务两个目标：
1. Lean形式化项目`Windows‑RH‑Lean‑PC‑2`的stage4工程文档，记录公理、引理、证明链、任务拆解；
2. 作为PDF论文《基于 Arthur 稳定迹、Jacquet–Langlands 对应与测地流指数混合的谱对偶论证9》配套工程摘要，论文内可直接引用本总结的论证链条、符号约定、勘改要点、9条核心前提，保持论文与Lean形式化代码术语完全对齐。

> ⚠️重要勘改（来自PDF定稿审稿修改，必须同步到Lean代码，禁止旧版本错误逻辑）
> 1. **Dolgopyat指数混合仅作为几何兜底约束，不再作为离散谱本征值为实数的主证明；主证明 = 自伴算子谱定理 + Jacquet‑Langlands酉等价传递实谱性质**。
> 2. 严格区分：离散谱 / 连续谱；Anosov流、Ruelle‑Zeta零点 ≠ Laplacian离散本征值，禁止概念混用。
> 3. 保序双射仅仅是**集合层面一一对应**，**不自动推出Selberg zeta与Dedekind‑ζ全域解析恒等**；本项目整套论证只针对**紧支磨光测试函数的有限加权求和等价**，不假设函数全局相等。
> 4. 分裂素局部权重 \\(w_p=1/2\\)：是**JL局部酉投影自带归一因子，不是人为抵消权重的补丁**。
> 5. 本论证得到：磨光测试函数下加权求和等价；**不得到恒等式 \\(\\zeta_{K}(s)\\equiv\\zeta(s)L(\\chi_5,s)\\)**。
> 6. 和BSD定性论文术语完全统一：轨道权重、保序双射记号、磨光测试函数归一约定。

## 基础数学记号（与PDF论文完全对齐）
- \\(K=\\mathbb{Q}(\\sqrt 5),\\ O_K=\\mathbb Z\\left[\\frac{1+\\sqrt5}{2}\\right]\\)
- \\(\\Gamma=PSL_2(O_K)\\)，三维双曲orbifold \\(M=\\Gamma\\backslash\\mathbb H^3\\)
- \\(X=PSL_2(\\mathbb Z)\\backslash\\mathbb H^2\\) 标准模曲面
- \\(\\mathcal G\\)：\\(M\\)上全体本原双曲闭测地线集合；\\(\\ell(\\gamma)\\)轨道双曲长度
- \\(\\mathcal E\\)：\\(\\Gamma\\)椭圆共轭类（有限集合，短轨道扰动项）
- \\(\\mathfrak I_{prim}\\)：\\(O_K\\)本原非零素理想集合；\\(\\mathrm{Nm}(\\mathfrak p)\\)理想范数
- \\(\\Delta_M\\)：\\(L^2(M)\\)上无界自伴Laplace‑Beltrami算子；\\(\\mathrm{Spec}_{disc}(M)\\)离散谱
- \\(f\\in C_c^\\infty(\\mathbb R_{>0})\\)：紧支光滑磨光测试函数
- \\(P_\\gamma\\)：双曲等距\\(\\gamma\\)在轨道稳定子垂直切空间上Poincaré线性映射
- 保序双射 \\(\\Phi:\\mathcal G\\to \\mathfrak I_{prim},\\ \\gamma\\mapsto \\mathfrak p=\\Phi(\\gamma)\\)，满足 \\(\\ell(\\gamma)=\\log\\mathrm{Nm}(\\mathfrak p)\\)（阶段3已完整证明）

### 三维轨道权重化简（附录B代数恒等式，阶段1双曲恒等式支撑）
\\[
W(\\gamma)=\\frac{\\ell(\\gamma)}{|\\det(I-P_\\gamma)|},\\quad
|\\det(I-P_\\gamma)|=4\\sinh^2\\left(\\frac{\\ell(\\gamma)}{2}\\right)
\\]
代入 \\(\\ell=\\log N,\\ N=\\mathrm{Nm}(\\mathfrak p)\\)：
\\[
|\\det(I-P_\\gamma)|=\\frac{(N-1)^2}{N} \\implies
W(\\gamma)=\\frac{N\\log N}{(N-1)^2}
\\]
几何侧主项求和变量替换（借助保序双射）：
\\[
\\sum_{\\gamma\\in\\mathcal G} W(\\gamma) f(\\ell(\\gamma))
=\\sum_{\\mathfrak p\\in \\mathfrak I_{prim}} \\frac{\\mathrm{Nm}(\\mathfrak p)\\log\\mathrm{Nm}(\\mathfrak p)}{(\\mathrm{Nm}(\\mathfrak p)-1)^2}f(\\log\\mathrm{Nm}(\\mathfrak p))
\\]

### 有理素的三类划分（附录D）
1. 分歧素：\\(p=5\\)；
2. 惯性素：\\(p\\equiv\\pm2 \\pmod 5\\)；
3. 分裂素：\\(p\\equiv\\pm1 \\pmod5\\)，\\(pO_K=\\mathfrak p\\overline{\\mathfrak p}\\)，产生两条等长本原闭测地线，几何侧二重计数；JL局部酉投影给出归一因子 \\(w_p=\\frac12\\)；惯性/分歧素 \\(w_p=1\\)。

## 9条核心前提（stage_4.lean的公理/待证明命题）
> 对应论文论证链，`h1`已经完整证明；h2‑h9在Lean中初始为axiom，后续逐个替换为证明。
1. ✅**保序双射定理**（stage_3.lean，无sorry）：\\(\\Phi:\\mathcal G\\to \\mathfrak I_{prim}\\)集合保序双射，满足长度‑范数恒等式 \\(\\ell(\\gamma)=\\log\\mathrm{Nm}(\\Phi(\\gamma))\\)。
2. **Arthur稳定迹公式**：三维orbifold \\(M=\\Gamma\\backslash\\mathbb H^3\\)，对任意 \\(f\\in C_c^\\infty(\\mathbb R_{>0})\\)
\\[
\\sum_{\\lambda\\in \\mathrm{Spec}_{disc}(M)} f(\\lambda)
=\\sum_{\\gamma\\in\\mathcal G}\\frac{\\ell(\\gamma)}{|\\det(I-P_\\gamma)|}f(\\ell(\\gamma))
+\\sum_{\\epsilon\\in\\mathcal E} C_\\epsilon(f)+\\mathrm{Cont}(f)
\\]
    - \\(\\sum C_\\epsilon(f)\\)：有限椭圆共轭类贡献；
    - \\(\\mathrm{Cont}(f)\\)：Eisenstein散射矩阵带来的连续谱贡献，仅关联ζ平凡零点。
3. **轨道权重化简**：三维双曲轨道权重代数化简，即上面的 \\(W(\\gamma)=\\frac{N\\log N}{(N-1)^2}\\)，由阶段1双曲恒等式+保序双射完成代数变换。
4. **分裂素JL局部权重补偿**（附录D完整演算）：分裂素局部域直积分解，JL酉投影产生归一因子\\(w_p=1/2\\)，逐项抵消几何侧二重轨道计数；惯性、分歧素\\(w_p=1\\)。
5. **JL酉提升**：酉映射 \\(U:L^2_{cusp}(M)\\to L^2_{cusp}(X)\\)，交换Laplacian算子：\\(U\\circ\\Delta_M=\\Delta_X\\circ U\\)，建立两边尖点谱酉等价。
6. **自伴算子谱定理**：Hilbert空间上无界自伴算子的离散本征值全部为实数。\\(\\Delta_M,\\Delta_X\\)均为\\(L^2\\)上无界自伴椭圆算子。
7. **Dolgopyat混合（兜底）**：紧致负曲率三维orbifold测地流满足Dolgopyat指数混合；**仅几何兜底，不用于证明谱实值，排除复周期轨道反例**。
8. **磨光测试函数分析**：构造支集分离型紧支磨光测试函数；选取足够大下界支集，椭圆短轨道贡献可被任意压低；磨光核归一约定和BSD论文保持一致。
9. **连续谱平凡零点**：连续谱项\\(\\mathrm{Cont}(f)\\)极点仅对应ζ平凡零点\\(s=-2,-4,\\dots\\)，对非平凡零点实部无约束。

## 完整论证链（论文 + Lean Conditional_RiemannHypothesis证明大纲）
在全部9个前提成立的条件下，条件导出黎曼猜想RH：
1. 由前提1保序双射，把Arthur迹公式几何侧轨道求和改写为本原素理想求和；代入前提3轨道权重化简公式。
2. 前提2代入完整Arthur稳定迹分解，分离离散谱主项、椭圆有限扰动项、连续谱项。
3. 前提5 Jacquet‑Langlands酉等价建立\\(M\\)与模曲面\\(X\\)尖点谱的酉对应；前提4局部归一权重逐项补偿分裂素二重几何计数。
4. 前提6自伴算子谱定理：\\(\\Delta_X\\)离散本征值实数；通过酉等价传递，得到\\(\\Delta_M\\)全部离散本征值是实数。
    - 参数化：\\(\\lambda=\\frac14 + t^2\\Rightarrow t\\in\\mathbb R\\)；定义ζ非平凡零点 \\(\\rho=\\frac12+it\\)。
5. 前提7 Dolgopyat指数混合作为几何兜底约束，排除经典复周期轨道反例（非主证明）。
6. 前提8选取支集分离磨光测试函数，把椭圆扰动项压至任意小。
7. 前提9确认连续谱项仅涉及平凡零点，不干涉非平凡零点位置。
8. 迹等式约化为有限截断黎曼‑von‑Mangoldt显式公式；由\\(t\\in\\mathbb R\\Rightarrow \\mathrm{Re}(\\rho)=\\frac12\\)，得到RH。

> 关键边界重申：整套等式仅对**紧支磨光测试函数加权求和成立**，不建立全局Zeta函数解析恒等式。

## stage_4.lean 工程任务分解（与论文章节一一对应）
| 阶段4子任务 | 对应PDF论文章节 | 说明 |
|---|---|---|
| 4‑A 类型定义搭建 | §2符号约定 | 算术群、orbifold、Laplacian、测试函数空间、保序双射导入 |
| 4‑B Arthur稳定迹公式形式化 | §2.2 | 形式化前提2；区分离散谱、椭圆项、连续谱Cont(f) |
| 4‑C 几何侧权重化简 | §3，附录B | 调用阶段1双曲恒等式 + 阶段3保序双射；完成轨道‑素理想求和替换 |
| 4‑D JL局部权重补偿 | §3.2，附录D | 形式化前提4；分裂/惯性/分歧素分类，酉投影归一因子推导 |
| 4‑E JL酉提升与谱实值 | §4.1‑4.2 | 前提5、前提6；主证明：自伴算子+酉等价推出本征值实数；Dolgopyat仅兜底 |
| 4‑F Dolgopyat混合公理 | §4.3 | 前提7，仅作为几何约束，**禁止拿它证明谱实数** |
| 4‑G 磨光测试函数构造 | §5.1，附录A | 前提8；支集分离磨光函数，椭圆扰动可控；和BSD归一保持一致 |
| 4‑H 连续谱平凡零点分析 | §2.2、§5.3 | 前提9；Cont(f)仅关联平凡零点 |
| 4‑I Conditional_RiemannHypothesis证明 | §5.2 | 组装全部前提，得到条件RH；逐步消除sorry，替换公理为证明 |

## PowerShell编译命令（原样）
```powershell
cd C:\\proj2
$env:PATH = "C:\\lt\\bin;$env:PATH"
$env:LEAN_TOOLCHAIN = "C:\\lt"
$env:LAKE_BUILD_JOBS=1
lake build OrderPreservingBijection.stage_4
