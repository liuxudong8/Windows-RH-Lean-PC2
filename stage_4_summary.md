# Stage 4 总结 — RH/K-GRH 谱对偶论证框架

| 项目 | 值 |
|------|-----|
| 生成时间 | 2026-09-30（傍晚更新，含 9/30 下午 :109 重构、Weil exact 重构、三篇审计、目标下调） |
| Lean 版本 | v4.34.0-rc2 |
| mathlib | mathlib4-master（`c:\proj2\mathlib4-master`） |
| 项目路径 | `c:\proj2` |
| 构建 | `lake build OrderPreservingBijection.stage_4` 通过（3849 jobs，2026-09-30）；全量 7690 jobs（9/30 早些时候） |

---

## 项目状态总览

| 项目 | 数值 |
|------|------|
| 活跃 .lean 文件（不含 test/archive/.bak） | 26 |
| `sorry` / `admit`（stage_4.lean，语句级实测） | 21 |
| `sorry`（ZetaZeros.lean） | 1（唯一保留：`nontrivialZeroEnum_exists` 的 S 无限，用户明确要求） |
| `sorry` / `admit`（ContourIntegral.lean） | 2（`:109` 围道=留数和 admit、`:143` 素 Dirichlet 差 admit；`:115` 已真填） |
| 自定义 `axiom`（活跃文件） | 2（均在 stage_4.lean，不在 RH/K-GRH 主链） |
| `#print axioms riemann_hypothesis` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| **主链自定义 axiom** | **0** |

---

## 项目目标与数学框架【目标状态 2026-09-30 拍板】

**当前形式化目标：K-GRH（Q(√5) 局部广义黎曼假设）**——ζ_K(s) = ζ(s)L(χ₅,s) 的全部非平凡零点 Re(ρ)=1/2，由谱对偶桥（Arthur 迹 + 保序双射 + JL 酉等价 + 显式公式）推出。

**Riemann ζ 的 RH 为长期目标**：需在文章层面补"ζ_K 零点侧 → ζ 零点侧"的桥（K-GRH 不蕴涵 RH：ζ 零点 ⊂ ζ_K 零点，反向推不出）。三篇源文献（数值匹配2 / 保序双射定理6 / 谱对偶论证9）的代数设定均为 K=Q(√5)（PSL₂(𝒪_K)），**不含 F=Q 设定**；第三篇明确放弃"Z_M(s)=ζ(s) 全域解析恒等"（类域论代数障碍 + 零点位置障碍 + k≥1 因子，数学上不可证明）。

```
Arthur 迹公式（紧支加权：谱侧 Σf(λ) = 几何侧 ΣW(γ)f(ℓ(γ)) + 椭圆 + Cont）
    ↓  保序双射 Φ:𝒢↔I_prim（第二篇，ℓ=log Nm，类数 h_K=1）
Jacquet-Langlands 酉等价（分裂素 w_p=1/2 局部酉投影归一，非人为抵消）
    ↓
K 素理想加权求和 ↔ ζ_K 显式公式（A2 修正后成立；非 ζ 显式公式）
    ↓  谱参数实值（自伴算子谱定理 + JL 酉等价，Dolgopyat 仅兜底）
λ = 1/4 + t², t∈ℝ ⟹ ρ = 1/2 + it ⟹ Re(ρ) = 1/2
    ↓
K-GRH（当前目标）→（待补桥）→ RH（长期目标）
```

代码与三篇文章逐项对应：`spectralSum`(Σf(λ) ↔ §2.2)、`geometricSum`/`orbitWeight`(W=N log N/(N−1)² ↔ §3.1/附录B)、`localJLWeight`=1/2（↔ §3.2/D.3-D.5）、`maassSpectralSum`（↔ §4.1）、`jlLParameterMap`=1/2+it（↔ §5.2）、磨光归一 ∫g_ε=1（↔ 附录A）。

---

## 已完成的主体工作

### 1. 基础设施层（已证，无 sorry）

| 模块 | 内容 |
|------|------|
| `BasicInfrastructure.lean` | TestFunction 类型（光滑紧支函数）、基本运算 |
| `MellinInfrastructure.lean` | Mellin 变换 `melinTransform f s`，基本性质 |
| `ManifoldInfrastructure.lean` | 双曲平面上的流形、度量、Laplacian |
| `HeatKernel.lean` | 热核 K_t(x,y) 及其基本性质 |
| `HeatKernelSemigroup.lean` | 热核半群 e^{-tΔ}，卷积运算 |
| `HeatKernelConvolution.lean` | 热核卷积定理 |
| `MollifiedFunction.lean` | 磨光测试函数 |

### 2. 证明框架层（结构完整，深层估计为框架假设）

| 模块 | 内容 | 状态 |
|------|------|------|
| `BijectionPhi/Basic.lean` | 谱对偶映射 Φ 的定义与基本性质 | 框架完整 |
| `Interpolation.lean` | 零点插值定理 | 框架完整 |
| `stage_3.lean` | Stage 3 桥接 | 框架完整 |
| `ContourIntegral.lean` | 围道积分（**:109 已重写为围道内版本**，`:115` 真填，`:109/:143` admit） | 重构完成 |
| `ZetaZeros.lean` | 零点枚举、重数、**围道内 Finset + 围道外 farZeroContribution 拆分**（1 个保留 sorry） | 重构完成 |
| `CompletedZeta.lean` | 完成 zeta ξ(s) 及函数方程（**0 sorry**，`xi_one_sub` 已证；整函数性/Gammaℝ 非零/零点等价 9/30 确认全填） | 新建 |

### 3. 主定理层（stage_4.lean）

`riemann_hypothesis (f : MollifiedTestFunction)` 为最终定理（**陈述保留占位**，目标为 K-GRH，见上）。关键中间定理：

- **Perron 公式框架**：几何侧求和 = Dirichlet 积分（深层交换为框架假设）
- **Mellin 反演**：f(log N(γ)) = (1/2πi)∮ M[f](s) N(γ)^{-s} ds
- **零点加权级数可和性**：密度估计 + Mellin 衰减（框架假设）
- **成对局部化**：nontrivialZeroSum 的两点隔离性质（已证）
- **对偶范数下界**、**统一支集**：主链关键估计
- **Mellin 速降界**（真证）：`mellin_transform_C2_rapid_decay : ‖M[f](s)‖ ≤ 8B'(R₀³+1)/|Im s|²`
- **反证主链**：off_critical_line_contradiction（spectralSum 由测试函数值决定 + 零点隔离）→ 与 weil_explicit_formula_trivial_terms_cancel 矛盾

---

## 本轮工作（2026-09-28 ～ 09-30）

### A. Axiom 批量降级（9/28，~28 个）

将静默 `axiom X : T` 机械替换为 `lemma X : T := by sorry`，使所有漏洞显性化。备份快照移至 `c:\proj2\archive\`（49 个文件）。删除错误文件 `stage_4_m.lean`。

### B. 主链自定义 axiom 清零（9/28）

`nontrivialZero_im_ne_zero`（ζ 在 (0,1) 无实零点）通过 Dirichlet eta 桥接降级为 theorem。**主链零自定义 axiom**。

### C. ZetaZeros 模块重构（9/28）

`zeroMultiplicity` opaque→def、`zeroMultiplicity_symmetry` 降级 theorem（带假设）等。

### D. mathlib 桥接（9/28）

`riemannZeta_conj`、`second_moment_gaussian_integral`、`cauchy_theorem_contour` → mathlib 现成定理。

### E. 新增 CompletedZeta.lean（9/28）

ξ(s) = (1/2)s(s-1)·completedRiemannZeta(s)，`xi_one_sub : ξ(1-s)=ξ(s)` 完整证明。

### F. 零重数对称性通关（9/29，`zeroMultiplicity_symmetry`）

函数方程 + Gamma 非零 + 因子非零 + 邻域内解析阶乘数链。

### G. η = (1-2^{1-s})·ζ 在 Re s>1 通关（9/29，`eta_eq_mul_riemannZeta`）

η(s)=∑(-1)^n/((n:ℂ)+1)^s = (1-2^(1-s))·ζ(s)。踩坑：`((n+1:ℕ):ℂ)` cast 一致性；`HasSum.congr_fun`；偶部/奇部 tsum_add。

### H. ζ 在 (0,1) 实段为负 通关（9/30，`riemannZeta_neg_on_Ioo`）

成对级数 `etaPaired`，Re s>0 逐项为正 → η(x)>0；身份定理把 `etaPaired = (1-2^(1-s))·ζ(s)` 从 Re s>1 延拓到连通域 `etaDomain`（四片凸集链式并，避开 s=1）。**`nontrivialZero_im_ne_zero` 彻底落地**。

### I. ContourIntegral :109 围道内重构（9/30，方案 i）

`:109` 从"全零点 tsum 假定理"重写为围道内版本：`contourIntegral = zetaZeroSide f − farZeroContribution f`（docstring 4 步留数蓝图：residue_theorem_general + 留数分类 m(ρ)、s=1 极点 −M[f](1)、围道内奇点 = czf ∪ {1}）；`:115` `(∑ρ∈czf m(ρ)M[f]ρ) + (−1)M[f](1) = zetaZeroSide f − farZeroContribution f` **真填**（unfold+ring）；`:128` 传递定理 rw 一条。

### J. ZetaZeros 重构（9/30，contourZeroFinset + farZeroContribution）

新增 `contourZeroFinset_finite`（紧集 closedBall(1/2,1) ∩ riemannZetaZeros 有限）、`contourZeroFinset`、`farZeroContribution`（tsum over ‖nontrivialZeroEnum n − 1/2‖ ≥ 1）、拆分版 `nontrivialZeroSum = czf 和 + farZeroContribution f`、`nontrivialZeroSum_localization` 重写。`:49` 枚举 sorry 保留并加注"【可改正的遗留，当前不用】"。修错记录：`:1129` closedBall 成员用 change+simpa（simp [B] 失败）；`:1142` 用 simp [coe_toFinset]（Set.Finite.mem_toFinset 失败）；`:1185` mp hρ 取 .1。

### K. Weil exact 重构（9/30，stage_4.lean）

`mollified_trace_equality` 保留 weylError 项；新增 **`weil_explicit_formula_exact : spectralSum = nontrivialZeroSum`**（admit，核心对偶假设）；新增 **`weyl_far_error_pairing : weylErrorTerm f = farZeroContribution f`**（真定理，从 exact+迹公式+截断 Weil 公式 ring 解方程）；删除 `weyl_error_vanishes`/`far_zero_vanishes`。修错：`rw [← h5]` 方向反，应 `rw [h5]`。

### L. 三篇源文献审计 + 目标下调（9/30，★ 本日定盘）

读全三篇：数值匹配2.pdf（8 页）、谱对偶论证9.pdf（18 页含附录 D）、保序双射定理6.pdf（10 页）。裁定：

1. **代数设定**：三篇均为 K=Q(√5)（Γ=PSL₂(𝒪_K)），**无 F=Q 设定**；第三篇明确放弃"Z_M(s)=ζ(s) 全域恒等"（数学上不可证明：类域论代数障碍 + 零点位置障碍——Z_M 零点在 Re(s)=1 谱线/长度谱，ζ_K 零点在临界带 + k≥1 因子）。**换 F=Q 无文献依据**。
2. **文章三处瑕疵（明天改文章的重点）**：
   - **A1 代数口径**：保序双射篇"实嵌入、无限体积、测地线在 ℍ² 截面" vs 谱对偶篇"紧致"——同一 Γ 两种设定；影响 Cont(f)（紧致无散射=0，非紧 Cont≠0）。
   - **A2 惯性素（最关键）**：谱对偶篇附录 D.5 惯性素按 W(p)f(log p) 并入"遍历有理素"——与保序双射篇 Nm(𝔭)=p² ⟹ ℓ=log p² 及数值篇表格（N=4,9）矛盾；修正后加权几何侧 = Σ_split W(p)f(log p) + Σ_inert W(p²)f(2log p) + W(5)f(log 5) ≠ Σ_p W(p)f(log p)——**ζ 显式公式匹配不成立，修正后对应 ζ_K 显式公式（K-GRH 级）**。
   - **A3 连续谱声明**：散射矩阵极点对应负偶数的陈述在紧致设定下无意义。
3. **目标下调（用户拍板）**：K-GRH（当前）→ RH（长期，需补桥）。Lean 侧：weil_explicit_formula_exact、all_zeros_on_critical_line、riemann_hypothesis 三处 docstring 标注目标状态（定理陈述暂保留占位，编译通过）。

---

## 剩余 sorry / admit 分布（活跃文件，2026-09-30 实测）

| 文件 | 数量 | 内容 |
|------|------|------|
| stage_4.lean | 21 | 主链估计 + 核心对偶 admit（weil_explicit_formula_exact 等） |
| ManifoldInfrastructure.lean | 11 | 流形分析估计 |
| HeatKernel.lean | 10 | 热核 HS 估计 |
| MellinInfrastructure.lean | 9 | Mellin 估计 |
| Interpolation.lean | 8 | 插值估计 |
| HeatKernelConvolution.lean | 8 | 卷积估计 |
| BijectionPhi/Basic.lean | 8 | 对偶映射分析 |
| stage_3.lean | 6 | Stage 3 桥接 |
| ContourIntegral.lean | 2 | :109 围道=留数和 admit、:143 素 Dirichlet 差 admit（:115 已真填） |
| CompletedZeta.lean | 0 | 整函数性、Gammaℝ 非零、零点等价已全部填完 |
| **ZetaZeros.lean** | **1** | **仅 `nontrivialZeroEnum_exists`（S 无限，用户保留，注"可改正遗留"）** |
| MollifiedFunction.lean | 1 | 磨光函数 |
| test_*.lean | ~20 | 测试文件（非交付） |

## 剩余 axiom（2 个，均不在 RH/K-GRH 主链）

| 位置 | 内容 |
|------|------|
| stage_4.lean:716 | `shimuraKernel_hilbert_schmidt` |
| stage_4.lean:5278 | `spectral_zero_set_match`（不喂 riemann_hypothesis） |

---

## 已知真缺口（mathlib 无基础设施）

1. **一般留数定理**：mathlib 无留数理论（`:109` 蓝图第一步依赖它，admit）。
2. **S 无限（Weyl/Hardy）**：`nontrivialZeroEnum_exists` 保留 sorry（S 可数已证）。
3. **Dolgopyat 指数混合**：几何兜底（非主证明，第三篇口径）。
4. **Arthur 迹公式 / JL 酉等价完整形式化**：表示论大工程，admit 级。
5. **A2 惯性素处理（文章层）**：决定 K-GRH 桥成立与否；修正后得到 ζ_K 显式公式。

（已闭合：ζ 在 (0,1) 无实零点——见 H；:115 围道留数和——见 I；主链零自定义 axiom——见 B。）

---

## 下一步

1. **（明天）改三篇文章**：A2（惯性素，决定 K-GRH 桥）> A1（口径统一）> A3（连续谱）；数值篇同步注释。
2. **Lean 侧 K-GRH 落地**：零点基础设施从 Riemann ζ 换成 ζ_K（需 Dedekind zeta / L(χ₅) / K 素理想 von Mangoldt 定义——mathlib 无，admit 级）；nontrivialZeroSum → ζ_K 零点侧。
3. 逐步降级 stage_4.lean 中的框架假设（21 个）。
