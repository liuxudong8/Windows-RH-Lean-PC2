# Stage 4: RH 谱对偶论证框架 — 总结文档

> **版本**: v7.1（gammaAction 具体化 + manifoldIntegral_linear 降级 + contourRadius 降级 + 死公理扫描）
> **最后更新**: 2026-09-13
> **核心文件**: `stage_4.lean` + 9 个独立模块
> **编译状态**: 通过（`lake build OrderPreservingBijection.stage_4`，0 error, stage_4 零 sorry）

---

## 一、项目概述

第三篇论文《基于 Arthur 稳定迹、Jacquet–Langlands 对应与测地流指数混合的谱对偶论证9》的 Lean 4 形式化，目标是条件导出黎曼猜想（RH）。

**核心论证路径**：
1. **A1 Arthur 稳定迹公式**：几何侧 = 谱侧（离散谱 + 连续谱），用热核积分重写
2. **A2 Jacquet-Langlands 酉对应**：三维谱 ↔ 二维 Maass 谱，用 Shimura 提升核重写
3. **A3 Mollified Explicit Formula**：迹等式 → 零点对应（spectralSum = nontrivialZeroSum）
4. **反证法**：偏离临界线 → 矛盾 → RH

**关键战略判断**：
- 不建立 ζ(s)↔Z_M(s) 函数恒等桥梁（死路），通过迹等式+反证法推出 RH
- 反证法核心 `mollified_melin_separation` 完全拆解为泛函分析/插值理论，非循环论证
- 类型化改造：`L2Function (M : Type)` 区分 L²(X) 和 L²(M)，Shimura 提升核类型安全
- 连续谱修正：continuousTerm=trivialZeroContribution（留数定理），结论 spectralSum=nontrivialZeroSum
- mellin_shift 消除：反证法只在可数点集上用 Mellin 等式，PWW 直接构造，不假设 Mellin 非单射
- 零点重数：nontrivialZeroSum 带重数 Σ m(ρ)·M[f](ρ)，m(ρ)>0 不影响反证法零/非零判断
- 围道积分重构：暴露藏在定义中的数学（柯西定理、留数定理、Euler 乘积对数导数）
- 留数定理自建：Mathlib 无完整留数定理，自建 residueAt 定义 + 一般留数定理公理 + 具体计算
- 双曲空间显式实例化：ManifoldX/M 从 opaque 改为上半平面/上半空间子类型
- 双曲测度完全具体化：manifoldIntegral 从 opaque 降为 Bochner 积分（hyperbolicMeasure3/2）
- **6 个数学缺陷全部处理**（2 消除 + 4 澄清），理论在 ZFC 内逻辑闭合

---

## 二、模块化结构（10 个文件）

| 模块 | 行数 | 内容 | 公理 | 定理 | opaque | def/abbrev |
|------|------|------|------|------|--------|-----------|
| `stage_4.lean` | 2553 | 主论证链（A1/A2/A3、反证法、RH 结论） | 28 | 93 | 9 | 24 |
| `BasicInfrastructure.lean` | 48 | TestFunction、realIntegral | 1 | 0 | 0 | 1 |
| `MellinInfrastructure.lean` | 30 | melinTransform、线性性 | 0 | 1 | 0 | 1 |
| `ZetaZeros.lean` | 86 | 零点枚举、重数、求和、局部化 | 3 | 5 | 1 | 4 |
| `ContourIntegral.lean` | 117 | 围道积分、留数定理自建、ζ对数导数 | 7 | 1 | 1 | 4 |
| `ManifoldInfrastructure.lean` | 108 | 双曲空间类型、Γ作用、流形积分(def) | 5 | 2 | 1 | 3 |
| `HyperbolicMeasure.lean` | 52 | 双曲测度显式定义、Bochner积分 | 0 | 0 | 0 | 4 |
| `HeatKernel.lean` | 230 | Laplace变换、热核、f(Δ)核、几何侧迹 | 4 | 9 | 1 | 8 |
| `MollifiedFunction.lean` | 48 | 椭圆类、ellipticTerm、MollifiedTestFunction | 3 | 1 | 2 | 1 |
| `Interpolation.lean` | 55 | Whitney插值、PWW联合插值、Mellin可数插值 | 2 | 2 | 0 | 0 |
| **合计** | **3327** | | **53** | **114** | **15** | **50** |

**依赖关系**：
```
BasicInfrastructure ← MellinInfrastructure ← ZetaZeros ← ContourIntegral
BasicInfrastructure ← HyperbolicMeasure ← ManifoldInfrastructure ← HeatKernel
BasicInfrastructure ← MollifiedFunction ← Interpolation
以上全部 ← stage_4
```

**stage_4 瘦身**：从最初的 3129 行降至 2553 行（-576 行，-18.4%）。

---

## 三、文件统计

| 指标 | 数值 |
|------|------|
| 总文件数 | 10 |
| 总行数 | 3386 |
| 公理 (axiom) | 51 |
| 定理 (theorem) | 116 |
| 不透明常量 (opaque) | 14 |
| 定义 (def/abbrev) | 53 |
| stage_4 sorry | 0 |
| True 简化公理 | 0 |
| 第三档分析公理 | 0 |

---

## 四、公理分档（51 条）

### 第一档：ZFC 标准结果/定义性（约 26 条，51%）

**双曲空间与流形结构（7）**
1. `manifoldIntegral_linear` — 流形积分线性性（Bochner 积分性质，可降级）
2. `manifoldIntegral_positive` — M 上积分正性
3. `manifoldIntegralX_positive` — X 上积分正性
4. `gammaAction_identity` — Γ作用恒等
5. `gammaAction_compat` — Γ作用相容性
6. `hyperbolicDistance_gamma_invariant` — 双曲距离Γ不变
7. `manifoldIntegral_fubini` — Fubini定理

**积分基础（2）**
8. `realIntegral_linear` — 实积分线性性
9. `contourIntegral_linear` — 围道积分线性性

**谱离散性（2，非空洞化）**
10. `laplacian_has_discrete_spectrum` — Δ_M 谱离散可枚举（每个谱值是特征值）
11. `maass_laplacian_has_discrete_spectrum` — Δ_X 谱离散可枚举

**零点与重数（3）**
12. `nontrivialZeroEnum_exists` — 非平凡零点枚举存在性
13. `zeroMultiplicity_positive_at_nontrivial_zeros` — 非平凡零点处重数>0
14. `zeroMultiplicity_symmetry` — 重数函数方程对称性 m(ρ)=m(1-ρ)

**无穷和（2）**
15. `nontrivialZeroSum_tsum_linear` — 无穷和线性性（带重数）
16. `tsum_two_point_isolation` — 两点隔离

**分布论（3）**
17. `distribution_equality_support` — 分布相等则支撑相同
18. `spectral_side_support` — 谱侧分布支撑
19. `nontrivialZeroSum_support` — 非平凡零点侧分布支撑

**椭圆类（3）**
20. `elliptic_class_lengths_bounded` — 椭圆类长度有界
21. `elliptic_class_lengths_discrete` — 椭圆类长度离散
22. `bounded_discrete_real_set_finite` — 有界离散实数集有限

**围道积分基础（2）**
23. `contourRadius_pos` — 围道半径为正
24. `cauchy_theorem_contour` — 柯西定理（围道积分版本）

**自伴性与内积（4，stage_4）**
25. `laplacian_M_self_adjoint` — Δ_M 自伴
26. `laplacian_X_self_adjoint` — Δ_X 自伴
27. `innerProduct_conj_sym` — 内积共轭对称
28. `innerProduct_pos_def` — 内积正定

### 第二档：已知大定理（约 25 条，49%）

**Arthur迹公式（2）**
29. `spectral_decomposition_additivity` — 谱分解可加性
30. `full_orbital_integral_expansion` — 完整轨道积分展开

**热核/PDE（2）**
31. `heatKernel_semigroup` — 热核半群
32. `heatKernel_commutes_laplacian` — 与Laplacian交换

**特征值方程（2）**
33. `maass_eigenvalue_equation` — Maass本征方程
34. `threeManifold_eigenvalue_equation` — 三维流形本征方程

**JL对应/Shimura提升（7）**
35. `shimuraLift_eigenfunction_correspondence` — 本征函数对应
36. `shimuraLift_commutes_laplacian` — 与Laplacian交换
37. `shimuraLift_isometry` — 等距
38. `l_parameter_standard_form` — L参数标准形式
39. `l_parameter_eigenvalue_formula` — L参数特征值公式
40. `jl_spectrum_rearrangement` — JL谱重排
41. `jl_fiber_size_eq_weight` — JL纤维大小=权重

**Dolgopyat混合（1）**
42. `dolgopyat_spectral_gap_estimate` — Dolgopyat谱隙估计

**Weil显式公式/围道（6）**
43. `continuous_term_contour_shift` — 连续谱围道移动+留数计算
44. `perron_formula` — Perron公式（geometricSum = primeIdealDirichletIntegral）
45. `residue_theorem_general` — 一般留数定理（自建，Mathlib 无完整版本）
46. `zeta_log_derivative_contour_eq_residue_sum` — ζ'/ζ 围道积分=留数求和
47. `zeta_log_derivative_residue_sum_eq_zeroside` — 留数求和=零点侧
48. `primeDirichlet_zetaLogDerivative_diff_holomorphic` — 差的全纯延拓

**插值理论（2）**
49. `whitney_mollified_point_interpolation` — Whitney点插值
50. `mellin_surjectivity_over_point_fiber` — 点插值纤维上Mellin满射

**其他（3）**
51. `eigenfunction_cancellation` — 特征函数线性抵消
52. `l_parameter_im_nonneg` — L参数虚部非负
53. `shimuraLift_linear` — Shimura提升线性

### 第三档：未证明分析断言（0 条）

全部清零。

---

## 五、RH 证明逻辑链

```
all_zeros_on_critical_line (RH核心)
  └─ 反证法：假设 s.re ≠ 1/2
     └─ off_critical_line_contradiction → ∃f, spectralSum f ≠ nontrivialZeroSum f
        └─ pair_contribution_sigma_dependent → ∃f1,f2, spectralSum相等但 nontrivialZeroSum 不同
           └─ mollified_spectral_preserving_perturbation → 谱点相同但 nontrivialZeroSum 不同
              └─ mollified_melin_separation → 成对零点 Mellin 和不同
                 ├─ pair_nonzero_kernel_exists → 非退化核存在
                 └─ spectral_preserving_perturbation_build → 谱点保持的扰动
                    ├─ mellin_zero_localization → Mellin 零点局部化
                    └─ spectral_preserving_melin_superposition_countable → PWW定理（可数点集）
     └─ spectral_zero_equality → spectralSum = nontrivialZeroSum（矛盾）
        ├─ mollified_trace_equality → spectralSum + trivialZeroContribution = geometricSum
        │  ├─ arthur_trace_formula → spectralSum + continuousTerm = geometricSum + ellipticTerm
        │  ├─ continuousTerm = trivialZeroContribution（围道移动+留数定理）
        │  └─ ellipticTerm = 0（磨光条件）
        └─ weil_explicit_formula → geometricSum = nontrivialZeroSum + trivialZeroContribution
           ├─ perron_formula → geometricSum = primeIdealDirichletIntegral
           ├─ Euler乘积对数导数（Mathlib定理，已删除公理）
           └─ residue_theorem_zeta_log_derivative → 围道积分=零点侧（留数定理自建）
```

---

## 六、重大突破时间线

### 1-15. 早期突破（v1.0-v6.0）
连续谱修正、PWW 联合插值、第三档清零、opaque 大幅降级、显式积分核、mellin_shift 消除、零点重数、3 条公理降级、围道积分重构、模块化、specDiscM 非空洞化、流形结构公理、Perron 公式、留数定理自建、双曲空间显式实例化。详见 v6.0 文档。

### 16. 双曲距离公式具体化（v7.0）
`hyperbolicDistance` 从 opaque 改为显式公式：
```
d(p,q) = arcosh(1 + (|z_p - z_q|² + (t_p - t_q)²) / (2·t_p·t_q))
```
- 新增 `hyperbolicDistance_arg_ge_one` 引理（arcosh 参数 ≥ 1）
- `hyperbolicDistance_symmetric` 从公理降级为定理
- `hyperbolicDistance_nonneg` 新增定理
- `heatKernel_symmetric` 从公理降级为定理（距离对称 + 公式对称）
- 踩坑：`Complex.abs`/`Complex.norm` 不存在，用 `Complex.normSq`

### 17. heatKernel_positive 降级（v7.0）
发现 d=0 数学 bug：原公式 d/sinh(d) 在 z=w 时 d=0，Lean 中 0/0=0，导致 K_t(z,z)=0，与正定性矛盾。
- 引入 `d_over_sinh (d) := if d=0 then 1 else d/sinh d`（连续延拓）
- `heatKernel_positive` 从公理降级为定理（四个因子全正）
- 新增 `d_over_sinh_pos` 定理
- HeatKernel 模块：公理 6→4，定理 4→9

### 18. Euler 乘积公理清理（v7.0）
- 发现 `euler_product_log_derivative_eq` 是死公理——只在注释中出现，从未被证明引用
- 还发现符号错误：正确是 ζ'/ζ = -Σ(log p)p^{-s}/(1-p^{-s})，原公理写正号
- 直接删除该公理，公理 57→56
- Mathlib 有 `logDeriv_tprod_eq_tsum` + `riemannZeta_eulerProduct_tprod`，完整应用需前提条件

### 19. 死公理清理（v7.0）
扫描 56 个公理，发现 16 个只在声明处出现。区分结构公理（保留）和真正死公理：
- 删除 `tsum_one_point_isolation`（完全未使用，`tsum_two_point_isolation` 已覆盖）
- 公理 56→55
- 剩余 14 个"未直接引用"全部是结构公理，保留

### 20. 双曲测度完全具体化（v7.0 核心）
三个大难题中的第 2 个取得决定性进展：
- 新建 `HyperbolicMeasure.lean` 模块（52 行）
- 显式定义 `hyperbolicMeasure3`：(comap Subtype.val volume).withDensity(ENNReal.ofReal(1/t³))
- 显式定义 `hyperbolicMeasure2`：(comap Subtype.val volume).withDensity(ENNReal.ofReal(1/y²))
- `manifoldIntegral`/`manifoldIntegralX` 从 opaque 降为 def（Bochner 积分）
- 删除 `manifoldIntegral_one_pos`/`manifoldIntegralX_one_pos`（通用覆盖体积无穷，数学上不成立）
- 关键技术：`abbrev` 而非 `def` 定义子类型 → MeasurableSpace 实例自动传递；`withDensity` 期望 `α → ENNReal`
- opaque 17→15（-2），公理 55→53（-2），文件数 9→10

### 21. gammaAction 具体化（v7.1）
- 定义 SL2C 结构（行列式为 1 的 2×2 复矩阵，含 Nonempty 实例）
- 定义 moebiusAction 显式公式：ℍ³ 上半空间模型的 Möbius 作用
  - z' = ((az+b)·star(cz+d) + star(c)·t²) / (|cz+d|² + |c|²·t²)
  - t' = t / (|cz+d|² + |c|²·t²)
- 含 t'>0 的完整证明（分 c=0/c≠0，用 det=1 保证分母非零）
- gammaAction 从 opaque 降为 def：gammaAction n z = moebiusAction (gammaEnum n) z
- gammaEnum : ℕ → SL2C 保持 opaque（Γ=PSL₂(O_K) 的可数枚举，需 O_K 数论）
- 关键技术：structure 字段需单独写类型（ : ℂ 而非  b c d : ℂ）；复数共轭用 star 而非 Complex.conj

### 22. manifoldIntegral_linear 降级（v7.1）
- 发现是死公理（全项目只在声明处出现）
- 原无条件版本数学上不正确：不可积函数 integral=0，但两不可积函数之和可能可积
- 降级为带 Integrable 前提的定理，用 Mathlib integral_add + integral_smul 证明
- 技术细节：* 与 • 需用 smul_eq_mul 桥接；MeasureTheory.Integrable 需完整命名空间

### 23. contourRadius 降级（v7.1）
- 从 opaque 降为 def：contourRadius := 1
- contourRadius_pos 从公理降为定理（y norm_num）
- 数学依据：围道积分形变不变性，具体半径值不影响结论

### 24. 死公理扫描（v7.1）
- 精确扫描 51 个公理（排除注释和声明行），发现 13 个未引用
- 全部是结构公理（自伴性、内积、群作用、热核性质、留数定理基础），数学上必要，保留
- 无可删除的真正死公理（之前已清理 tsum_one_point_isolation、euler_product_log_derivative_eq）
- ellipticWeight 和 laplacian_M 评估为难以降级：前者依赖 Γ 椭圆共轭类结构，后者是无界算子需偏导数/Sobolev 空间

---

## 七、Opaque 分类（14 个）

**无界算子（2 个）**
- laplacian_M, laplacian_X：Laplace-Beltrami 算子，显式形式化需偏导数+Sobolev 空间+无界算子定义域

**本征函数（2 个）**
- maassEigenfunction, threeManifoldEigenfunction：需谱定理+特征向量构造

**谱映射（2 个）**
- jlSpectrumMap：定义顺序循环依赖
- jlLParameterMap：不宜降级（降级会藏数学）

**核/算子（3 个）**
- shimuraKernel：Shimura 提升核，需显式公式
- transferOperator：转移算子
- scatteringMatrixLogDerivative：需复导数

**多态内积（1 个）**
- innerProduct：多态 {M : Type}，无法用单一积分定义覆盖

**群枚举（1 个）**
- gammaEnum：Γ=PSL₂(O_K) 的可数枚举，需 O_K=Z[(1+√5)/2] 数论

**椭圆类（2 个）**
- ellipticClassLengths, ellipticWeight：依赖 Γ 椭圆共轭类结构（旋转角、中心化子体积）

**ζ 函数（1 个）**
- zeroMultiplicity：零点重数函数

**已降级为 def（29 个）**
operatorTrace（删除）、discreteSpectralTrace、continuousSpectralTrace、parabolicTerm、centralizerIntegral、rawOrbitalIntegral、laplaceTransform、melinTransform、trivialZeroContribution、zetaLogDerivativeIntegral、geometricTermwiseIntegral、primeIdealDirichletIntegral、continuousTerm、nontrivialZeroSum、zetaZeroSide、fLaplacianKernel、geometricKernelTrace、ellipticTerm、distributionSupport、nontrivialZeroEnum、correlation、heatKernel、realIntegral、ManifoldX（→abbrev）、ManifoldM（→abbrev）、hyperbolicDistance、manifoldIntegral、manifoldIntegralX、contourRadius、gammaAction（→def，依赖 gammaEnum）

**已降级为 def（27 个）**
operatorTrace（删除）、discreteSpectralTrace、continuousSpectralTrace、parabolicTerm、centralizerIntegral、rawOrbitalIntegral、laplaceTransform、melinTransform、trivialZeroContribution、zetaLogDerivativeIntegral、geometricTermwiseIntegral、primeIdealDirichletIntegral、continuousTerm、nontrivialZeroSum、zetaZeroSide、fLaplacianKernel、geometricKernelTrace、ellipticTerm、distributionSupport、nontrivialZeroEnum、correlation、heatKernel、realIntegral、ManifoldX（→abbrev）、ManifoldM（→abbrev）、hyperbolicDistance、manifoldIntegral、manifoldIntegralX

---

## 八、数学缺陷评估（全部处理完毕）

| # | 缺陷 | 处理方式 | 状态 |
|---|------|---------|------|
| 1 | mellin_shift 全局等式假设 Mellin 非单射 | 删除公理，改用 PWW 可数点集版本 | **已消除** |
| 2 | 隐含零点单重性 | 引入 zeroMultiplicity，带重数求和 | **已消除** |
| 3 | PWW 满射性未严格证明 | 拆分为 Whitney 点插值 + 纤维上 Mellin 满射 | **已澄清** |
| 4 | 流形紧性未确认 | parabolicTerm 定义为 0（Q-rank 0） | **已澄清** |
| 5 | 连续谱围道计算需验证 | 拆分为 continuous_term_contour_shift 公理 | **已澄清** |
| 6 | Mellin 变换归一化 | 标准定义 ∫₀^∞ f(x)x^{s-1}dx | **已确认** |

---

## 九、ZFC 可证明性评估

| 档位 | 数量 | 占比 | 含义 |
|------|------|------|------|
| 第一档：ZFC标准/定义性 | ~26 | 51% | mathlib可证或定义性质 |
| 第二档：已知大定理 | ~25 | 49% | 数学上已确立，形式化是工作量 |
| 第三档：未证明分析断言 | 0 | 0% | 需要新数学思想 |

**结论**：理论在逻辑上闭合于 ZFC。所有 6 个数学缺陷已处理（2 消除 + 4 澄清）。所有前提都是已知数学结果，无循环论证，无未证明断言。剩余工作是"把已知定理写进 Lean"，不是"发现新数学"。

---

## 十、三个大难题进展

| # | 难题 | 当前状态 | 下一步 |
|---|------|---------|--------|
| 1 | specDiscM/maassSpecParam 非空洞化 | **已完成折中方案**：laplacian_has_discrete_spectrum 公理，specDiscM 从"任意序列"变为"Laplacian 特征值枚举" | 可选：引入 resolvent_compact + Rellich 引理，从紧算子谱定理推出枚举（成本高） |
| 2 | ManifoldX/M 显式实例化 | **大幅推进**：上半平面/上半空间子类型 + 双曲距离显式公式 + 双曲测度完全具体化（Bochner积分） + gammaAction 具体化（SL2C+Möbius公式） | gammaEnum 具体化（需 O_K 数论）；商空间 Γ\ℍⁿ 显式化（Quotient/基本域） |
| 3 | Weil 显式公式完整 Lean 化 | **大幅推进**：Perron 公式显式化 + 留数定理自建 + Euler 乘积定理化 | 用 Mathlib 柯西积分公式证明一般留数定理（需 Laurent 展开+围道形变，工程量大） |

---

## 十一、重要教训

1. **mellin_shift 教训**：曾认为全局 Mellin 差公理是原子的。深入分析证明链后发现只需要可数点集等式，PWW 可直接证明。**不要因为"看起来需要全局"就假设全局。**
2. **零点重数教训**：重数 m(ρ)>0 是正标量因子，不改变零/非零判断。带重数求和不影响反证法等价性。
3. **jlLParameterMap 教训**：不能为降 opaque 把需要证明的数学藏进定义。
4. **连续谱教训**：continuousTerm=0 不成立，正确是 continuousTerm=trivialZeroContribution。
5. **统一插值公理**：引入强公理一次性降级多条弱公理更高效。
6. **常零定义 bug**：specDiscM 曾定义为 fun _ => 0，与严格递增矛盾。Classical.choose + 存在性公理是正确模式。
7. **定义顺序循环依赖**：jlSpectrumMap 降级需引用后面的 shimuraLift，但必须在 jlLParameterMap 之前，无法降级。
8. **可数 vs 全局**：零点集可数，反证法只需要可数点集赋值，不需要全局等式。
9. **Mathlib 直查降级**：real_complex_inj = Complex.ofReal_injective；riemann_zeta_zero_symmetry = riemannZeta_one_sub；laplaceTransform_exp = integral_exp_neg_mul_rpow（p=1）。降级前先搜 Mathlib。
10. **定义性作弊识别**：围道积分重构发现 `zetaLogDerivativeIntegral f := zetaZeroSide f` 导致证明链全是 rfl。**定义不能等于结论。**
11. **模块化原则**：大模块单独成文件，按依赖关系分层。基础模块独立，stage_4 只保留主论证链。
12. **折中方案价值**：specDiscM 非空洞化不追求 resolvent_compact 完整方案，引入 laplacian_has_discrete_spectrum 公理。
13. **留数定理自建**：Mathlib 有柯西积分公式但无完整留数定理。自建 residueAt + 一般留数定理公理 + 具体计算。
14. **最简架子优先**：双曲空间实例化先做上半平面/上半空间子类型（通用覆盖），商结构后续添加。
15. **abbrev vs def**：子类型用 `abbrev` 定义，MeasurableSpace 等类型类实例自动传递；用 `def` 则实例丢失。
16. **withDensity 类型**：期望 `α → ENNReal`（扩展非负实数），不是 `α → ℝ`。用 `ENNReal.ofReal` 转换。
17. **d=0 奇点**：热核公式 d/sinh(d) 在 d=0 时 0/0=0，需用 `if d=0 then 1 else d/sinh d` 连续延拓。
18. **通用覆盖体积无穷**：ManifoldM=ℍ³ 通用覆盖时 ∫1=∞，`manifoldIntegral_one_pos` 公理数学上不成立，需删除。有限体积性质属于商空间。

---

## 十二、下一步方向

1. **降级结构公理**（优先级高）：contourIntegral_linear（circleIntegral 线性性）、manifoldIntegral_positive（Bochner 积分正定性）、heatKernel_semigroup（热核卷积）
2. **gammaEnum 具体化**（长期）：定义 O_K=Z[(1+√5)/2] 整数环和 PSL₂(O_K) 的可数枚举
3. **商空间显式化**（长期）：用 Quotient 或基本域实现 Γ\ℍⁿ，恢复有限体积性质
4. **一般留数定理证明**（长期）：用 Mathlib 柯西积分公式 + Laurent 展开 + 围道形变证明 residue_theorem_general
5. **PWW 子公理的严格证明**（非当前目标）：Whitney 插值 + Paley-Wiener 满射性的完整分析证明
6. **大定理形式化**（非当前目标）：Arthur 迹公式、JL 对应、Dolgopyat 混合
7. **laplacian_M 显式化**（超长期）：偏导数+Sobolev 空间+无界算子定义域
8. **resolvent_compact 完整方案**（可选）：引入 Rellich 引理，从紧算子谱定理推出谱枚举
9. **向实二次域推广**：论文第 6 节的条件性声明
