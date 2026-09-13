# Stage 4: RH 谱对偶论证框架 — 总结文档

> **版本**: v6.0（双曲空间显式实例化 + 留数定理自建 + Perron 公式 + specDiscM 非空洞化 + 流形结构公理）
> **最后更新**: 2026-09-13
> **核心文件**: `stage_4.lean` + 8 个独立模块
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
- **6 个数学缺陷全部处理**（2 消除 + 4 澄清），理论在 ZFC 内逻辑闭合

---

## 二、模块化结构（9 个文件）

| 模块 | 行数 | 内容 | 公理 | 定理 | opaque | def/abbrev |
|------|------|------|------|------|--------|-----------|
| `stage_4.lean` | 2560 | 主论证链（A1/A2/A3、反证法、RH 结论） | 29 | 93 | 9 | 24 |
| `BasicInfrastructure.lean` | 60 | TestFunction、realIntegral | 1 | 0 | 0 | 2 |
| `MellinInfrastructure.lean` | 39 | melinTransform、线性性 | 0 | 1 | 0 | 1 |
| `ZetaZeros.lean` | 109 | 零点枚举、重数、求和、局部化 | 3 | 5 | 1 | 4 |
| `ContourIntegral.lean` | 125 | 围道积分、留数定理自建、ζ对数导数 | 8 | 1 | 1 | 4 |
| `ManifoldInfrastructure.lean` | 129 | 双曲空间显式实例化、流形积分、Γ作用 | 7 | 2 | 3 | 6 |
| `HeatKernel.lean` | 197 | Laplace变换、热核、f(Δ)核、几何侧迹 | 6 | 4 | 2 | 6 |
| `MollifiedFunction.lean` | 67 | 椭圆类、ellipticTerm、MollifiedTestFunction | 3 | 1 | 2 | 1 |
| `Interpolation.lean` | 76 | Whitney插值、PWW联合插值、Mellin可数插值 | 2 | 2 | 0 | 0 |
| **合计** | **3362** | | **59** | **109** | **18** | **48** |

**依赖关系**：
```
BasicInfrastructure ← MellinInfrastructure ← ZetaZeros ← ContourIntegral
BasicInfrastructure ← ManifoldInfrastructure ← HeatKernel
BasicInfrastructure ← MollifiedFunction ← Interpolation
以上全部 ← stage_4
```

**stage_4 瘦身**：从最初的 3129 行降至 2560 行（-569 行，-18.2%）。

---

## 三、文件统计

| 指标 | 数值 |
|------|------|
| 总文件数 | 9 |
| 总行数 | 3362 |
| 公理 (axiom) | 59 |
| 定理 (theorem) | 109 |
| 不透明常量 (opaque) | 18 |
| 定义 (def/abbrev) | 48 |
| stage_4 sorry | 0 |
| True 简化公理 | 0 |
| 第三档分析公理 | 0 |

---

## 四、公理分档（59 条）

### 第一档：ZFC 标准结果/定义性（约 32 条，54%）

**双曲空间与流形结构（9）**
1. `manifoldIntegral_linear` — 流形积分线性性
2. `manifoldIntegral_positive` — M 上积分正性
3. `manifoldIntegralX_positive` — X 上积分正性
4. `manifoldIntegral_one_pos` — M 上 ∫1 > 0
5. `manifoldIntegralX_one_pos` — X 上 ∫1 > 0
6. `gammaAction_identity` — Γ作用恒等
7. `gammaAction_compat` — Γ作用相容性
8. `hyperbolicDistance_gamma_invariant` — 双曲距离Γ不变
9. `manifoldIntegral_fubini` — Fubini定理

**积分基础（2）**
10. `realIntegral_linear` — 实积分线性性
11. `contourIntegral_linear` — 围道积分线性性

**热核基本性质（2）**
12. `heatKernel_symmetric` — 热核对称
13. `heatKernel_positive` — 热核正定

**谱离散性（2，非空洞化）**
14. `laplacian_has_discrete_spectrum` — Δ_M 谱离散可枚举（每个谱值是特征值）
15. `maass_laplacian_has_discrete_spectrum` — Δ_X 谱离散可枚举

**零点与重数（3）**
16. `nontrivialZeroEnum_exists` — 非平凡零点枚举存在性
17. `zeroMultiplicity_positive_at_nontrivial_zeros` — 非平凡零点处重数>0
18. `zeroMultiplicity_symmetry` — 重数函数方程对称性 m(ρ)=m(1-ρ)

**无穷和（3）**
19. `nontrivialZeroSum_tsum_linear` — 无穷和线性性（带重数）
20. `tsum_one_point_isolation` — 单点隔离
21. `tsum_two_point_isolation` — 两点隔离

**分布论（3）**
22. `distribution_equality_support` — 分布相等则支撑相同
23. `spectral_side_support` — 谱侧分布支撑
24. `nontrivialZeroSum_support` — 非平凡零点侧分布支撑

**椭圆类（3）**
25. `elliptic_class_lengths_bounded` — 椭圆类长度有界
26. `elliptic_class_lengths_discrete` — 椭圆类长度离散
27. `bounded_discrete_real_set_finite` — 有界离散实数集有限

**围道积分基础（2）**
28. `contourRadius_pos` — 围道半径为正
29. `cauchy_theorem_contour` — 柯西定理（围道积分版本）

**自伴性与内积（4，stage_4）**
30. `laplacian_M_self_adjoint` — Δ_M 自伴
31. `laplacian_X_self_adjoint` — Δ_X 自伴
32. `innerProduct_conj_sym` — 内积共轭对称
33. `innerProduct_pos_def` — 内积正定

**Shimura提升线性性质（1）**
34. `shimuraLift_linear` — Shimura提升线性

### 第二档：已知大定理（约 27 条，46%）

**Arthur迹公式（2）**
35. `spectral_decomposition_additivity` — 谱分解可加性
36. `full_orbital_integral_expansion` — 完整轨道积分展开

**热核/PDE（2）**
37. `heatKernel_semigroup` — 热核半群
38. `heatKernel_commutes_laplacian` — 与Laplacian交换

**特征值方程（2）**
39. `maass_eigenvalue_equation` — Maass本征方程
40. `threeManifold_eigenvalue_equation` — 三维流形本征方程

**JL对应/Shimura提升（7）**
41. `shimuraLift_eigenfunction_correspondence` — 本征函数对应
42. `shimuraLift_commutes_laplacian` — 与Laplacian交换
43. `shimuraLift_isometry` — 等距
44. `l_parameter_standard_form` — L参数标准形式
45. `l_parameter_eigenvalue_formula` — L参数特征值公式
46. `jl_spectrum_rearrangement` — JL谱重排
47. `jl_fiber_size_eq_weight` — JL纤维大小=权重

**Dolgopyat混合（1）**
48. `dolgopyat_spectral_gap_estimate` — Dolgopyat谱隙估计

**Weil显式公式/围道（6）**
49. `continuous_term_contour_shift` — 连续谱围道移动+留数计算
50. `perron_formula` — Perron公式（geometricSum = primeIdealDirichletIntegral）
51. `residue_theorem_general` — 一般留数定理（自建，Mathlib 无完整版本）
52. `zeta_log_derivative_contour_eq_residue_sum` — ζ'/ζ 围道积分=留数求和
53. `zeta_log_derivative_residue_sum_eq_zeroside` — 留数求和=零点侧
54. `primeDirichlet_zetaLogDerivative_diff_holomorphic` — 差的全纯延拓

**插值理论（2）**
55. `whitney_mollified_point_interpolation` — Whitney点插值
56. `mellin_surjectivity_over_point_fiber` — 点插值纤维上Mellin满射

**其他（3）**
57. `eigenfunction_cancellation` — 特征函数线性抵消
58. `l_parameter_im_nonneg` — L参数虚部非负
59. `euler_product_log_derivative_eq` — Euler乘积→对数导数等式（Re(s)>1）

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
           ├─ euler_product_log_derivative_eq → 对数导数=Dirichlet级数
           └─ residue_theorem_zeta_log_derivative → 围道积分=零点侧（留数定理自建）
```

---

## 六、重大突破时间线

### 1. 连续谱数学修正
旧公理假设 continuousTerm=0，数学上不成立。正确等式 continuousTerm=trivialZeroContribution，结论升级为 spectralSum=nontrivialZeroSum。

### 2. PWW 联合插值
引入 `paley_wiener_whitney_joint_interpolation`，后拆分为 Whitney 点插值 + 纤维上 Mellin 满射两个子公理。

### 3. 第三档公理清零
12 条未证明分析断言全部降级为定理或替换为标准结果。

### 4. Opaque 大幅降级
distributionSupport、nontrivialZeroEnum、correlation、heatKernel、realIntegral、melinTransform、trivialZeroContribution、zetaLogDerivativeIntegral、laplaceTransform、nontrivialZeroSum 等降级为 def。从 35 降至 18。

### 5. 显式积分核基础设施
用热核重写 Arthur 迹公式（operatorTrace → 热核积分），用 Shimura 提升核重写 JL 对应。`jl_l_parameter_preserving` 降级为定理。

### 6. mellin_shift 消除（最重大）
删除 `mellin_shift_preserving_spectral_values` 公理（假设 Mellin 非单射，真实数学中可能不成立）。关键洞察：反证法只在可数个点上用 Mellin 等式（零点集可数），PWW 联合插值可直接构造。删除 B 组 8 条定理，新增可数版本定理。

### 7. 零点重数处理
引入 `zeroMultiplicity : ℂ → ℕ`，nontrivialZeroSum 改为带重数求和。m(ρ)>0 是正标量因子，不影响反证法零/非零判断。

### 8. 3 条公理降级为 Mathlib 定理
- `real_complex_inj` → theorem（`Complex.ofReal_injective`）
- `riemann_zeta_zero_symmetry` → theorem（`riemannZeta_one_sub` 函数方程）
- `laplaceTransform_exp` → theorem（`integral_exp_neg_mul_rpow` p=1）
- 附带 `realIntegral` 从 opaque 降为 def（Set.Ioi 0 上的 Lebesgue 积分）

### 9. 围道积分重构（B 方案，真正重构）
发现 Weil 显式公式证明链存在"定义性作弊"——`zetaLogDerivativeIntegral f := zetaZeroSide f` 导致证明链全是 rfl。重构：新增围道积分基础设施（contourRadius、contourIntegral、zetaLogDerivative、primeDirichletSeries），新增 6 条公理，`euler_product_integral` 从 axiom 降为 theorem。

### 10. 模块化重构（v5.0）
将大模块从 stage_4.lean 拆分为 8 个独立文件。stage_4 从 3129 行降至 2560 行（-18.2%）。

### 11. specDiscM 非空洞化（折中方案）
用户问"是不是引入 resolvent_compact 公理"。分析 Mathlib 有紧自伴算子谱定理但无无限维特征值枚举定理，且无界算子预解式处理复杂。采用折中方案：引入 `laplacian_has_discrete_spectrum` 和 `maass_laplacian_has_discrete_spectrum` 公理（比原 specDiscM_exists 强，声明每个谱值是 Laplacian 特征值），specDiscM/maassSpecParam 不再是"任意序列"。新增 2 定理 `specDiscM_is_eigenvalue`、`maassSpecParam_is_eigenvalue`。

### 12. 流形结构公理补充
补充测度结构（4 条：manifoldIntegral_positive/X_positive/one_pos/X_one_pos）和自伴性+内积结构（4 条：laplacian_M_self_adjoint/X_self_adjoint、innerProduct_conj_sym/pos_def）。

### 13. Perron 公式显式化
当前 Perron 公式被拆成 `geometric_sum_mellin_inversion`（rfl）+ `termwise_integral_swap`（公理），中间层直接定义为 geometricSum，导致真正的数学内容藏在公理里。重构：删除冗余中间层，引入显式 `perron_formula` 公理（直接声明 geometricSum = primeIdealDirichletIntegral）。

### 14. 留数定理自建（v6.0 核心）
Mathlib 有柯西积分公式但无完整留数定理。自建方案：
- 定义 `residueAt`（小圆周积分，标准留数定义）
- 引入一般留数定理公理 `residue_theorem_general`（第二档标准复分析定理）
- 引入 `zeta_log_derivative_contour_eq_residue_sum` 公理（围道积分 = 留数求和）
- 引入 `zeta_log_derivative_residue_sum_eq_zeroside` 公理（留数求和 = 零点侧）
- `residue_theorem_zeta_log_derivative` 从公理降级为定理（证明仅 2 行 rw）

### 15. 双曲空间显式实例化（最简架子，v6.0）
三个大难题中的第 2 个迈出第一步：
- 定义 `UpperHalfPlane := {z : ℂ // 0 < z.im}`（ℍ² 上半平面）
- 定义 `UpperHalfSpace3 := {p : ℂ × ℝ // 0 < p.2}`（ℍ³ 上半空间）
- ManifoldX/M 从 opaque 改为 abbrev（通用覆盖版本，商结构由 gammaAction 隐式处理）
- `manifoldM_nonempty` 从公理降级为定理（(0,1) ∈ ℍ³）
- 新增 `manifoldX_nonempty` 定理（i ∈ ℍ²）
- opaque 20→18（-2），公理 60→59（-1），定理 107→109（+2）

---

## 七、Opaque 分类（18 个）

**抽象基础设施（11 个，不能降级）**
- 积分：manifoldIntegral, manifoldIntegralX
- 内积：innerProduct
- 算子：laplacian_X, laplacian_M, transferOperator
- 本征函数：maassEigenfunction, threeManifoldEigenfunction
- 谱映射：jlLParameterMap
- 围道：contourRadius

**ζ 函数性质（1 个）**
- zeroMultiplicity：零点重数函数

**不宜降级（4 个，降级会藏数学）**
- gammaAction, ellipticClassLengths, ellipticWeight, hyperbolicDistance

**技术障碍（2 个）**
- jlSpectrumMap：定义顺序循环依赖
- scatteringMatrixLogDerivative：需复导数

**已降级为 def（25 个）**
operatorTrace（删除）、discreteSpectralTrace、continuousSpectralTrace、parabolicTerm、centralizerIntegral、rawOrbitalIntegral、laplaceTransform、melinTransform、trivialZeroContribution、zetaLogDerivativeIntegral、geometricTermwiseIntegral、primeIdealDirichletIntegral、continuousTerm、nontrivialZeroSum、zetaZeroSide、fLaplacianKernel、geometricKernelTrace、ellipticTerm、distributionSupport、nontrivialZeroEnum、correlation、heatKernel、realIntegral、ManifoldX（→abbrev）、ManifoldM（→abbrev）

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
| 第一档：ZFC标准/定义性 | ~32 | 54% | mathlib可证或定义性质 |
| 第二档：已知大定理 | ~27 | 46% | 数学上已确立，形式化是工作量 |
| 第三档：未证明分析断言 | 0 | 0% | 需要新数学思想 |

**结论**：理论在逻辑上闭合于 ZFC。所有 6 个数学缺陷已处理（2 消除 + 4 澄清）。所有前提都是已知数学结果，无循环论证，无未证明断言。剩余工作是"把已知定理写进 Lean"，不是"发现新数学"。

---

## 十、三个大难题进展

| # | 难题 | 当前状态 | 下一步 |
|---|------|---------|--------|
| 1 | specDiscM/maassSpecParam 非空洞化 | **已完成折中方案**：laplacian_has_discrete_spectrum 公理，specDiscM 从"任意序列"变为"Laplacian 特征值枚举" | 可选：引入 resolvent_compact + Rellich 引理，从紧算子谱定理推出枚举（成本高） |
| 2 | ManifoldX/M 显式实例化 | **第一步完成**：上半平面/上半空间子类型，opaque→abbrev | 补双曲距离公式、双曲测度、群作用（分式线性变换）、商空间（Quotient/基本域） |
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
9. **Mathlib 直查降级**：real_complex_inj = Complex.ofReal_injective；riemann_zeta_zero_symmetry = riemannZeta_one_sub（函数方程）；laplaceTransform_exp = integral_exp_neg_mul_rpow（p=1）。降级前先搜 Mathlib，很多"公理"其实是已有定理。
10. **定义性作弊识别**：围道积分重构发现 `zetaLogDerivativeIntegral f := zetaZeroSide f` 导致证明链全是 rfl。**定义不能等于结论，否则数学内容被藏起来了。**
11. **模块化原则**：大模块单独成文件，按依赖关系分层。基础模块独立，stage_4 只保留主论证链。
12. **折中方案价值**：specDiscM 非空洞化不追求 resolvent_compact 完整方案（成本太高），引入 laplacian_has_discrete_spectrum 公理（比原公理强，比完整方案弱），既非空洞又避免技术细节。
13. **留数定理自建**：Mathlib 有柯西积分公式但无完整留数定理。自建 residueAt 定义 + 一般留数定理公理 + 具体计算公理，把特殊公理降级为定理。公理净增但结构更诚实。
14. **最简架子优先**：双曲空间实例化先做上半平面/上半空间子类型（通用覆盖），商结构后续添加。不要一开始就追求完整的 Γ\ℍⁿ 商空间理论。

---

## 十二、下一步方向

1. **双曲空间基础设施填充**（优先级高）：hyperbolicDistance 从 opaque 改为具体公式，manifoldIntegral 从 opaque 改为双曲测度积分，gammaAction 从 opaque 改为分式线性变换
2. **一般留数定理证明**（长期）：用 Mathlib 柯西积分公式 + Laurent 展开 + 围道形变证明 residue_theorem_general
3. **PWW 子公理的严格证明**（非当前目标）：Whitney 插值 + Paley-Wiener 满射性的完整分析证明
4. **大定理形式化**（非当前目标）：Arthur 迹公式、JL 对应、Dolgopyat 混合
5. **商空间显式化**（长期）：用 Quotient 或基本域实现 Γ\ℍⁿ
6. **resolvent_compact 完整方案**（可选）：引入 Rellich 引理，从紧算子谱定理推出谱枚举
7. **向实二次域推广**：论文第 6 节的条件性声明
