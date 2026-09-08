# Stage 4: RH 谱对偶论证框架 — 总结文档

> **版本**: v4.0 + 多轮公理分解 + 第6章显式积分核基础设施  
> **最后更新**: 2026-09-08  
> **文件**: stage_4.lean  
> **编译状态**: 通过（lake env lean）

---

## 一、项目概述

本文件是第三篇论文的 Lean 4 形式化，目标是条件导出黎曼猜想（RH）。

核心论证路径：
1. Arthur 稳定迹公式（A1）：几何侧 = 谱侧
2. Jacquet-Langlands 酉对应（A2）：三维谱 ↔ 二维 Maass 谱
3. Mollified Explicit Formula（A3）：迹等式 → 零点对应
4. 反证法：偏离临界线 → 矛盾 → RH

### 关键战略判断

- 不需要建立 ζ(s) ↔ Z_M(s) 函数恒等桥梁（那是死路）
- 论文路径通过迹等式 + 反证法推出 RH
- 但迹等式到 RH 的推导依赖未验证的分析公理（特别是 mollified_melin_separation）

---

## 二、文件统计

| 指标 | 数值 |
|------|------|
| 总行数 | 1767 |
| 公理 (axiom) | 60 |
| 定理 (theorem) | 55 |
| 不透明常量 (opaque) | 33 |
| 定义 (def/abbrev) | 25 |
| sorry | 0 |

---

## 三、章节结构

1. Section 1: 基础设置与谱参数
2. Section 2: Arthur 迹公式（A1）
3. Section 3: 保序双射与素理想
4. Section 3.5: Shimura 提升核基础设施（新增）
5. Section 4: JL 酉等价（A2）
6. Section 5: 自伴谱定理与 Dolgopyat 混合
7. Section 6: 显式积分核基础设施
8. Section 7: Mollified Explicit Formula（A3）
9. Section 8: RH 主定理

---

## 四、公理清单（60 条，按章节分组）

### 4.1 谱参数性质（6 条）
1. specDiscM_nonneg_axiom - specDiscM(n) >= 0
2. specDiscM_strict_mono_axiom - 严格递增
3. specDiscM_unbounded_axiom - 无界
4. maassSpecParam_nonneg_axiom - maassSpecParam(n) >= 0
5. maassSpecParam_strict_mono_axiom - 严格递增
6. maassSpecParam_unbounded_axiom - 无界

### 4.2 Arthur 迹公式（8 条）
7. operatorTrace_eq_geometricKernel - 算子迹 = 几何核迹
8. spectral_decomposition_additivity - 谱分解可加性
9. discrete_trace_computation - 离散迹计算
10. continuous_trace_computation - 连续迹计算
11. centralizer_isomorphic_R - 中心化子 ≅ R
12. homogeneous_measure_decomposition - 齐性测度分解
13. full_orbital_integral_expansion - 完整轨道积分展开
14. parabolic_term_vanishes - 抛物项消失

### 4.3 椭圆类（4 条）
15. elliptic_term_support - 椭圆项支撑
16. elliptic_class_lengths_bounded - 椭圆类长度有界
17. elliptic_class_lengths_discrete - 椭圆类长度离散
18. bounded_discrete_real_set_finite - 有界离散实数集有限

### 4.4 Shimura 提升与 JL（11 条）
19. maass_eigenvalue_equation - Δ_X φ_k = (1/4+t_k²)φ_k
20. threeManifold_eigenvalue_equation - Δ_M ψ_n = specDiscM(n)ψ_n
21. shimuraLift_eigenfunction_correspondence - U(φ_{φ(n)}) = ψ_n
22. shimuraLift_commutes_laplacian - U∘Δ_X = Δ_M∘U
23. shimuraLift_linear - U(a·f) = a·U(f)
24. eigenfunction_cancellation - a·ψ_n = b·ψ_n → a = b
25. l_parameter_standard_form - jlLParameterMap(n).re = 1/2
26. l_parameter_im_nonneg - 0 <= jlLParameterMap(n).im
27. real_complex_inj - (x:C)=(y:C) → x=y
28. shimuraLift_isometry - U 是部分等距
29. l_parameter_eigenvalue_formula - specDiscM(n) = 1/4+(jlLParameterMap(n).im)²

### 4.5 JL 加权迹（2 条）
30. jl_spectrum_rearrangement - 按纤维重排谱
31. jl_fiber_size_eq_weight - 纤维大小 = localJLWeight

### 4.6 Dolgopyat 混合（2 条）
32. correlation_transfer_operator_identity - 相关函数 = 转移算子
33. dolgopyat_spectral_gap_estimate - 转移算子谱间隙

### 4.7 MEF 分析核心（12 条）
34. mollified_continuous_spectrum_vanishes - 磨光后连续谱消失
35. geometric_sum_mellin_inversion - 几何和 Mellin 反演
36. termwise_integral_swap - Fubini 交换
37. euler_product_integral - Euler 乘积积分
38. log_derivative_integral_residues - 对数导数积分留数
39. mollified_spectral_delta - 磨光函数谱点插值
40. delta_trace_zero_correspondence - delta 迹等式 → 零点
41. zero_side_melin_localization - 零点侧 Mellin 局部化
42. mollified_melin_separation - 磨光 Mellin 分离
43. distribution_equality_support - 分布等式 → 支撑相等
44. spectral_side_support - 谱侧支撑
45. zero_side_support - 零点侧支撑

### 4.8 热核与积分核（15 条）
46. heatKernel_semigroup - 热核半群
47. heatKernel_commutes_laplacian - 热核与 Laplacian 交换（True 简化）
48. fLaplacianKernel_via_heatKernel - f(Δ) 核热核表示（True 简化）
49. manifoldIntegral_linear - 流形积分线性
50. gammaAction_identity - Γ 作用单位元
51. gammaAction_compat - Γ 作用相容性
52. geometricKernelTrace_integral_representation - 几何核迹积分表示（精确）
53. laplaceTransform_exp - Laplace 变换 e^{-st}
54. laplaceTransform_linear - Laplace 变换线性
55. trace_cyclicity - 迹循环性（True 简化）
56. hyperbolicDistance_gamma_invariant - 双曲距离 Γ 不变
57. heatKernel_explicit_formula - 三维双曲热核显式公式
58. heatKernel_symmetric - 热核对称
59. heatKernel_positive - 热核正定
60. fLaplacianKernel_heatKernel_exact - f(Δ) 核热核精确式（True 简化）

---

## 五、定理清单（55 条，按重要性分组）

### 5.1 RH 主定理（1 条）
- riemann_hypothesis - 所有非平凡零点在临界线上

### 5.2 RH 分析核心（8 条）
- all_zeros_on_critical_line - 所有非平凡零点在临界线上（反证法）
- off_critical_line_contradiction - 偏离临界线 → 矛盾
- pair_contribution_sigma_dependent - 配对贡献依赖 σ
- mollified_spectral_preserving_perturbation - 谱点保持的扰动
- spectral_zero_equality - 谱和 = 零点侧
- zero_to_maass_param - 逆向显式公式
- maass_param_to_zero - 正向显式公式
- spectral_zero_support_match - 谱零点支撑匹配

### 5.3 Arthur 迹公式（8 条）
- arthur_trace_formula - Arthur 迹公式（A1，已降级）
- atf_spectral_decomposition - 谱分解
- atf_geometric_expansion - 几何展开
- atf_geometric_expansion_core - 几何展开核心
- raw_orbital_integral_explicit - 轨道积分显式公式
- hyperbolic_orbital_integral_simplification - 双曲轨道积分化简
- hyperbolic_orbital_sum_eq_geometric - 双曲轨道和 = 几何和
- elliptic_classes_finite - 椭圆类有限（已降级）

### 5.4 JL 对应（5 条）
- jl_l_parameter_preserving - L-参数保持（最新降级，从 Shimura 提升证明）
- jl_spectrum_preserving - 谱保持
- jl_weighted_trace_identity - 加权迹恒等式
- jl_unitary_equivalence - JL 酉等价（A2，已降级）
- three_manifold_eigenvalue_lower_bound - 三维谱 >= 1/4（意外收获）

### 5.5 MEF 与显式公式（7 条）
- mollified_trace_equality - 磨光迹等式
- mollified_trace_explicit_formula - 磨光迹显式公式（MEF，A3 已降级）
- weil_explicit_formula - Weil 显式公式
- geometric_sum_log_derivative - 几何和对数导数
- perron_formula_geometric - Perron 公式
- forward_support_match - 正向支撑匹配
- zero_im_matches_maass_param - 零点虚部 = Maass 参数

### 5.6 谱性质与混合（8 条）
- specDiscM_properties - specDiscM 性质束
- maassSpecParam_properties - maassSpecParam 性质束
- self_adjoint_eigenvalue_real - 自伴算子特征值实
- maass_eigenvalue_lower_bound - Maass 特征值 >= 1/4
- three_manifold_eigenvalue_positive - 三维特征值正
- dolgopyat_exponential_mixing - Dolgopyat 指数混合（已降级）
- dolgopyat_geometric_backstop - 几何兜底
- continuous_spectrum_trivial_zeros_only - 连续谱只有平凡零点

### 5.7 其他（18 条）
- orbitWeight_eq_norm_form, orbitWeight_simplification
- geometricSum_via_prime_ideals, split_prime_compensation
- elliptic_term_locality, continuous_term_trivial_zeros
- mollified_elliptic_zero, spectral_sum_determined_by_points
- nontrivial_zero_has_maass_param, zero_correspondence
- trivial_zeros_negative_even, generalization_to_real_quadratic_fields
- 以及 6 条谱参数性质的推论定理

---

## 六、Opaque 清单（33 条）

### 6.1 Arthur 迹公式相关（8 条）
ellipticTerm, continuousTerm, operatorTrace, fLaplacianKernel, geometricKernelTrace, discreteSpectralTrace, continuousSpectralTrace, parabolicTerm

### 6.2 轨道积分相关（3 条）
rawOrbitalIntegral, centralizerIntegral, ellipticClassLengths

### 6.3 Shimura 提升与 JL（9 条）
innerProduct, integralOperator, shimuraKernel, jlSpectrumMap, jlLParameterMap, laplacian_X, laplacian_M, maassEigenfunction, threeManifoldEigenfunction

### 6.4 Dolgopyat 混合（2 条）
correlation, transferOperator

### 6.5 MEF 分析（6 条）
zetaZeroSide, zetaLogDerivativeIntegral, primeIdealDirichletIntegral, geometricTermwiseIntegral, melinTransform, distributionSupport

### 6.6 热核与积分核（5 条）
heatKernel, manifoldIntegral, gammaAction, laplaceTransform, hyperbolicDistance

---

## 七、RH 主定理完整证明链

```
riemann_hypothesis
  └─ all_zeros_on_critical_line (定理)
       └─ off_critical_line_contradiction (定理)
            └─ pair_contribution_sigma_dependent (定理)
                 ├─ spectral_sum_determined_by_points (定理)
                 └─ mollified_spectral_preserving_perturbation (定理)
                      ├─ zero_side_melin_localization (公理 41)
                      └─ mollified_melin_separation (公理 42) ⚠️

spectral_zero_equality (定理)
  └─ mollified_trace_equality (定理)
       ├─ arthur_trace_formula (定理)
       ├─ mollified_continuous_spectrum_vanishes (公理 34) ⚠️
       └─ weil_explicit_formula (定理)
            ├─ geometric_sum_log_derivative (定理)
            │    ├─ perron_formula_geometric (定理)
            │    │    ├─ geometric_sum_mellin_inversion (公理 35)
            │    │    └─ termwise_integral_swap (公理 36)
            │    └─ euler_product_integral (公理 37)
            └─ log_derivative_integral_residues (公理 38)
```

---

## 八、已降级为定理的原核心公理（26 条）

| 原公理 | 降级为 |
|--------|--------|
| A1 Arthur 迹公式 | arthur_trace_formula |
| ATF-Spec | atf_spectral_decomposition |
| ATF-Geo | atf_geometric_expansion |
| A2 JL 酉等价 | jl_unitary_equivalence |
| A3 MEF | mollified_trace_explicit_formula |
| zero_to_maass_param | 定理 |
| maass_param_to_zero | 定理 |
| spectral_zero_support_match | 定理 |
| off_critical_line_contradiction | 定理 |
| pair_contribution_sigma_dependent | 定理 |
| mollified_spectral_preserving_perturbation | 定理 |
| weil_explicit_formula | 定理 |
| geometric_sum_log_derivative | 定理 |
| perron_formula_geometric | 定理 |
| zero_im_matches_maass_param | 定理 |
| raw_orbital_integral_explicit | 定理 |
| specDiscM_properties | 定理 |
| maassSpecParam_properties | 定理 |
| atf_geometric_expansion_core | 定理 |
| jl_spectrum_preserving | 定理 |
| **jl_l_parameter_preserving** | **定理（最新，从 Shimura 提升证明）** |
| jl_weighted_trace_identity | 定理 |
| forward_support_match | 定理 |
| elliptic_classes_finite | 定理 |
| dolgopyat_exponential_mixing | 定理 |
| continuous_term_trivial_zeros | 定理 |

---

## 九、仍为 True 简化的公理（4 条）

1. heatKernel_commutes_laplacian - 可升级为 H_t∘Δ = Δ∘H_t
2. fLaplacianKernel_via_heatKernel - 可升级为 K_f = ∫ f̂(t)K_t dt
3. trace_cyclicity - 可升级为 Tr(AB)=Tr(BA)
4. fLaplacianKernel_heatKernel_exact - 可升级为精确表达式

---

## 十、RH 分析核心公理的诚实评估

### ⚠️ 需要警惕的公理

1. **mollified_continuous_spectrum_vanishes**（公理 34）
   - 论文只说连续谱与非平凡零点位置无关，没说为零
   - 当前形式过度强化

2. **mollified_melin_separation**（公理 42）
   - 论文中完全没有这个概念
   - 这是我们的理论框架中引入的分析工具
   - 需要严格验证是否成立

3. **mollified_spectral_delta**（公理 39）
   - 论文中只是定义而非证明
   - 磨光函数的谱点插值能力需要分析证明

### logic.pdf 的核心观点

把 Arthur/JL 黑箱换成显式积分表达式，不改变论证链条，只是把存在性断言替换为分析断言。这使得每个公理都可以通过分析手段独立验证。

---

## 十一、下一步计划

### 优先级 1：更新与验证
- [ ] 升级 4 条 True 简化公理为精确等式
- [ ] 验证 mollified_melin_separation 是否真的成立
- [ ] 弱化 mollified_continuous_spectrum_vanishes 为论文原始表述

### 优先级 2：继续拆公理
- [ ] 拆 spectral_decomposition_additivity
- [ ] 拆 discrete_trace_computation
- [ ] 拆 full_orbital_integral_expansion

### 优先级 3：积分核深化
- [ ] 用热核显式公式证明 heatKernel_semigroup
- [ ] 用 Shimura 核显式公式证明 shimuraLift_commutes_laplacian
- [ ] 建立 fLaplacianKernel 的 Laplace 变换精确表达式

---

## 十二、编译命令

```powershell
cd C:\proj2
$env:PATH = "C:\ltin;$env:PATH"
C:\ltin\lake.exe env lean OrderPreservingBijection/stage_4.lean
```

**注意**: 不能用 `lake build`（会触发 mathlib .ltar 权限错误），必须用 `lake env lean` 单独编译。

---

*文档生成时间: 2026-09-08*  
*对应文件: stage_4.lean (1767 行, 60 公理, 55 定理, 33 opaque, 0 sorry)*
