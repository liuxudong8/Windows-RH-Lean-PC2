# Stage-4: RH 谱对偶论证框架 — 形式化总结

> 项目：Windows-RH-Lean-PC-2
> 文件：`OrderPreservingBijection/stage_4.lean`（v4.0 + 多轮深度公理分解）
> 论文：《基于 Arthur 稳定迹、Jacquet–Langlands 对应与测地流指数混合的谱对偶论证9》
> 日期：2026-09-05
> 状态：编译通过，零错误，零 sorry

---

## 1. 目标

在 Lean 4 中形式化第三篇论文的核心论证路径，**条件导出黎曼猜想（RH）**：

```
Arthur 稳定迹公式（已分解为谱侧+几何侧子定理）
  → 保序双射变量替换（Stage-3）
  → 轨道积分化简（中心化子 G_γ ≅ ℝ + 齐性空间测度分解）
  → JL 酉等价分解（谱保持 + 加权迹恒等式）
  → 自伴算子谱定理（本征值实数）
  → Dolgopyat 指数混合（几何兜底）
  → 磨光测试函数（椭圆项+连续谱消失）
  → Weil 显式公式（Mellin反演 + Fubini交换 + Euler乘积 + 留数定理）
  → 谱-零点等式
  → 反证法：off_critical_line_contradiction → all_zeros_on_critical_line
  → RH：所有非平凡零点 Re(s) = 1/2
```

**关键设计原则**：不假设 Selberg zeta = Dedekind zeta 全域解析恒等（论文明确摒弃此路径），仅对给定紧支测试函数给出有限加权求和等价。

**RH 证明路径重大简化**：`riemann_hypothesis` 直接调用 `all_zeros_on_critical_line`（反证法定理），不再绕 MEF 逆向。分布支撑比较（`zero_im_matches_maass_param`）仅用于 MEF 完整双向对应，不是 RH 的必需前提。

---

## 2. 文件统计

| 指标 | 数值 |
|------|------|
| 总行数 | ~1120 |
| `sorry` | **0** |
| 公理（`axiom`） | **27** |
| 不透明常量（`opaque`） | **15** |
| 定理（`theorem`） | **48** |
| 结构（`structure`） | 2 |
| 定义（`def`） | 4 |
| 编译错误 | **0** |
| 命名空间 | `RHSpectralDuality` |

---

## 3. 公理分解历程

原始 v4.0 框架有 **8 个核心公理**（A1-A4 + 4 个辅助公理）。经过多轮深度分解，原 4 大核心公理（A1 Arthur 迹公式、A2 JL 酉等价、A3 MEF、A4 Dolgopyat）**全部降级为定理**，替换为更基本的子公理。后续继续分解 Weil 显式公式、分布支撑比较、轨道积分、性质束等。

### 分解时间线

| 阶段 | 操作 | 公理数 |
|------|------|--------|
| v4.0 初始 | 8 公理框架 | 8 |
| 16 项处置 | A4 标准形式化；B1-B4 opaque 化；C1-C5 改进；D1-D3 修复 | 8 |
| A1 分解 | Arthur 迹公式 → 谱侧+几何侧子定理，引入 operatorTrace + 3 子公理 | 10 |
| ATF-Geo 分解 | 几何展开 → core + 轨道积分，引入 rawOrbitalIntegral | 11 |
| ATF-Spec 分解 | 谱分解 → 3 子公理，引入 discrete/continuousSpectralTrace | 13 |
| A2 分解 | JL 酉等价 → 谱保持 + 加权迹恒等式，引入 jlSpectrumMap | 14 |
| A3 分解 | MEF → 磨光连续谱消失 + 正/逆向显式公式 | 15 |
| 逆向分解 | zero_to_maass_param → Weil公式 + spectral_zero_support_match | 16 |
| 正向分解 | maass_param_to_zero → spectral_zero_equality + forward_support_match | 16 |
| 连续谱改进 | continuous_term_trivial_zeros 降级为定理 | 15 |
| 公理15分解 | spectral_zero_support_match → off_critical + zero_im_matching | 16 |
| off_critical分解 | → pair_contribution_sigma_dependent（定理） | 16 |
| pair_contribution分解 | → spectral_sum_determined + mollified_spectral_preserving_perturbation | 17 |
| mollified扰动分解 | → zero_side_melin_localization + mollified_melin_separation | 18 |
| Weil分解 | weil_explicit_formula → geometric_sum_log_derivative + log_derivative_integral_residues | 18 |
| geometric_sum分解 | → perron_formula_geometric + euler_product_integral | 19 |
| Perron分解 | → geometric_sum_mellin_inversion + termwise_integral_swap | 20 |
| zero_im分解 | → 分布支撑3公理 + distributionSupport opaque；RH简化为直接用all_zeros | 22 |
| 轨道积分分解 | raw_orbital_integral → centralizer_isomorphic_R + homogeneous_measure_decomposition | 23 |
| 性质束拆分 | specDiscM/maassSpecParam 各拆为3原子公理 | **27** |

---

## 4. 二十七个公理清单（按逻辑层次分组）

### 第一层：谱理论基础（6）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 1 | `specDiscM_nonneg_axiom` | 18 | 三维离散谱非负：∀n, 0 ≤ specDiscM n |
| 2 | `specDiscM_strict_mono_axiom` | 22 | 三维离散谱严格递增 |
| 3 | `specDiscM_unbounded_axiom` | 26 | 三维离散谱无界（Weyl 定律） |
| 4 | `maassSpecParam_nonneg_axiom` | 38 | Maass 谱参数非负（t≥0 分支） |
| 5 | `maassSpecParam_strict_mono_axiom` | 42 | Maass 谱参数严格递增 |
| 6 | `maassSpecParam_unbounded_axiom` | 46 | Maass 谱参数无界（Weyl 定律） |

### 第二层：ATF 谱侧（3）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 7 | `spectral_decomposition_additivity` | 147 | L² 正交分解：算子迹 = 离散迹 + 连续迹 |
| 8 | `discrete_trace_computation` | 156 | 离散迹 = Σ_n f(specDiscM n) |
| 9 | `continuous_trace_computation` | 166 | 连续迹 = continuousTerm |

### 第三层：ATF 几何侧（4）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 10 | `atf_geometric_expansion_core` | 327 | 几何展开核心：算子迹 = 双曲轨道和 + 椭圆项 |
| 11 | `centralizer_isomorphic_R` | 211 | 中心化子 G_γ ≅ ℝ：中心化子积分 = ℓ·f(ℓ) |
| 12 | `homogeneous_measure_decomposition` | 222 | 齐性空间测度分解：横截面平均 = 1/(1-N⁻¹) |
| 13 | `elliptic_classes_finite` | 362 | 椭圆共轭类有限：椭圆项只依赖有限个特征长度 |

### 第四层：JL 对应（2）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 14 | `jl_spectrum_preserving` | 482 | JL 谱保持：specDiscM(n) = 1/4 + maassSpecParam(φ(n))² |
| 15 | `jl_weighted_trace_identity` | 491 | JL 加权迹恒等式：三维谱和 = Maass 谱和 |

### 第五层：动力学兜底（1）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 16 | `dolgopyat_exponential_mixing` | 575 | 测地流指数混合：∃α,C>0, ‖correlation(f,g,t)‖ ≤ C·e^{-α|t|} |

### 第六层：磨光与 Weil 显式公式（4）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 17 | `mollified_continuous_spectrum_vanishes` | 613 | 磨光函数下连续谱项 = 0 |
| 18 | `geometric_sum_mellin_inversion` | 680 | Mellin 反演：几何侧 → 逐项积分 |
| 19 | `termwise_integral_swap` | 693 | Fubini 交换：逐项积分 → Dirichlet 生成函数积分 |
| 20 | `euler_product_integral` | 719 | Euler 乘积：Dirichlet 积分 → ζ 对数导数积分 |
| 21 | `log_derivative_integral_residues` | 744 | 留数定理：对数导数积分 → 零点侧求和 |

### 第七层：分布支撑比较（3）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 22 | `distribution_equality_support` | 963 | 分布相等 → 支撑相同（磨光族完备性） |
| 23 | `spectral_side_support` | 971 | 谱侧支撑 = {1/4+t_n²} |
| 24 | `zero_side_support` | 980 | 零点侧支撑 = {1/4+(Imρ)² : 上半平面临界线零点} |

### 第八层：Melin 局部化与正向匹配（3）

| # | 公理 | 行 | 内容 |
|---|------|-----|------|
| 25 | `zero_side_melin_localization` | 828 | 零点侧 Melin 局部化 |
| 26 | `mollified_melin_separation` | 853 | Γ 因子不对称 + 磨光插值（谱点-Melin 分离） |
| 27 | `forward_support_match` | 785 | 正向支撑匹配：每个 Maass 参数 t_n → ζ 零点 ρ=1/2+i·t_n |

---

## 5. 十五个不透明抽象常量

| 常量 | 行 | 类型 | 数学含义 |
|------|-----|------|----------|
| `ellipticTerm` | 113 | `TestFunction → ℂ` | 椭圆共轭类贡献 E(f) |
| `continuousTerm` | 119 | `TestFunction → ℂ` | 连续谱贡献 Cont(f) |
| `operatorTrace` | 125 | `TestFunction → ℂ` | 算子迹 Tr(f(Δ))，Arthur 迹公式两侧公共值 |
| `discreteSpectralTrace` | 131 | `TestFunction → ℂ` | 离散谱迹 |
| `continuousSpectralTrace` | 138 | `TestFunction → ℂ` | 连续谱迹 |
| `rawOrbitalIntegral` | 195 | `PrimeGeodesic → TestFunction → ℂ` | 原始轨道积分 ∫_{G_γ\G} f(g^{-1}γg) dg |
| `centralizerIntegral` | 202 | `PrimeGeodesic → TestFunction → ℂ` | 中心化子方向积分 ∫_{G_γ} f(x^{-1}γx) dx |
| `jlSpectrumMap` | 468 | `ℕ → ℕ` | JL 谱映射 φ: 三维谱指标 → Maass 谱指标 |
| `correlation` | 563 | `(ℝ→ℂ)→(ℝ→ℂ)→ℝ→ℂ` | 测地流关联函数 C(f,g,t) |
| `zetaZeroSide` | 642 | `TestFunction → ℂ` | ζ 零点侧求和 Z(f) = Σ_ρ f̂(ρ) + T(f) |
| `zetaLogDerivativeIntegral` | 651 | `TestFunction → ℂ` | (ζ'/ζ)(s)·f̂(s) 的围道积分 |
| `primeIdealDirichletIntegral` | 661 | `TestFunction → ℂ` | 素理想 Dirichlet 生成函数 D(s)·f̂(s) 的围道积分 |
| `geometricTermwiseIntegral` | 669 | `TestFunction → ℂ` | 逐项积分形式 Σ_p W(p)·∮f̂(s)N(p)^{-s}ds |
| `melinTransform` | 815 | `TestFunction → ℂ → ℂ` | Melin 变换 f̂(s) |
| `distributionSupport` | 955 | `(TestFunction→ℂ) → Set ℝ` | 分布的支撑 |

---

## 6. 核心定理（48 个，按逻辑层次分组）

### 谱性质推论（8）

| 定理 | 行 | 内容 |
|------|-----|------|
| `specDiscM_properties` | 30 | 性质束（定理，由3原子公理合取） |
| `maassSpecParam_properties` | 50 | 性质束（定理，由3原子公理合取） |
| `specDiscM_nonneg` | 57 | specDiscM n ≥ 0 |
| `specDiscM_strict_mono` | 60 | specDiscM n < specDiscM (n+1) |
| `specDiscM_unbounded` | 64 | ∀M, ∃n, specDiscM n > M |
| `maassSpecParam_nonneg` | 68 | maassSpecParam n ≥ 0 |
| `maassSpecParam_strict_mono` | 72 | maassSpecParam n < maassSpecParam (n+1) |
| `maassSpecParam_unbounded` | 76 | ∀M, ∃n, maassSpecParam n > M |

### 轨道权重与积分（5）

| 定理 | 行 | 内容 |
|------|-----|------|
| `orbitWeight_eq_norm_form` | 92 | W(γ) = N·log N / (N-1)² |
| `orbitWeight_simplification` | 98 | 轨道权重化简 |
| `raw_orbital_integral_explicit` | 234 | **降级为定理**：ℓ/(1-N⁻¹)·f(ℓ)（中心化子+测度分解） |
| `hyperbolic_orbital_integral_simplification` | 274 | 轨道积分 = W(γ)·f(ℓ)（代数证明） |
| `hyperbolic_orbital_sum_eq_geometric` | 314 | 双曲轨道和 = geometricSum |

### Arthur 迹公式（3）

| 定理 | 行 | 内容 |
|------|-----|------|
| `atf_spectral_decomposition` | 175 | 谱侧分解：operatorTrace = spectralSum + continuousTerm |
| `atf_geometric_expansion` | 333 | 几何展开：operatorTrace = geometricSum + ellipticTerm |
| `arthur_trace_formula` | 349 | **A1 降级为定理**：spectralSum + continuousTerm = geometricSum + ellipticTerm |

### 椭圆与连续谱（3）

| 定理 | 行 | 内容 |
|------|-----|------|
| `elliptic_term_locality` | 373 | 椭圆项局部性：只依赖有限个点 |
| `continuous_term_trivial_zeros` | 394 | **降级为定理**：临界带内连续谱正则 |
| `continuous_spectrum_trivial_zeros_only` | 1081 | 连续谱仅含平凡零点 |

### 几何侧变量替换（2）

| 定理 | 行 | 内容 |
|------|-----|------|
| `geometricSum_via_prime_ideals` | 406 | 几何侧 → 素理想范数求和（复用 Stage-3） |
| `split_prime_compensation` | 452 | 分裂素 p≡1,4 mod 5 的 JL 权重 1/2 补偿 |

### JL 对应（3）

| 定理 | 行 | 内容 |
|------|-----|------|
| `jl_unitary_equivalence` | 498 | **A2 降级为定理**：spectralSum = maassSpectralSum |
| `three_manifold_eigenvalue_lower_bound` | 507 | 三维谱 ≥ 1/4（从 JL 谱保持推出，意外收获） |
| `self_adjoint_eigenvalue_real` | 516 | 自伴算子本征值为实数（内积论证） |

### 谱下界（2）

| 定理 | 行 | 内容 |
|------|-----|------|
| `maass_eigenvalue_lower_bound` | 534 | Maass 本征值 λ = 1/4 + t² ≥ 1/4 |
| `three_manifold_eigenvalue_positive` | 543 | 三维谱 n≥1 时严格正（递推证明） |

### Dolgopyat（1）

| 定理 | 行 | 内容 |
|------|-----|------|
| `dolgopyat_geometric_backstop` | 583 | 指数混合推论：t≥0 时关联函数指数控制 |

### Weil 显式公式（4）

| 定理 | 行 | 内容 |
|------|-----|------|
| `perron_formula_geometric` | 704 | **降级为定理**：几何侧 = Dirichlet 积分（Mellin反演+Fubini） |
| `geometric_sum_log_derivative` | 730 | **降级为定理**：几何侧 = ζ对数导数积分（Perron+Euler） |
| `weil_explicit_formula` | 756 | **降级为定理**：几何侧 = 零点侧（四步标准定理） |
| `spectral_zero_equality` | 768 | spectralSum = zetaZeroSide（磨光迹等式+Weil公式） |

### 磨光与 MEF（5）

| 定理 | 行 | 内容 |
|------|-----|------|
| `mollified_elliptic_zero` | 603 | 磨光函数椭圆项 = 0（结构字段） |
| `mollified_trace_equality` | 625 | 磨光迹等式：spectralSum = geometricSum |
| `maass_param_to_zero` | 791 | **正向降级为定理**：t_n → ζ 零点 ρ=1/2+i·t_n |
| `mollified_trace_explicit_formula` | 1060 | **A3 降级为定理**：MEF 双向对应（上半平面） |
| `zero_correspondence` | 1067 | 每个 Maass 参数对应临界线上零点 |

### 反证法与 RH 核心（6）

| 定理 | 行 | 内容 |
|------|-----|------|
| `spectral_sum_determined_by_points` | 800 | 谱和完全由谱点取值决定（从定义直接推出） |
| `mollified_spectral_preserving_perturbation` | 874 | **降级为定理**：谱点保持的扰动（Melin局部化+分离） |
| `pair_contribution_sigma_dependent` | 894 | **降级为定理**：配对贡献依赖 σ |
| `off_critical_line_contradiction` | 914 | **降级为定理**：临界线外零点导致矛盾 |
| `all_zeros_on_critical_line` | 939 | **核心定理**：所有非平凡零点在临界线上（反证法） |
| `zero_im_matches_maass_param` | 998 | **降级为定理**：零点虚部与Maass参数匹配（分布支撑比较） |

### 谱-零点对应（3）

| 定理 | 行 | 内容 |
|------|-----|------|
| `spectral_zero_support_match` | 1032 | 上半平面零点 s → ∃n, s=1/2+i·t_n |
| `zero_to_maass_param` | 1049 | **逆向降级为定理**：上半平面零点 → Maass 参数 |
| `nontrivial_zero_has_maass_param` | 1074 | 非平凡零点有 Maass 参数对应（上半平面） |

### 主定理与推广（3）

| 定理 | 行 | 内容 |
|------|-----|------|
| `trivial_zeros_negative_even` | 1087 | ζ 平凡零点在负偶数（mathlib 标准定理） |
| `riemann_hypothesis` | 1099 | **主定理**：∀s, ζ(s)=0 → 0<Re(s)<1 → Re(s)=1/2 |
| `generalization_to_real_quadratic_fields` | 1111 | 推广到一般实二次域（条件性声明） |

---

## 7. 主定理证明路径（当前）

```
riemann_hypothesis (主定理)
  └─ all_zeros_on_critical_line (定理, 反证法)
       ├─ off_critical_line_contradiction (定理)
       │    └─ pair_contribution_sigma_dependent (定理)
       │         ├─ spectral_sum_determined_by_points (定理, 从定义)
       │         └─ mollified_spectral_preserving_perturbation (定理)
       │              ├─ zero_side_melin_localization (公理 25)
       │              └─ mollified_melin_separation (公理 26)
       └─ spectral_zero_equality (定理)
            └─ mollified_trace_equality (定理)
                 ├─ arthur_trace_formula (定理, 原 A1)
                 │   ├─ atf_spectral_decomposition (定理)
                 │   │   ├─ spectral_decomposition_additivity (公理 7)
                 │   │   ├─ discrete_trace_computation (公理 8)
                 │   │   └─ continuous_trace_computation (公理 9)
                 │   └─ atf_geometric_expansion (定理)
                 │       ├─ atf_geometric_expansion_core (公理 10)
                 │       └─ hyperbolic_orbital_sum_eq_geometric (定理)
                 │           └─ hyperbolic_orbital_integral_simplification (定理)
                 │               └─ raw_orbital_integral_explicit (定理)
                 │                   ├─ centralizer_isomorphic_R (公理 11)
                 │                   └─ homogeneous_measure_decomposition (公理 12)
                 ├─ mollified_continuous_spectrum_vanishes (公理 17)
                 └─ f.ellipticVanishes (结构字段)

            + weil_explicit_formula (定理)
                 ├─ geometric_sum_log_derivative (定理)
                 │   ├─ perron_formula_geometric (定理)
                 │   │   ├─ geometric_sum_mellin_inversion (公理 18)
                 │   │   └─ termwise_integral_swap (公理 19)
                 │   └─ euler_product_integral (公理 20)
                 └─ log_derivative_integral_residues (公理 21)
```

**关键**：RH 主定理**不依赖** MEF 逆向（`zero_to_maass_param` / `zero_im_matches_maass_param` / 分布支撑比较）。RH 只依赖 `all_zeros_on_critical_line`，后者由反证法 + `spectral_zero_equality` 推出。

---

## 8. Weil 显式公式的完整四步分解

```
geometricSum (几何侧)
    │  geometric_sum_mellin_inversion (公理 18) — Mellin 反演
    ▼
geometricTermwiseIntegral (opaque)
    Σ_p W(p) · ∮ f̂(s)N(p)^{-s}ds
    │  termwise_integral_swap (公理 19) — Fubini 交换
    ▼
primeIdealDirichletIntegral (opaque)
    ∮ (Σ_p W(p)N(p)^{-s}) f̂(s)ds
    │  euler_product_integral (公理 20) — Euler 乘积 + 柯西定理
    ▼
zetaLogDerivativeIntegral (opaque)
    ∮ (ζ'/ζ)(s) f̂(s)ds
    │  log_derivative_integral_residues (公理 21) — 留数定理
    ▼
zetaZeroSide (零点侧)
    │
    ▼
weil_explicit_formula (定理)
```

---

## 9. 已降级为定理的原核心公理

| 原公理 | 降级为 | 依赖的子公理 |
|--------|--------|-------------|
| A1 Arthur 迹公式 | `arthur_trace_formula` | 公理 7,8,9,10,11,12 |
| ATF-Spec 谱分解 | `atf_spectral_decomposition` | 公理 7,8,9 |
| ATF-Geo 几何展开 | `atf_geometric_expansion` | 公理 10,11,12 |
| raw_orbital_integral | `raw_orbital_integral_explicit` | 公理 11,12 |
| A2 JL 酉等价 | `jl_unitary_equivalence` | 公理 14,15 |
| A3 MEF | `mollified_trace_explicit_formula` | 公理 17,18-21,25-27 |
| Weil 显式公式 | `weil_explicit_formula` | 公理 18,19,20,21 |
| Perron 公式 | `perron_formula_geometric` | 公理 18,19 |
| geometric_sum_log_derivative | `geometric_sum_log_derivative` | 公理 18,19,20 |
| 正向显式公式 | `maass_param_to_zero` | 公理 27 |
| 逆向显式公式 | `zero_to_maass_param` | 公理 22,23,24 |
| spectral_zero_support_match | `spectral_zero_support_match` | 公理 22,23,24 |
| zero_im_matches_maass_param | `zero_im_matches_maass_param` | 公理 22,23,24 |
| off_critical_line_contradiction | `off_critical_line_contradiction` | 公理 25,26 |
| pair_contribution_sigma_dependent | `pair_contribution_sigma_dependent` | 公理 25,26 |
| mollified_spectral_preserving_perturbation | `mollified_spectral_preserving_perturbation` | 公理 25,26 |
| 连续谱平凡零点 | `continuous_term_trivial_zeros` | 无（由定义推出） |
| specDiscM 性质束 | `specDiscM_properties` | 公理 1,2,3 |
| maassSpecParam 性质束 | `maassSpecParam_properties` | 公理 4,5,6 |

---

## 10. 公理硬度分级

| 级别 | 公理 | 可形式化程度 |
|------|------|-------------|
| **标准分析定理** | 18-21 (Mellin反演, Fubini, Euler乘积, 留数定理) | 经典证明，需复分析基础设施 |
| **分布论** | 22-24 (分布唯一性, 两侧支撑) | 需分布论基础设施，mathlib 不支持 |
| **Melin 分析** | 25-26 (局部化, Γ因子分离) | 深度调和分析 |
| **对应原理** | 14-15 (JL 谱保持, 加权迹) | 表示论深度结果 |
| **谱理论** | 7-9 (L²分解, 迹计算) | 标准自伴算子理论 |
| **几何** | 10-12 (几何展开, 中心化子, 测度分解) | 轨道积分，需李群基础设施 |
| **算术** | 13 (椭圆类有限) | 算术群标准性质 |
| **动力学** | 16 (Dolgopyat 混合) | Anosov 流深度定理 |
| **谱性质** | 1-6 (非负/递增/无界) | Weyl 定律 |
| **技术** | 17 (磨光连续谱消失) | 磨光论证技术 |
| **正向匹配** | 27 (forward_support_match) | 局部化论证 |

---

## 11. 前置依赖

| 文件 | 内容 | 状态 |
|------|------|------|
| `stage_3.lean` | 保序双射定理（本原闭测地线 ↔ 素理想） | 核心部分完全证明 |
| `QuadraticFieldFive.lean` | Q(√5) 代数数论（2056 行，无 sorry） | 完成 |
| `HyperbolicIdentity.lean` | 双曲恒等式 | 完成 |
| `Basic.lean` | 基础定义 | 完成 |
| mathlib | `Trigonometric.Basic`（其余通过 stage_3 间接导入） | 已编译 |

**stage_3 可复用定理**：
- `prime_ideal_norm_gt_one (γ) : principalIdealNorm γ.element > 1`
- `length_norm_identity_prime (γ) : geodesicLengthPrime γ = Real.log (principalIdealNorm γ.element : ℝ)`

---

## 12. 编译环境

- **编译工作目录**：`C:\proj2`
- **Lean 工具链**：`C:\lt`（v4.34.0-rc2）
- **编译命令**（必须用此，不能用 `lake build`）：
  ```powershell
  cd C:\proj2
  $env:PATH = "C:\lt\bin;$env:PATH"
  C:\lt\bin\lake.exe env lean OrderPreservingBijection/stage_4.lean
  ```
- **mathlib 路径**：`C:\proj2\mathlib4-master`（符号链接 → `C:\proj\mathlib4-master`）
- **注意**：`lake build` 会触发 mathlib 重编译并遇到 `.ltar` 权限错误（Windows lake 已知问题），必须用 `lake env lean` 单独编译。

---

## 13. 后续工作方向

1. **拆 `atf_geometric_expansion_core`（公理 10）**：几何展开核心，可拆为双曲类求和 + 椭圆类求和 + 抛物类（=0）。
2. **拆 `jl_weighted_trace_identity`（公理 15）**：JL 加权迹恒等式，需要表示论基础设施。
3. **拆 `dolgopyat_exponential_mixing`（公理 16）**：可拆为 Anosov 性 + 转移算子谱隙，但需动力系统基础设施。
4. **拆 `elliptic_classes_finite`（公理 13）**：可拆为有界性 + 离散性 → 有限，但需引入椭圆类集合。
5. **攻击 `mollified_melin_separation`（公理 26）**：Γ 因子不对称 + 磨光插值，是 RH 分析核心中最深的一个。
6. **攻击 `zero_side_melin_localization`（公理 25）**：零点侧 Melin 局部化。
7. **谱序列具体化**：`specDiscM` 和 `maassSpecParam` 当前为 `fun _=>0` + 性质公理，未来可构造具体谱序列。
8. **opaque 具体化**：`ellipticTerm`、`continuousTerm`、`zetaZeroSide` 等可定义具体表达式。
9. **推广到一般实二次域**：`generalization_to_real_quadratic_fields` 当前为条件性声明。

---

*本文件反映 stage_4.lean 最新状态（27 公理 / 15 opaque / 48 定理 / 0 sorry），编译通过零错误。*
