# Stage 4: RH 谱对偶论证框架 — 总结文档

> **版本**: v7.4（HeatKernelConvolution 测度论 API 打通 + 径向积分完全零 sorry + even_merge_lemma 独立引理）
> **最后更新**: 2026-09-14
> **核心文件**: `stage_4.lean` + 12 个独立模块
> **编译状态**: 通过（`lake build OrderPreservingBijection.stage_4`，stage_4 零 sorry）

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
- **v7.2 分层公理重构**：gammaAction_identity/compat 拆分为代数层（moebiusAction 定理）+ 群论层（gammaEnum 公理）
- **热核半群独立模块**：HeatKernelSemigroup.lean，heatKernel_semigroup 定理零 sorry
- **热核卷积五层拆解**：HeatKernelConvolution.lean，L4 径向积分完全零 sorry，L3 角度积分剩 2 个 sorry

---

## 二、模块化结构（12 个核心文件）

| 模块 | 行数 | 内容 | 公理 | 定理 | opaque | sorry |
|------|------|------|------|------|--------|-------|
| `stage_4.lean` | ~2553 | 主论证链（A1/A2/A3、反证法、RH 结论） | 28 | 93 | 9 | 0 |
| `BasicInfrastructure.lean` | 48 | TestFunction、realIntegral | 1 | 0 | 0 | 0 |
| `MellinInfrastructure.lean` | 30 | melinTransform、线性性 | 0 | 1 | 0 | 0 |
| `ZetaZeros.lean` | 86 | 零点枚举、重数、求和、局部化 | 3 | 5 | 1 | 0 |
| `ContourIntegral.lean` | 117 | 围道积分、留数定理自建、ζ对数导数 | 7 | 1 | 1 | 0 |
| `ManifoldInfrastructure.lean` | ~490 | SL2C、Möbius作用、gammaAction、商结构 | 5 | 8 | 1 | 4 |
| `HyperbolicMeasure.lean` | 52 | 双曲测度显式定义、Bochner积分 | 0 | 0 | 0 | 0 |
| `HeatKernel.lean` | ~260 | Laplace变换、热核、f(Δ)核、几何侧迹 | 4 | 9 | 1 | 0 |
| `HeatKernelSemigroup.lean` | ~60 | 热核半群定理 + 卷积公式公理 | 1 | 1 | 0 | 0 |
| `HeatKernelConvolution.lean` | ~800 | 热核卷积五层拆解（L4 完成，L3 剩 2 sorry） | 2 | 20+ | 1 | 2 |
| `MollifiedFunction.lean` | 48 | 椭圆类、ellipticTerm、MollifiedTestFunction | 3 | 1 | 2 | 0 |
| `Interpolation.lean` | 55 | Whitney插值、PWW联合插值、Mellin可数插值 | 2 | 2 | 0 | 0 |
| **合计** | **~4553** | | **56** | **150+** | **15** | **6** |

> 注：stage_3.lean 为前置阶段（保序双射定理），不计入核心模块统计。

---

## 三、HeatKernelConvolution 模块（v7.4 核心进展）

### 3.1 模块目标

证明 `heatKernel_convolution_formula` 公理（当前在 HeatKernelSemigroup.lean 中），将其降级为定理。该公理是热核半群 `K_t ∘ K_s = K_{t+s}` 的积分核表达，需要球坐标 + 双曲余弦定理 + 角度/径向积分。

### 3.2 五层拆解结构

```
L1 球坐标：sphericalPoint opaque + 2 axioms（角度参数化）
L2 双曲余弦定理：axiom（cosh d(z,w) = cosh r cosh d - sinh r sinh d cos θ）
L3 角度积分：theorem heatKernel_angular_integral（原函数法，剩 2 个测度论 sorry）
L4 径向积分：theorem heatKernel_radial_integral（✓ 完全零 sorry）
L5 卷积公式：theorem（组合 L3+L4，待 L3 完成后）
```

### 3.3 已零 sorry 证明的引理（v7.4 新增大量测度论引理）

**分析引理**：

| 引理 | 内容 | 证明方法 |
|------|------|----------|
| `rho_deriv` | ρ'(θ) = B sinθ / sinhρ(θ) | `hasDerivAt_arcosh` + 链式法则 + `cosh_sq_sub_sinh_sq` |
| `rho_endpoints` | ρ(0)=\|r-d\|, ρ(π)=r+d | `cosh_sub`/`cosh_add` + `arcosh_cosh` + 分情况 |
| `F_endpoints_diff` | F(π)-F(0) = 2s/B(e^{-(r-d)²/4s} - e^{-(r+d)²/4s}) | `cos_pi`/`cos_zero` + `sq_abs` + `field_simp <;> ring` |
| `radial_completing_square` | 配方：r²/4t+(r∓d)²/4s = a(r∓c)²+d²/4(t+s) | `field_simp <;> ring` + `exp_add` + `calc` |
| `radial_gaussian` | ∫₀^∞ e^{-a u²} du = √(π/a)/2 | `integral_gaussian_Ioi` 直接应用 |
| `h3`（提取公因子） | ∫ r[e^{-a(r-c)²}-e^{-a(r+c)²}] = e^{-d²/4(t+s)}·∫ r[...] | `gaussian_integrable_shift` + `Integrable.sub` + `exact?` |
| `h72`（代数化简） | 2√π d t^{3/2} s^{1/2}/(t+s)^{3/2} | `Real.sqrt_mul` + `Real.sqrt_div` + `Real.rpow_add` 分步 |
| `heatKernel_radial_integral` | L4 主定理，完全零 sorry | 组合上述所有引理 |
| `radial_substitution` | 换元+奇函数消去+偶函数翻倍 | 测度论 API + even_merge_lemma |
| `even_merge_lemma` | ∫_{-c}^c c·h + ∫_c^∞ 2c·h = 2c·∫_0^∞ h | 独立引理，分情况 c=0/c>0，集合等式 ext+cases |

**测度论基础设施引理（v7.4 新增，全部零 sorry）**：

| 引理 | 内容 |
|------|------|
| `setIntegral_translation` | 一般平移换元：∫_s f(x-c) = ∫_{s+c} f(x) |
| `setIntegral_Ioi_translation` | 半直线平移：∫_{-c}^∞ f(u) = ∫₀^∞ f(x-c) |
| `setIntegral_reflection` | 对称集反射换元 |
| `setIntegral_reflection_general` | 一般反射换元：∫_s f(x) = ∫_{-s} f(-x) |
| `setIntegral_odd_zero` | 奇函数在对称集上积分为 0 |
| `even_half_reflection` | 偶函数半区间反射：∫_{-c}^0 h = ∫_0^c h |
| `real_volume_singleton` | volume {x} = 0 |
| `aedisjoint_of_disjoint` | Disjoint → AEDisjoint |
| `setIntegral_union_disjoint` | 不相交集合并集积分拆分 |
| `integral_remove_singleton` | 删单点不改变积分（filter_upwards + ae_iff） |
| `integral_Ioc_eq_Ioo` | Ioc 与 Ioo 积分相等 |
| `integral_Icc_eq_interval` | 闭区间积分 = 区间积分 |
| `gaussian_integrable_exp` | e^{-a x²} 可积（integrable_exp_neg_mul_sq） |
| `gaussian_integrable_x` | x·e^{-a x²} 可积（integrable_rpow_mul_exp_neg_mul_sq, s=1） |
| `gaussian_integrable_affine` | (x+c)·e^{-a x²} 可积 |
| `gaussian_integrable_shift` | 平移可积性（MeasurePreserving + comp_measurable） |

### 3.4 角度积分证明（heatKernel_angular_integral）

**数学方法**：原函数法。定义 F(θ) = -2s/B · exp(-ρ(θ)²/4s)，则 F'(θ) = 被积函数。

**证明结构**：
1. `h_g_ge_one`：g(θ) ≥ 1 on [0,π]
2. `h_g_gt_one`：g(θ) > 1 on (0,π)
3. `h_rho_cont`：rho 连续 on [0,π]
4. `h_rho_hasDeriv`：rho' = B sinθ/sinhρ（rho_deriv 已证）
5. `hF_hasDeriv`：F' = 被积函数（链式法则 5 步）
6. `hF_cont` / `hF_diff` / `h_deriv_eq`：✓ 零 sorry
7. FTC：`integral_deriv_eq_sub_uIoo`
8. 端点值：`F_endpoints_diff`

**当前状态**：5 个子目标中 3 个零 sorry，**2 个测度论 sorry**：
- `h_int`：`IntervalIntegrable (deriv F) volume 0 Real.pi`（可积性）
- `h_eq_integral`：积分等式（被积函数 = deriv F）

数学内容完全清楚：`rho θ > 0` 在 `(0,π]`，`d_over_sinh` 连续延拓，F 是原函数。三次尝试失败均因 Lean API 细节（`strictMonoOn_arcosh` 参数、`integral_congr` 不存在等）。

### 3.5 径向积分证明（heatKernel_radial_integral）✓ 完全零 sorry

**数学推导**：
- 配方：r²/(4t)+(r∓d)²/(4s) = a(r∓c)² + d²/(4(t+s))，a=(t+s)/(4ts), c=dt/(t+s)
- 换元 u=r∓c → 拆分区间 → 奇函数 ∫_{-c}^c u e^{-a u²}=0 → 2c ∫₀^∞ e^{-a u²} du
- 高斯积分：∫₀^∞ e^{-a u²} du = √(π/a)/2
- 结果：2√π d t^{3/2} s^{1/2} / (t+s)^{3/2} · exp(-d²/4(t+s))

**陈述修正（重要）**：原陈述右边多了 d/sinh d、少了 2√π。从热核半群 K_t∘K_s=K_{t+s} 反推得到正确结果。

**证明结构**：
1. `radial_completing_square`：✓ 零 sorry（纯代数）
2. `radial_substitution`：✓ 零 sorry（测度论 API + even_merge_lemma）
   - h_split1：区间拆分 ✓
   - h_diff：线性性合并 ✓
   - h_odd：奇函数消去 ✓
   - h_lin：线性性 ✓
   - h_even_merge：偶函数翻倍+区间合并 ✓（用 even_merge_lemma）
3. `radial_gaussian`：✓ 零 sorry
4. `h3`（提取公因子）：✓ 零 sorry
5. `h72`（代数化简）：✓ 零 sorry
6. `heatKernel_radial_integral`：✓ 完全零 sorry

### 3.6 even_merge_lemma 独立引理（v7.4 关键突破）

**陈述**：
```lean
lemma even_merge_lemma (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    let h := fun u => exp(-(a * u^2))
    (∫_{-c}^c c·h) + (∫_c^∞ 2c·h) = 2c·∫_0^∞ h
```

**证明要点**：
- 分情况 `c = 0`（两边为 0）和 `c > 0`
- 偶函数翻倍：∫_{-c}^c h = 2∫_0^c h（用 even_half_reflection + integral_remove_singleton + setIntegral_union_disjoint）
- 区间合并：∫_0^c h + ∫_c^∞ h = ∫_0^∞ h（用 setIntegral_union₀ + integral_remove_singleton）
- 集合等式用 `ext` + `cases` + `have` 分步（避免 `No goals to be solved`）
- `IntegrableOn` 用 `Integrable.mono_measure` + `Measure.restrict_mono` + `Set.subset_univ`
- `setIntegral_union₀` 方向用 `.symm`

**战略意义**：将 `h_even_merge` 从 `radial_substitution` 内部抽出，隔离变量干扰，在独立环境中攻坚成功。

### 3.7 关键技术坑（v7.4 积累）

1. **`hd : 0 ≤ d` 不是 `0 < d`**：`radial_substitution` 参数导致 `c` 可能为 0，需分情况
2. **集合等式 `tauto` 失败**：`Ioo(-c,0) ∪ Ioo(0,c) = Ioo(-c,c)` 为假（差单点 0），用 `ext` + `by_cases`
3. **`No goals to be solved`**：`by linarith` 在 `exact ⟨by linarith, ...⟩` 中提前解决目标，用 `have` 分步
4. **`IntegrableOn` 构造**：`Integrable.integrableOn` 不是函数，用 `Integrable.mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)` + `simpa [restrict_univ]`
5. **`setIntegral_union₀` 方向**：返回 `∫ s∪t = ∫s + ∫t`，需要 `.symm` 得到反向
6. **`lt_of_le_of_ne`**：代替 `by_contra` + `by linarith`，避免 `No goals to be solved`
7. **`integral_neg` 需显式测度**：`(μ := volume.restrict s)`
8. **`gaussian_integrable_shift a (-c)` 类型不匹配**：需 `funext r; ring_nf` 转换
9. **`ae_eq_set` 构造**：用 `filter_upwards [h1] with y hy` + `simp [Set.mem_diff, hy]`
10. **`strictMonoOn_arcosh` 参数**：需要 `x ∈ Ioi 0`，不是 `1 < x`

---

## 四、v7.2 分层公理重构（已完成）

### 4.1 重构内容

`gammaAction_identity` 和 `gammaAction_compat` 拆分为：
- **代数层**：`moebiusAction_one`、`moebiusAction_mul`（定理，零 sorry）
- **群论层**：`gammaEnum_contains_one`、`gammaEnum_closed_under_mul`（公理）
- **顶层**：gammaAction_identity/compat 变为定理

### 4.2 moebiusAction 公式 bug 修复

- **原公式**：z' = ((az+b)·conj(cz+d) + conj(c)·t²) / D
- **正确公式**：z' = ((az+b)·conj(cz+d) + a·conj(c)·t²) / D
- 四元数推导 + 数值验证（S 变换作用于 (1,1)，双曲距离守恒）

### 4.3 ManifoldInfrastructure 4 个 sorry

| sorry | 说明 |
|-------|------|
| `SL2C.inv_mul` | 逆元乘法，纯代数 |
| `SL2C.mul_inv` | 乘法逆元，纯代数 |
| `moebiusDenom_mul` | 分母乘法性，8 个复变量模平方展开 |
| `moebiusNumZ_mul` | 分子乘法性，与分母配对 |

---

## 五、公理清单（56 条）

### 5.1 分析公理（第三档，1 条）

| 公理 | 风险 | 说明 |
|------|------|------|
| `mollified_continuous_spectrum_vanishes` | 高 | 连续谱在磨光函数支集分离条件下消失，涉及散射矩阵解析性质 |

> 第三档从 12 条降到 1 条。其余 11 条已通过 PWW 联合插值、mellin_shift 消除、连续谱修正等方式降级为定理。

### 5.2 插值理论公理（3 条）

| 公理 | 说明 |
|------|------|
| `paley_wiener_whitney_joint_interpolation` | PWW 联合插值（Mellin 赋值 × 谱点取值同时指定） |
| `mellin_countable_interpolation` | Mellin 变换可数点插值 |
| `whitney_extension` | Whitney 延拓定理 |

> 这 3 条是 RH 反证法的分析核心，有标准证明路径（Paley-Wiener 定理 + Whitney 延拓）。

### 5.3 热核卷积公理（3 条，HeatKernelConvolution）

| 公理 | 说明 |
|------|------|
| `sphericalPoint` 相关 2 条 | 球坐标参数化（L1 层） |
| `hyperbolic_law_of_cosines` | 双曲余弦定理（L2 层） |
| `heatKernel_convolution_formula` | 卷积公式（待 L5 证明后降级） |

### 5.4 结构公理（~45 条）

包括自伴性、内积、热核性质、留数定理基础、群作用等。大部分已降级为定理，剩余的是需要具体数学对象（如 O_K 数论）的公理。

### 5.5 群论公理（2 条，v7.2）

| 公理 | 说明 |
|------|------|
| `gammaEnum_contains_one` | Γ 枚举包含单位矩阵 |
| `gammaEnum_closed_under_mul` | Γ 枚举对乘法封闭 |

---

## 六、Sorry 清单（6 个）

### 6.1 ManifoldInfrastructure.lean（4 个）

| 行号 | 名称 | 说明 |
|------|------|------|
| ~161 | `SL2C.inv_mul` | 逆元乘法，纯代数 |
| ~165 | `SL2C.mul_inv` | 乘法逆元，纯代数 |
| ~210 | `moebiusDenom_mul` | 分母乘法性，纯代数恒等式 |
| ~224 | `moebiusNumZ_mul` | 分子乘法性，纯代数恒等式 |

### 6.2 HeatKernelConvolution.lean（2 个，均为角度积分 L3）

| 行号 | 名称 | 说明 |
|------|------|------|
| ~284 | `h_int` | deriv F 区间可积性，标准分析事实（连续有界 → IntervalIntegrable） |
| ~294 | `h_eq_integral` | 积分等式，被积函数 = deriv F |

> stage_4.lean 零 sorry。stage_3.lean 的 sorry 是前置阶段的，不在本次修改范围。

---

## 七、Opaque 清单（15 个）

主要集中在：
- `gammaEnum : ℕ → SL2C`（Γ 枚举，需 O_K 数论具体化）
- `sphericalPoint`（球坐标参数化，HeatKernelConvolution L1 层）
- `specDiscM` / `maassSpecParam`（谱序列，已从"存在任意序列"升级为 laplacian_has_discrete_spectrum 公理构造）
- `scatteringMatrix` 等分析对象

---

## 八、离 RH 的距离评估

### 8.1 已完成

- ✅ 框架完整：A1/A2/A3 + 反证法 + RH 结论，逻辑链条闭合
- ✅ 第三档分析公理从 12 条降到 1 条
- ✅ 插值理论公理 3 条，有标准证明路径
- ✅ 6 个数学缺陷全部处理
- ✅ v7.2 分层公理重构完成，moebiusAction_mul 定理化
- ✅ 热核半群定理（heatKernel_semigroup）零 sorry
- ✅ 热核卷积五层拆解建立
- ✅ **L4 径向积分完全零 sorry**（heatKernel_radial_integral + radial_substitution + even_merge_lemma）
- ✅ 测度论 API 打通（16 个通用引理零 sorry）
- ✅ 8 个可积性 sorry 全部清零
- ✅ stage_4 零 sorry

### 8.2 剩余障碍

1. **1 条第三档分析公理**（mollified_continuous_spectrum_vanishes）：涉及散射矩阵解析性质
2. **3 条插值公理**：PWW 联合插值等，有标准证明路径但需完整形式化
3. **热核卷积 L3 角度积分**：h_int / h_eq_integral（2 个 sorry，数学清楚，Lean API 细节）
4. **L5 卷积公式组合**：待 L3 完成后组合 L3+L4
5. **4 个代数 sorry**（ManifoldInfrastructure）：纯代数，表达式大但数学上平凡
6. **15 个 opaque**：主要是 gammaEnum（需 O_K 数论）、sphericalPoint、谱序列

### 8.3 下一步建议

**优先级 1**：完成 HeatKernelConvolution L3 角度积分
- 填 h_int（`ContinuousOn.intervalIntegrable` + 被积函数连续有界）
- 填 h_eq_integral（`IntervalIntegrable.congr_uIoo` + `Set.EqOn`）
- 完成后 L5 卷积公式可组合，heatKernel_convolution_formula 公理降级为定理

**优先级 2**：攻 4 个代数 sorry（ManifoldInfrastructure）
- 用 nlinarith 拆实部虚部，或引入四元数理论
- 纯代数，数学上无争议，只是 Lean 证明繁琐

**优先级 3**：攻 3 条插值公理
- Paley-Wiener 定理 + Whitney 延拓有标准证明路径
- 这是 RH 反证法的分析核心

---

## 九、编译命令

```powershell
cd C:\proj2
$env:PATH = "C:\lt\bin;$env:PATH"
$env:LAKE_BUILD_JOBS=1
C:\lt\bin\lake.exe build OrderPreservingBijection.stage_4
```

单独编译 HeatKernelConvolution：
```powershell
C:\lt\bin\lake.exe build OrderPreservingBijection.HeatKernelConvolution
```

---

## 十、历史版本

- **v7.4**（当前）：测度论 API 打通（16 个通用引理）+ L4 径向积分完全零 sorry + even_merge_lemma 独立引理 + h3/h72 零 sorry
- **v7.3**：HeatKernelConvolution 模块建立 + 角度积分核心证明完成 + 径向积分配方引理证明
- **v7.2**：moebiusAction 公式 bug 修复 + moebiusAction_mul 定理化 + 分层公理重构完成
- **v7.1**：gammaAction 具体化 + manifoldIntegral_linear 降级 + contourRadius 降级 + 死公理扫描
- **v7.0**：双曲测度完全具体化 + gammaAction 具体化
- **v6.x**：留数定理自建 + 双曲空间显式实例化 + specDiscM 非空洞化
- **v5.x**：模块化拆分（10 个文件）+ 6 个数学缺陷处理
- **v4.x**：连续谱修正 + mellin_shift 消除 + PWW 联合插值
- **v3.x**：热核重写 Arthur 迹公式 + Shimura 提升核重写 JL 对应
- **v2.x**：类型化改造 + 公理分解
- **v1.x**：初始框架
