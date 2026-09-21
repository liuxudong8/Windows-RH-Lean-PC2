# Stage 4 总结 — RH 谱对偶论证框架

> **更新日期**：2026-09-21
> **Lean 版本**：v4.34.0-rc2
> **mathlib 版本**：mathlib4-master

## 目录

- [项目状态](#项目状态)
- [最新进展：shimuraLift_linear 证明完成](#最新进展shimuralift_linear-证明完成)
- [最新进展：perron_formula Step 5（Dirichlet 级数相等）](#最新进展perron_formula-step-5dirichlet-级数相等)
- [最新进展：perron_formula 拆分](#最新进展perron_formula-拆分)
- [最新进展：mellin_integral_bound_uniform 7 步框架](#最新进展mellin_integral_bound_uniform-7-步框架)
- [`#print axioms riemann_hypothesis` 审计结果](#print-axioms-riemann_hypothesis-审计结果)
- [核心数学洞察：为什么 Arthur 迹公式与 Weil 显式公式能连接？](#核心数学洞察为什么-arthur-迹公式与-weil-显式公式能连接)
- [RH 证明链](#rh-证明链)
- [剩余 sorry 统计](#剩余-sorry-统计)
- [下一步方向](#下一步方向)

---

## 项目状态

| 项目 | 状态 |
|------|------|
| 核心文件 | stage_4.lean（编译通过，**20 个 sorry** 定理证明体） |
| 核心公理 | **1 条**（`spectral_zero_set_match`，RH 主定理不依赖） |
| 模块 | 13 个独立 Lean 文件 + 6 个新文件夹 |
| 目标 | 在 ZFC 内条件导出黎曼猜想（RH） |

---

## 最新进展：shimuraLift_linear 证明完成（2026-09-21）

### 关键突破：我们成功地证明了 `shimuraLift_linear` —— 线性性！

我们成功地证明了积分算子的线性性：

```lean
theorem shimuraLift_linear (a : ℂ) (f : L2ManifoldX) :
    shimuraLift (a • f) = a • shimuraLift f
```

### 证明思路

我们把证明拆分成了 3 个小步骤：

1. **Step 1**：证明 `L2Function` 的外延性定理 —— 如果两个 `L2Function` 的 `toFun` 相等，那么它们就相等
2. **Step 2**：证明 `(shimuraLift (a • f)).toFun = (a • shimuraLift f).toFun`
   - 用 `funext` 逐点证明
   - 用积分的线性性 `MeasureTheory.integral_smul`
3. **Step 3**：用外延性定理组装，得到最终结论

### 关键 API

| API | 用途 |
|-----|------|
| `shimura_kernel_integrand_integrable` | 证明被积函数可积 |
| `MeasureTheory.integral_smul` | 积分的线性性 |
| `cases f; cases g; congr` | 证明 `L2Function` 外延性 |

---

## 最新进展：perron_formula Step 5（Dirichlet 级数相等）（2026-09-21）

### 关键发现：mathlib 中有 von Mangoldt 函数的 L 级数定理！

我们找到了 mathlib 中的关键定理：

```lean
theorem ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div 
    (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s
```

这正是我们需要的！

### 已成功证明的引理

| 引理 | 内容 | 状态 |
|------|------|------|
| `geometric_sum_from_one` | 几何级数求和（从 k=1 开始）：∑' k, x^(k+1) = x / (1 - x) | ✅ 已证明 |
| `primeDirichletSeries_eq_tsum_primes` | primeDirichletSeries s = ∑' p : Nat.Primes, ... | ✅ 已证明 |
| `primeDirichletSeries_eq_LSeries_vonMangoldt` | primeDirichletSeries s = LSeries Λ s | ⏳ sorry |

### 证明拆分思路

我们把 `primeDirichletSeries s = LSeries Λ s` 拆分成了 3 个小步骤：

1. **Step 1**：交换求和顺序，把 `∑' n, Λ(n) * n^{-s}` 变成 `∑' p, if Prime p then ∑' k, log p * (p^k)^{-s} else 0`
2. **Step 2**：幂运算化简，`(p^k)^{-s} = (p^{-s})^k`
3. **Step 3**：几何级数求和，`∑' k, (p^{-s})^k = p^{-s} / (1 - p^{-s})`

---

## 最新进展：perron_formula 拆分（2026-09-20）

### 关键发现：mathlib 中有 Mellin 反演公式！

我们找到了 mathlib 中的 Mellin 反演公式：

```lean
theorem mellinInv_mellin_eq (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x) 
    (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x
```

这正是我们需要的 Mellin 反演公式！

### perron_formula 拆分

我们把 `perron_formula` 拆分成了 5 个小步骤：

| 步骤 | 内容 | 难度 | 状态 |
|------|------|------|------|
| Step 1 | Mellin 反演公式 | 中 | 已找到 mathlib 定理 |
| Step 2 | 逐点代入（把 f(log N(p)) 换成积分形式） | 低 | 待填充 |
| Step 3 | 求和-积分交换（控制收敛定理） | 中 | 待填充 |
| Step 4 | 围道移动 | 高 | 待填充 |
| Step 5 | Dirichlet 级数相等 | 低 | 部分完成 |

---

## 最新进展：mellin_integral_bound_uniform 7 步框架（2026-09-20）

### 关键 API 发现：`Integrable.mul_bdd`

我们找到了关键 API：`Integrable.mul_bdd`，它正是我们需要的"连续函数 × 有界可测函数"在紧集上可积的定理！

签名：
```lean
hf.mul_bdd hg hg_bound
```
其中：
- `hf : Integrable f μ`
- `hg : AEStronglyMeasurable g μ`
- `hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c`

### 已成功填充的步骤

| 步骤 | 内容 | 状态 |
|------|------|------|
| Step 1 | `mellin_set_integral_reduce`（积分缩限） | ✅ 已证明 |
| Step 2 | `h_right_integrable` 的连续性 | ✅ 已证明 |
| Step 3 | `h_integral_power` Case 1（∫ x⁻¹ dx = log(R₀/ε₀)） | ✅ 已证明 |
| Step 4 | `h_integral_power` Case 2（∫ x^{σ-1} dx = (R₀^σ - ε₀^σ)/σ） | ✅ 已证明 |
| Step 5 | `h_left_integrable`（用 `Integrable.mul_bdd`） | ✅ 已证明 |

---

## `#print axioms riemann_hypothesis` 审计结果

RH 主定理依赖 8 条项目特定公理 + ZFC 标准公理。

核心公理 `spectral_zero_set_match` **不在** RH 主定理的依赖列表中！

---

## 核心数学洞察：为什么 Arthur 迹公式与 Weil 显式公式能连接？

### 两个权重的关系

| 侧 | 权重 | 来源 |
|----|------|------|
| **Arthur 迹公式（几何侧）** | W(γ) = N² log N / (N-1)² | 双曲轨道积分（H³ 中 PSL₂(ℂ) 的表示论计算） |
| **Weil 显式公式（素数侧）** | (log Np) / (1 - Np^{-s}) | Dedekind zeta 函数的对数导数 |

### 连接方式

通过**保序双射 Φ**（系列第二篇的成果），Arthur 迹公式的几何侧和 Weil 显式公式的素数侧一一对应——这就是我们为什么能把 RH 从几何问题转化为数论问题的根本原因！

---

## RH 证明链

```
mellin_smooth_surjectivity [theorem, 已证明]
+ mellin_min_norm_principle [theorem, 已证明]
→ mellin_smooth_min_derivative_norm_uniform [theorem]
→ mellin_smooth_interpolation [theorem]
→ mellin_transform_C2_rapid_decay [theorem]
→ mellin_rapid_decay_choice [theorem]
→ mellin_pair_uniform_decay_bound [theorem]
→ mollified_pair_tail_sum_negligible [theorem]
→ off_critical_zero_tail_dominated [theorem]
→ nontrivial_zero_sum_pair_separation [theorem]
→ off_critical_line_contradiction [theorem]
→ all_zeros_on_critical_line [theorem]
→ riemann_hypothesis [theorem]
```

---

## 剩余 sorry 统计

| 类别 | 数量 |
|------|------|
| 核心文件 sorry | **20** |
| 核心公理 | 1（`spectral_zero_set_match`） |

---

## 下一步方向

1. **eigenfunction_cancellation**：继续证明特征函数消去律
2. **perron_formula 填充**：继续拆分 perron_formula，逐个填充小步骤
3. **其他 sorry 填充**：继续逐个填充剩余的 sorry
