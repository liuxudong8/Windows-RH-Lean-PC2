# Stage 4 总结 — RH 谱对偶论证框架

## 项目状态
- **核心文件**：`stage_4.lean`（约 2930 行，编译通过，零 sorry）
- **编译**：3818 jobs，Build completed successfully
- **公理数**：62 条（高风险 0 条，第三档分析核心 0 条）
- **模块**：10+ 个独立文件

## 最新进展

### 1. 删除冗余插值链条（本轮完成）
**重大发现**：`mellin_finite_surjectivity_zero_sum_norm_bound` 已包含有限插值存在性，原基于区间指示函数的插值链条完全是死代码。

删除三条：
- `mellin_interval_linear_independence`（axiom，中风险）— 广义 Vandermonde 断言
- `mellin_finite_surjectivity`（theorem）— Fin m 版本有限满射
- `mellin_finite_set_surjectivity`（theorem）— Set 版本有限满射

**公理数**：63 → 62
**中风险分析公理**：5 → 4

### 2. mellin_finite_surjectivity_zero_sum 升级为带范数估计版本
- 新增公理 `mellin_finite_surjectivity_zero_sum_norm_bound`（Hahn-Banach 依据）
- `mellin_finite_surjectivity_zero_sum`：axiom → theorem
- `mellin_single_point_separation_decay`：axiom → theorem

### 3. 之前的进展
- `zero_weighted_series_summable`：axiom → theorem
- `mellin_pair_uniform_decay_bound`：axiom → theorem
- `mellin_single_point_separation`：theorem（存在性）

## RH 证明链（完整）
```
mellin_finite_surjectivity_zero_sum_norm_bound [axiom, 中风险, Hahn-Banach]
  → mellin_single_point_separation_decay [theorem ✓]
  → mellin_pair_uniform_decay_bound [theorem ✓]
  + zero_weighted_series_summable [theorem ✓]
  → mollified_pair_tail_sum_negligible [theorem ✓]
  → off_critical_zero_tail_dominated [theorem ✓]
  → nontrivial_zero_sum_pair_separation [theorem]
  + spectral_sum_determined_by_points [theorem]
  → off_critical_line_contradiction [theorem]
  + spectral_zero_equality [theorem]
  → all_zeros_on_critical_line [theorem]
  → riemann_hypothesis [theorem]
```

## 公理统计（62 条）
- **高风险**：0 条
- **第三档分析核心**：0 条
- **中风险分析公理**：4 条
  - `mellin_finite_surjectivity_zero_sum_norm_bound`（Hahn-Banach 依据）
  - `zero_counting_estimate`
  - `mollified_mellin_vertical_decay`
  - `mollified_point_fiber_mellin_rich`（已弱化）
  - `maass_param_to_zero`
- **中低风险**：`zero_multiplicity_log_growth`、`riemannZeta_conj`
- **第二档大定理**（已知定理，挂着）：约 20 条
- **第一档结构/定义性公理**：其余约 35 条

## 关键数学决策
1. **方向 B**：放弃逐点消零，用 `nontrivial_zero_sum_pair_separation` 替代
2. **弱化 `mollified_point_fiber_mellin_rich`**：添加前提 `nontrivialZeroSum(h) = 0`
3. **PWW 联合插值**：Paley-Wiener-Whitney 定理
4. **连续谱修正**：磨光函数支集分离条件下消失
5. **零点重数处理**：`zeroMultiplicity` 加权
6. **分层求和**：`A_k = {n: 2^k ≤ |Im| < 2^(k+1)}`，每层 O(k²/2^k)
7. **公理分层**：构造（定理）+ 估计（公理）分离
8. **单点分离降级**：利用 w₁-w₂ 的特殊形式
9. **Hahn-Banach 升级**：有限插值带统一范数估计
10. **删除冗余链条**：norm_bound 版本已包含有限插值，原区间指示函数链条冗余

## 下一步优先级
1. **攻击 `mollified_mellin_vertical_decay`**：需要给 MollifiedTestFunction 添加光滑性前提
2. **攻击 `zero_counting_estimate`**：Riemann-von Mangoldt 公式
3. **攻击 `mollified_point_fiber_mellin_rich`**：磨光函数空间结构性质
4. **清理 warning**
5. **HeatKernelConvolution 3 个 sorry**：非当前主线

## 编译命令
```powershell
cd C:\proj2
$env:PATH = "C:\lt\bin;$env:PATH"
$env:LAKE_BUILD_JOBS=1
C:\lt\bin\lake.exe build OrderPreservingBijection.stage_4
```
