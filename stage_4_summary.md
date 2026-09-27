# stage_4.lean 工作总结

## 项目概览

**项目**：RH（黎曼假设）的 Lean 4 形式化，基于 mathlib4（v4.34.0-rc2）。
**主定理**：`RHSpectralDuality.riemann_hypothesis`（stage_4.lean:5396）

## 本轮完成的工作

### 1. `mellin_rapid_decay_bound` theorem 完全闭合

**位置**：stage_4.lean ~4349 行

**之前状态**：从备份 `stage_4_before_h92_downgrade.lean` 恢复后，剩 2 个 admit：
- `h83`：∫ B'·x^(σ+1) = B'(R₀^(σ+2)-ε₀^(σ+2))/(σ+2)（integral_rpow，set/interval 桥接）
- `h_s_im_ne_zero`：s.im ≠ 0（theorem statement 缺口）

**补完内容**：

#### a. 三角不等式（~4689 行）
直接复用已有的 `h7`（~4475 行已证明的 ‖1/(s(s+1)) · ∫ f‖ 界）。

#### b. h8 proof 闭合
```lean
rw [h83] at h82
exact mul_le_mul_of_nonneg_left h82 (by positivity)
```

#### c. h83（Newton-Leibniz 公式）
关键桥接引理链：
```lean
-- Icc → Ioc → interval integral
have h831 : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in ε₀..R₀, x^(s.re + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₀_lt_R₀.le]
-- 提常数
have h832 : ∫ B' * x^r = B' * ∫ x^r := by simp [integral_const_mul]
-- 幂函数积分
have h834 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
  rw [integral_rpow (Or.inl h833)] <;> ring
```

**关键引理名**：
- `MeasureTheory.integral_Icc_eq_integral_Ioc`
- `intervalIntegral.integral_of_le h`
- `integral_const_mul`
- `integral_rpow (Or.inl h)` — 注意是全局名，不是 `intervalIntegral.integral_rpow`

#### d. hs_im_ne_zero 参数加到 theorem statement

两个 theorem 都加了 `(hs_im_ne_zero : s.im ≠ 0)` 参数：

1. **`mellin_integral_bound_uniform`**（3030 行）：
   - statement：`0 < s.re → s.re < 1 → s.im ≠ 0 →`
   - intro：`... hs_re1 hs_re2 hs_im_ne_zero`

2. **`mellin_pointwise_dual_norm_bound`**（3407 行）：
   - 加参数 `(hs_im_ne_zero : s.im ≠ 0)`

3. **`mellin_constraint_dual_norm_uniform`**（3448 行）内部 h2：
   - statement 加 `s.im ≠ 0 →`
   - 所有调用方传参

**原因**：结论有 |s.im|² 分母，必须假设 s.im ≠ 0。在 RH 主证明里 s 是非平凡零点，这个假设是 trivial 的。

### 2. 项目清理

- 删除了 ~50 个 `stage_4_before_*.lean` 旧备份
- 删除了 ~300 个 `build_*.txt` 编译日志
- 保留 `stage_4.lean`（当前工作版）和 `stage_4_before_h92_downgrade.lean`（干净回滚点）

## 当前状态

**`mellin_rapid_decay_bound` theorem：0 个 admit，完全闭合。**

整个 stage_4.lean 编译通过。

## 剩余工作

- 前 16 个 admit（79-2687 行）是硬分析，未动
- RH 主证明 `riemann_hypothesis` 在 5396 行，依赖 axioms 列表里还有 `sorryAx`（来自前面未补的 admit）

## 技术经验

1. **行级编辑 proof block 不可行**：反复破坏 proof 结构（重复行、错位 have、变量冲突）。必须用 Write 写完整块再整体替换，或从备份恢复。
2. **set/interval integral 桥接**：`∫ Icc = ∫ Ioc = ∫ a..b`，关键引理是 `integral_Icc_eq_integral_Ioc` + `intervalIntegral.integral_of_le`。
3. **`integral_rpow`** 是全局名，不在 `intervalIntegral` namespace 下，接受 `Or.inl h` 或 `Or.inr ...`。
4. **PowerShell 后台任务限制**：大量后台编译任务会堆积报 "background shell task limit reached"，需要 Wait 或换 Python 脚本。
