path = r'C:\Users\shtcl\Doubao\chats\2026-09-05\Windows-RH-Lean-PC-2\stage_4_summary.md'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Update version
content = content.replace(
    "> **版本**: v7.7（插值公理攻击第二阶段：whitney + elliptic_term_adjustment 双降为 theorem）",
    "> **版本**: v7.8（插值公理攻击第三阶段：mellin_surjectivity 拆分为纯 Paley-Wiener + 点约束纤维丰富性）"
)

# Update v7.7 bullet and add v7.8
content = content.replace(
    "- **v7.7 插值公理攻击第二阶段**：whitney_mollified_point_interpolation 降为 theorem（分段函数构造），elliptic_term_adjustment 降为 theorem（构造性证明），插值公理从 2 条降至 1 条",
    "- **v7.7 插值公理攻击第二阶段**：whitney_mollified_point_interpolation 降为 theorem（分段函数构造），elliptic_term_adjustment 降为 theorem（构造性证明），插值公理从 2 条降至 1 条\n- **v7.8 插值公理攻击第三阶段**：mellin_surjectivity_over_point_fiber 降为 theorem，拆分为 mellin_transform_countable_surjectivity（纯 Paley-Wiener）+ mollified_point_fiber_mellin_rich（点约束纤维丰富性），混合公理变为两条独立可攻击的公理"
)

# Update module table - Interpolation.lean
content = content.replace(
    "| `Interpolation.lean` | ~200 | Whitney插值（theorem）、PWW联合插值、Mellin满射 | 3 | 4 | 0 | 0 |",
    "| `Interpolation.lean` | ~230 | Whitney插值（theorem）、PWW联合插值、Mellin满射（theorem） | 4 | 5 | 0 | 0 |"
)

# Update total
content = content.replace(
    "| **合计** | **~5500** | | **57** | **160+** | **15** | **3** |",
    "| **合计** | **~5500** | | **58** | **160+** | **15** | **3** |"
)

# Update section 3.7
old_37 = """### 3.7 插值公理当前状态（v7.7）

| 对象 | 风险 | 状态 | 说明 |
|------|------|------|------|
| `whitney_mollified_point_interpolation` | — | **theorem（零 sorry）** | 分段函数构造，v7.7 降级 |
| `elliptic_term_adjustment` | — | **theorem（零 sorry）** | 构造性证明，v7.7 降级 |
| `mellin_surjectivity_over_point_fiber` | 中高 | axiom | Paley-Wiener 满射性，唯一剩余插值公理 |
| `paley_wiener_whitney_joint_interpolation` | — | theorem（零 sorry） | 由 whitney + mellin_surjectivity 推出 |
| `mellin_countable_interpolation` | — | theorem（零 sorry） | PWW 取 S=∅ |
| `elliptic_adjustable_exists` | 低 | axiom | 可调整点存在性 |
| `finite_sum_single_point_change` | 极低 | axiom | 基础有限和性质 |

**插值核心公理从 2 条降至 1 条**（仅剩 mellin_surjectivity_over_point_fiber）。"""

new_37 = """### 3.7 插值公理当前状态（v7.8）

| 对象 | 风险 | 状态 | 说明 |
|------|------|------|------|
| `whitney_mollified_point_interpolation` | — | **theorem（零 sorry）** | 分段函数构造，v7.7 降级 |
| `elliptic_term_adjustment` | — | **theorem（零 sorry）** | 构造性证明，v7.7 降级 |
| `mellin_surjectivity_over_point_fiber` | — | **theorem（零 sorry）** | 由两条公理推出，v7.8 降级 |
| `mellin_transform_countable_surjectivity` | 中高 | axiom | 纯 Paley-Wiener 定理（无点约束），v7.8 新增 |
| `mollified_point_fiber_mellin_rich` | 中 | axiom | 点约束纤维的 Mellin 丰富性，v7.8 新增 |
| `paley_wiener_whitney_joint_interpolation` | — | theorem（零 sorry） | 由 whitney + mellin_surjectivity 推出 |
| `mellin_countable_interpolation` | — | theorem（零 sorry） | PWW 取 S=∅ |
| `elliptic_adjustable_exists` | 低 | axiom | 可调整点存在性 |
| `finite_sum_single_point_change` | 极低 | axiom | 基础有限和性质 |

**v7.8 拆分逻辑**：原 `mellin_surjectivity_over_point_fiber` 是混合公理（同时涉及 Paley-Wiener 满射性和点约束纤维结构）。拆分为：
1. **`mellin_transform_countable_surjectivity`**：纯分析断言，紧支集 TestFunction 的 Mellin 变换在可数点集上满射。标准 Paley-Wiener 定理推论，不涉及点插值约束。
2. **`mollified_point_fiber_mellin_rich`**：空间结构断言，点插值约束不减少 Mellin 变换自由度。{g|g|_S=0} 子空间无限维，其 Mellin 像与全空间相同。

两者独立可攻击：公理 1 可用区间指示函数构造性证明（TestFunction 不要求连续），公理 2 可用泛函分析维数论证。"""

content = content.replace(old_37, new_37)

# Update section 5.1
content = content.replace(
    "### 5.1 公理总数：57 条",
    "### 5.1 公理总数：58 条"
)

# Update section 5.2
old_52 = """### 5.2 高风险公理（诚实评估）

1. **`mellin_surjectivity_over_point_fiber`**：唯一剩余的插值核心公理。Paley-Wiener 满射性，RH 反证法的分析核心。标准证明路径：差空间无限维 + Mellin 变换局部满射性。
2. **`laplacian_has_discrete_spectrum`**：Δ_M 的谱离散、可枚举、无界。双曲三流形标准事实。
3. **`laplacian_spectral_gap`**：0 < specDiscM 0。双曲三流形标准事实（非紧有限体积）。"""

new_52 = """### 5.2 高风险公理（诚实评估）

1. **`mellin_transform_countable_surjectivity`**：纯 Paley-Wiener 定理，紧支集函数 Mellin 变换在可数点集上满射。RH 反证法的分析核心之一。证明路径：区间指示函数基 + 广义 Vandermonde 矩阵可逆（TestFunction 不要求连续，构造自由度极大）。
2. **`mollified_point_fiber_mellin_rich`**：点约束纤维的 Mellin 丰富性。证明路径：{g|g|_S=0} 子空间无限维 + Mellin 变换核无限维，像空间不变。
3. **`laplacian_has_discrete_spectrum`**：Δ_M 的谱离散、可枚举、无界。双曲三流形标准事实。
4. **`laplacian_spectral_gap`**：0 < specDiscM 0。双曲三流形标准事实（非紧有限体积）。"""

content = content.replace(old_52, new_52)

# Update section 6.2
content = content.replace(
    "3. **1 条插值核心公理**（mellin_surjectivity_over_point_fiber）：需要 Paley-Wiener 定理的完整 Lean 化，是 RH 反证法的最后一个分析核心。",
    "3. **2 条插值核心公理**（mellin_transform_countable_surjectivity + mollified_point_fiber_mellin_rich）：原混合公理已拆分，每条更透明、更可独立攻击。"
)

# Update section 6.3
content = content.replace(
    "**最关键的剩余障碍**是 `mellin_surjectivity_over_point_fiber`——这是唯一一条真正的分析核心公理。一旦它被证明，RH 反证法的分析核心就完全闭合了。",
    "**最关键的剩余障碍**是两条插值核心公理：`mellin_transform_countable_surjectivity`（纯 Paley-Wiener）和 `mollified_point_fiber_mellin_rich`（点约束纤维结构）。前者可用区间指示函数构造性攻击，后者可用泛函分析维数论证。"
)

# Update section 7
old_7 = """## 七、下一步优先级

1. **攻 mellin_surjectivity_over_point_fiber**（当前主战场，最后一条插值核心公理）
   - 数学路径：差空间无限维 + Mellin 变换局部满射性
   - 可尝试：Paley-Wiener 定理的标准证明（Fourier 变换 + 紧支集刻画）
2. **清零 HeatKernelConvolution 3 个 sorry**（数学已验证，工程细节）
3. **opaque 实例化**（gammaEnum、sphericalPoint 等）
4. **结构公理降级**（流形、群作用、测度的显式实例化）
5. **finite_sum_single_point_change 降级**（基础有限和性质，Finset.sum_erase API 细节）"""

new_7 = """## 七、下一步优先级

1. **攻 mellin_transform_countable_surjectivity**（当前主战场，纯 Paley-Wiener）
   - 构造路径：区间指示函数 1_{[a,b]} 作为 TestFunction（紧支，不要求连续）
   - M[1_{[a,b]}](s) = (b^s - a^s)/s，选择区间使 Mellin 矩阵可逆
   - 有限 T 版本可构造性证明，可数版本由有限版本逼近
2. **攻 mollified_point_fiber_mellin_rich**（点约束纤维丰富性）
   - 泛函分析路径：{g|g|_S=0} 余维数可数，Mellin 核无限维，像空间不变
3. **清零 HeatKernelConvolution 3 个 sorry**（数学已验证，工程细节）
4. **opaque 实例化**（gammaEnum、sphericalPoint 等）
5. **结构公理降级**（流形、群作用、测度的显式实例化）
6. **finite_sum_single_point_change 降级**（基础有限和性质，Finset.sum_erase API 细节）"""

content = content.replace(old_7, new_7)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Updated summary to v7.8')
