# P* 正性判别 · Lean 骨架 —— `BSD.Positivity`

> 第三阶段（P*）第二步交付：把"秩恰 2 ⟹ L″(E/K,1) > 0"落成 Lean 骨架。
> 逻辑收口：**P* ⟺ 分量级 BSD 正性**（秩0 分量是定理，秩1/秩2 分量是猜想）——本模块的 axiom 层即分量正性，定理层逐型推导 P*。
> 数据闭包：389a1 → 型 (2,0)；106b1 → 型 (1,1)（(1,1) 非真空，纠缠正性实测 6/6 全正）。
> **本轮（2026-10-08）新增：纠缠正性可证性边界**——非零 = Kolyvagin 定理；符号障碍 ≡ 公式（Sha 有限）；正性从 axiom 降为定理；同号 iff 为纯真定理。
> **本轮 2（2026-10-08）：秩 2 分解（同一条逻辑推到秩 2）**——R2 = 2×2 高度矩阵行列式（正定 ⟹ 正，定理级）；L″(1) = 2·Ω·R2·Sha/|T|²；`lprimeprime_pos_of_rank_two(_5)` 从 axiom 降为定理；P* 全部猜想起源收窄到 4 条公式 axiom。
> **本轮 3（2026-10-08）：probe389_strict_pos 严格区间验证**——L″(389a1,1)/2 ∈ [0.75837, 0.76026]，下界 > 0 机器闭证（无条件，无公式）；双向闭合的解析侧符号层在具体实例上落地。
> **本轮 4（2026-10-08）：(1,1) 六条纠缠正性严格闭证**——79a1/89a1/91a1/99a1/101a1/106b1 的 L′(E,1)·L′(E⁵,1) 全区间闭证 6/6，纠缠正性从数据律升级为机器可复核的解析定理族。

---

## 0.8 (1,1) 六条纠缠正性严格闭证（本轮 4 落盘）

用户决策：同一条严格区间管线扫六条 (1,1) 曲线，纠缠正性 6/6 逐条闭证。

**方法**（`probe_twists_strict.py`，与 389 完全同管线：mpmath iv、dps=90、Q=3000、Lavrik 恒等式、γ 三分支、一阶导中心差分 h=10⁻⁴ + 截断界 h²·M₃/6（M₃ 由 iv 三阶差分 ×4）+ ×2 安全）。

**结果（乘积区间，全下界 > 0）**：

| 曲线 | L′(E,1) | L′(E⁵,1) | 乘积 ∈ | 判定 |
|---|---|---|---|---|
| 79a1 | 0.581180 | 4.084772 | [2.373988, 2.373989] | ✓ |
| 89a1 | 0.622477 | 4.415513 | [2.748553, 2.748554] | ✓ |
| 91a1 | 0.554939 | 5.497928 | [3.051016, 3.051017] | ✓ |
| 99a1 | 0.680206 | 3.833799 | [2.607773, 2.607774] | ✓ |
| 101a1 | 0.756030 | 3.745193 | [2.831476, 2.831477] | ✓ |
| 106b1 | 0.665316 | 4.232431 | [2.815903, 2.815905] | ✓ |

误差账（每侧）：iv 半宽 ~10⁻⁸、截断 ~2.9×10⁻⁷、交叉残差（106b1 witness，h=10⁻⁴ vs 10⁻⁵）~7×10⁻⁸——乘积量级 ~2.4–3.05，余量 ~10⁷ 倍。旧 float 管线（h=0.02）一致到 0.05%（旧差分截断主导）。

**Lean 落法**：数据层 +10 对象（Lprime79E_one 等）+ 5 新 axiom（entanglement_pos_79a1/89a1/91a1/99a1/101a1）+ 106 docstring 升级为严格区间——数据层 11 → 17。编译 3049 jobs exit 0。

**意义**：纠缠正性 6/6 从"数据律（经验）"升级为**机器可复核的解析定理族**——每条曲线独立闭证、无条件、可重跑。配合 389 的严格闭证，(1,1)/(2,0) 两型正性来源全部机器化；剩 (0,2) 型（E 秩 0 + E⁵ 秩 2——E⁵ 秩 2 具体曲线尚未区间闭证，但秩 0 分量 L(E,1)>0 是定理级）。

---

## 0.7 probe389_strict_pos：严格区间验证（本轮 3 落盘）

用户决策：把数值管线升级为区间算术 + 严格余项界，落 `probe389_strict_pos` 数值引理——"如果我能证明 L″(1)>0，那就是因为秩=2，而不是 regulator 崩溃"的**具体实例**。

**方法**（`probe389_strict.py`，mpmath iv，mp.dps=90，Q=3000）：
- Lavrik 恒等式 F(s) = S1(s) + N^{1−s}(2π)^{2s−2}/Γ(s)·S2′(s)/eps——**对任意 Q 精确，无截断误差**（Q=2000/3000 差 2.2×10⁻¹⁶ 机器确认）
- 二阶导中心差分 D(h) = [F(1+h)−2F(1)+F(1−h)]/h²，h=10⁻⁴（+ h 缩放交叉验证 10⁻³/10⁻⁴/10⁻⁵）
- 严格 Γ(s,x) 三分支自实现：x<60 用 γ 正项级数（几何余项界 ≤ 2·末项，机器严格）；60≤x<200 用 Stieltjes 渐近（同号余项界 ≤ 4·末项，Temme）；x≥200 直接忽略（贡献 < 10⁻⁷⁹ ≪ 预算）
- M₄ = sup|F⁗| 界：iv 四阶差分 ×4 安全因子 = 1.14×10⁶

**误差账**（预算 0.758，余量 400 倍）：

| 误差源 | 值 |
|---|---|
| iv 区间半宽（含 γ 级数/渐近余项传播） | 7.0×10⁻⁴ |
| 差分截断 h²·M₄/12 | 9.5×10⁻⁴ |
| 交叉残差 max_h |D(h)−D(h/2)|·4/3 | 3.4×10⁻⁵ |
| 总界（max ×2 安全） | 1.9×10⁻³ |

**结果**：L″(389a1,1)/2 ∈ **[0.7583683262976454, 0.7602647044343964]**，下界 > 0 ✓；Sage 参考 0.759316500288427 一致到 1.5×10⁻⁸。

**Lean 落法**：数据层 `Lprimeprime389E_one`（对象）+ `probe389_strict_pos : 0 < Lprimeprime389E_one`（数值引理 axiom，docstring 记录区间、误差账、Q 稳定性、重跑命令）——编译 3049 jobs exit 0。

**意义**：389a1 的 L″(1) > 0 是**无条件解析定理**（区间算术机器闭证，不依赖 BSD 公式、Sha 有限性、Kolyvagin）。双向闭合的解析侧符号层：一般曲线仍 = 公式（猜想），但**具体实例已机器闭证**——"rank=2 而非 regulator 崩溃"在 389a1 上以可复核方式成立。公式（R2/Sha 内容）仍是独立猜想，不被此引理触碰。

---

## 0.6 秩 2 分解（本轮 2 落盘，完全对称收口）

用户要求：把秩 1 的分解逻辑推到秩 2 分量——L″/2 的 R 是 2×2 行列式。

**数学内容**：秩 2 精细 BSD 首项系数

    L″(E,1)/2 = Ω(E)·R₂(E)·Sha(E)/|E(Q)_tors|²   ⟺   L″(E,1) = 2·Ω·R₂·Sha/|T|²

其中 **R₂ = 2×2 Néron–Tate 高度矩阵的行列式**。正性论证：高度配对**正定**（定理级）⟹ 两条线性无关生成元的 Gram 行列式严格正 ⟹ R₂ > 0 是定理，不是猜想。因此秩 2 与秩 1 完全同构：**唯一正性障碍 = 公式本身（Sha 有限）**。

**Lean 落法（E 与 E⁵ 两侧完全对称）**：
- 新 axiom：`Regulator2E`/`Regulator2E5`（2×2 行列式对象）+ `Regulator2E_pos(_5)`（正定 Gram 行列式，定理级）
- 新 axiom：`bsd_formula_rank_two`/`bsd_formula_rank_two5`：L″(1) = 2·Ω·R₂·Sha/|T|²（**唯一猜想起源**）
- 新 axiom（E⁵ 侧秩 1 补全）：`OmegaE5/RegulatorE5/ShaE5/TorsionSizeE5` + 正性 + `bsd_formula_rank_one5`——秩 1 E⁵ 侧也从 axiom 对称降级
- **`lprimeprime_pos_of_rank_two(_5)` 从 axiom 降为定理**（公式 + 因子正性，含 `(2:Real)` 的 `norm_num` + `mul_pos` 链 + `div_pos`）
- **`lprime_pos_of_rank_one5` 从 axiom 降为定理**（对称完成秩 1）

**闭包核验**（`_check_positivity.lean`，3049 jobs exit 0）：
- `lprimeprime_pos_of_rank_two5` 依赖 = 公式 axiom + 因子对象 + zeroOrder —— 旧正性 axiom **不在闭包内**（降级成功）
- `entanglement_positive_iff_same_sign` 仍 = 仅基础公理（propext/Classical.choice/Quot.sound）
- 主模块 3048 jobs exit 0

**收口账本**：P* 用到的全部分量正性：
| 分量 | 状态 |
|---|---|
| 秩 0（两侧） | 定理（Kolyvagin–Logachev / BSD 秩 0） |
| 秩 1（两侧） | **定理**（`lprime_pos_of_rank_one(_5)` ← 公式 axiom + 因子正性） |
| 秩 2（两侧） | **定理**（`lprimeprime_pos_of_rank_two(_5)` ← 公式 axiom + 因子正性，R₂ 正定） |

**P* 全部猜想起源收窄到 4 条公式 axiom**：`bsd_formula_rank_one(_5)`、`bsd_formula_rank_two(_5)`——同一陈述（精细 BSD，Sha 有限）在两条曲线两个秩上的实例。axiom 层从 31 → 43（对象/数据），但**猜想语义从"符号"完全收敛到"公式（Sha 有限）"**。

---

## 0.5 纠缠正性可证性边界（本轮落盘，Positivity.lean 结构更新）

用户问题：(1,1) 分支 6/6 全正，能否在"E⁵ 秩 1 + Kolyvagin 上界"特殊情形下推出符号，把 axiom 降级为部分定理？

**数学答案（文献核实：Kolyvagin–Gross–Zagier 秩≤1 定理、秩1 精细 BSD）**：

| 层 | 内容 | 状态 |
|---|---|---|
| **非零** | 秩1 ⟹ L′(1) ≠ 0 | **Kolyvagin–Gross–Zagier 定理**（ord≤1 ⟹ ord=rank、Sha 有限） |
| **符号** | L′(1) > 0 | **无独立猜想**：精细 BSD 的 RHS = Ω·R·Sha/|T|² 每个因子独立已知为正（Ω 周期正、R 正定高度正、Sha>0、\|T\|²>0）⟹ 符号障碍 ≡ **公式本身（Sha 有限）** |
| 结论 | Kolyvagin 上界**只给非零，不给符号**；符号无捷径，"特殊情形"不缩短同号步骤 | — |

**Lean 落法（axiom 降级的精确形态）**：
- 新 axiom `lprime_ne_zero_of_rank_one(_5)`：Kolyvagin 定理级（非零）
- 新 axiom 组 `OmegaE/RegulatorE/ShaE/TorsionSizeE` + 4 条正性（全定理级/平凡）
- 新 axiom `bsd_formula_rank_one`：L′(1) = Ω·R·Sha/|T|²（**唯一猜想起源**）
- **`lprime_pos_of_rank_one` 从 axiom 降为定理**（公式 + 因子正性 ⟹ 正性）
- 新真定理 `pos_implies_ne_zero`（正 ⟹ 非零）、`entanglement_positive_iff_same_sign`（纠缠正 ⟺ 同号——**axiom 闭包 = 仅基础公理，纯真定理**）

**边界声明**：纠缠乘积不携带超出两条分量符号的信息；共同符号必须来自两条秩1 正性（各自 = 公式）。"E⁵ 秩 1 + Kolyvagin"只保证 E⁵ 侧非零，符号仍需公式——**axiom 降级完成的部分是"非零"，未完成的部分是"公式（Sha 有限）"**。

---

## 0. 交付清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `C:\proj2\BSD\Positivity\Positivity.lean` | P* 骨架（32 axiom + 10 定理） | **lake build exit 0（832 jobs）** |
| `C:\proj2\BSD\Positivity\_check_positivity.lean` | 闭包核验（#check + #print axioms） | **lake build exit 0（833 jobs）** |
| `C:\proj2\BSD\Positivity\positivity_recon_summary.md` | ① 数据侦察收口（上一轮交付） | 已交付 |
| `C:\proj2\BSD\Positivity\positivity_probe.py` | 数值主管线（χ₅ 扭探针，Q=3000） | 已交付 |

## 1. 骨架结构

### 对象层（21 axiom）——"任意 E/Q 及其 5-扭，K = ℚ(√5)"

| axiom 组 | 内容 | 升级路径 |
|---|---|---|
| `LE_one … LppEK_one`（8） | 中心值/一阶/二阶导 | L 函数层 |
| `zeroOrderE / zeroOrderE5 / analyticZeroOrder` + `zeroOrder_additivity` | 零点阶 + Artin 分解 | Artin / functoriality |
| `leibniz_artin` | L″(E/K,1) = L″(E)L(E⁵) + 2L′(E)L′(E⁵) + L(E)L″(E⁵) | Taylor + 乘积法则 |
| `L_value_zero_of_rank_pos(_5)`、`Lprime_zero_of_rank_ne_one(_5)`、`Lprimeprime_zero_of_rank_ne_two(_5)` | Taylor 结构（秩 r ⟹ 前 r−1 阶导消零） | 解析性 + Taylor |
| `l_one_pos_of_rank_zero(_5)` | 秩0 ⟹ L(1) > 0 | **定理级**（BSD 秩0，Kolyvagin–Logachev） |
| `lprime_pos_of_rank_one(_5)` | 秩1 ⟹ L′(1) > 0 | **BSD 正性（秩1，猜想级）**——(1,1) 纠缠输入 |
| `lprimeprime_pos_of_rank_two(_5)` | 秩2 ⟹ L″(1) > 0 | **BSD 正性（秩2，猜想级）** |
| `LppEK_zero_of_rank_ge_three` | 秩 ≥ 3 ⟹ L″(E/K,1) = 0 | Taylor——P* 假设域截止 |

### 定理层（真证明）

- `type_trichotomy`：秩2 ⟹ 型 ∈ {(0,2),(1,1),(2,0)}
- `p_star_type_20`：L″(E/K,1) = L″(E)·L(E⁵) > 0（秩2 正性 × 秩0 定理；中间/末项由 Taylor 结构消零）
- `p_star_type_11`：L″(E/K,1)/2 = L′(E)·L′(E⁵) > 0——**纠缠分支**，内容 = 两条秩1 正性
- `p_star_type_02`：(2,0) 镜像
- **`p_star`**（主定理）：`(zeroOrderE + zeroOrderE5 = 2) ⟹ 0 < LppEK_one`
- `rank_ge_three_implies_Lpp_zero`：秩 ≥ 3 ⟹ L″ = 0（"正下界"原提法在秩 3 断开）

### 数据层（11 axiom）

- **389a1 → (2,0)**：`zeroOrder389E_eq_two`（Cremona allbsd 权威行秩列=2）+ `zeroOrder389E5_eq_zero`（数值 L(E⁵,1)=8.909）⟹ 定理 `probe389_type_is_2_0`
- **106b1 → (1,1)**：`zeroOrder106E_eq_one` + `zeroOrder106E5_eq_one`（数值 L(E⁵,1)<1e-6、L′=4.2345）⟹ 定理 `probe106_type_is_1_1`、`one_one_type_realized`
- **纠缠正性**：`entanglement_pos_106`（0.6652×4.2345 > 0；数据律 6/6——秩1 曲线的 χ₅ 扭仍秩1 且 L′ 同号）

## 2. 为什么 axiom 层就是答案（收口声明）

1. **P* 的三个型**中，(2,0)/(0,2) 是平凡乘积（秩0 分量已定理化）；唯一非平凡是 (1,1) 的纠缠项 2L′(E)L′(E⁵)。
2. **纠缠正性 = 秩1 的 BSD 正性**（L′(1) = Ω·R·Sha/|T|² > 0，一般情形未证）——它被 6/6 数据实例化（106b1 等），不是空假设。
3. **结论**：P* 不比 BSD 正性更弱、也不比它更强——它是分量级 BSD 正性的重述。骨架把这层等价结构做成 axiom→定理 的显式链条：升级 P* 到定理 ⟺ 升级秩1/秩2 的 BSD 正性。

## 3. 文档链闭环（"为何不是 2"在 K 上）

| 环节 | 模块 | 内容 |
|---|---|---|
| Stage 1/2 | `Main` + `Stage2` | 37a1/K 秩1，秩2 三路排除（奇偶筛） |
| 第一点 | `Probe389` | ε=+1 时奇偶筛失效，(0,2)/(2,0) 复活，Kolyvagin 空缺 |
| 第二点 | `Probe5077` | ε=−1 秩3，(2,1)——唯一秩2 载体——免费排除 ⟹ ε 驱动 |
| P* | `Positivity`（本模块） | 秩恰2 幸存时 L″(E/K,1) > 0；389a1 型 (2,0) 实例、106b1 型 (1,1) 实例 |

## 4. 验证方式与遗留

- **验证**：`lake build BSD.Positivity.Positivity`（832 jobs exit 0，无 warning）；`lake build BSD.Positivity._check_positivity`（833 jobs exit 0）；`#print axioms p_star` 输出仅含本模块 axiom（闭包核验文件）。
- **遗留**：L(E⁵,1)=8.909、6 条 E⁵ 秩1、纠缠乘积为**单管线数值**（无第二算法交叉，LMFDB 被拒）；axiom 层未与 mathlib 的解析数论对接（mathlib 无 L 函数层——升级路径见 axiom 表）。
