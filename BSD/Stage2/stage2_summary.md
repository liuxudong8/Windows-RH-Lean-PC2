# Stage 2 —— Q(√5) 下秩 2 排除引理（Lean 骨架）

> 更新：2026-10-07。第二阶段：回答"为何不是秩 2"。与 Stage 1（BSD.Main，解析秩 = 1）衔接：**解析秩 = 1 唯一，秩 2 被根数奇偶三重排除，无需任何数值输入**。

## 0. 一句话定位

Stage 1 证明了"解析秩(E/K) = 1"（L_K′(1) > 0 的区间判定 + 函数方程）。Stage 2 给出互补结论：**解析秩 ≠ 2**——纯根数奇偶论证（函数方程层面），axiom 闭包干净，主定理是 Lean 真定理。

## 1. 论证结构（修正版）

核心事实（全部秩无关、无数值输入）：

```
epsilon(E)   = -1  ==>  ord_1 L(E)   奇        （函数方程奇偶性）
epsilon(E^5) = +1  ==>  ord_1 L(E^5) 偶
ord_1 L(E/K) = ord_1 L(E) + ord_1 L(E^5)        （Artin 分解加性）
```

推论：ord_1 L(E/K) = 奇 + 偶 = 奇 ==> **解析秩 ≠ 2**。

### 1.1 型筛版（结构展示）

若 ord_1 L(E/K) = 2，加性给出非负整数解 (a, b)，a + b = 2：

| 型 | 条件 | 奇偶检查 | 结论 |
|---|---|---|---|
| (0,2) | a = 0, b = 2 | a = 0 偶，但 epsilon(E) = -1 强制 a 奇 | 排除 |
| (1,1) | a = 1, b = 1 | b = 1 奇，但 epsilon(E^5) = +1 强制 b 偶 | 排除 |
| (2,0) | a = 2, b = 0 | a = 2 偶，但 epsilon(E) = -1 强制 a 奇 | 排除 |

三种型全死 ==> 秩 2 无型可居。

### 1.2 更正记录（重要）

上一轮讨论（2026-10-07）把 (0,2) 判为"唯一候选"，**错误**。epsilon(E) = -1 强制 ord_1 L(E) 恒奇，故 (0,2)（需 ord_1 L(E) = 0）同样被奇偶排除。修正后结论更强：**秩 2 排除完全不需要数值**。数值路径（L(E^5,1) ≠ 0 ==> ord_1 L(E^5) = 0）仅作为独立双保险保留（`zeroOrderE5_eq_zero`、`no_type02_numeric`）。

### 1.3 结构定理

`parityK_propagated`：ord 奇偶从 E/E^5 两侧经加性传播到 E/K，**不依赖 epsilon(E/K) = -1 的 axiom**——epsilon(K) 数值 axiom 对秩 2 排除是冗余的（结构性证明）。`rootNumberK_from_product`：乘性根数 epsilon(E/K) = epsilon(E)·epsilon(E^5) 的数值一致性由 `norm_num` 验证。

## 2. 文件结构

```
c:\proj2\BSD\Stage2\
├── RankTwoExclusion.lean   # 骨架主体（模块 BSD.Stage2.RankTwoExclusion）
├── _check_stage2.lean      # #print axioms 核验脚本
└── stage2_summary.md       # 本文件
```

## 3. axiom 清单（独立声明层，13 个）

| axiom | 含义 | 升级路径 |
|---|---|---|
| `rootNumberE` | epsilon(E) | 自守 L 理论（mathlib 缺失） |
| `rootNumberE5` | epsilon(E^5) | 同上 |
| `rootNumberK` | epsilon(E/K) | 同上 |
| `rootNumberE_eq_neg_one` | epsilon(E) = -1 | 局部根数（C5 审计） |
| `rootNumberE5_eq_one` | epsilon(E^5) = +1 | chi_5 本原 + gcd(37,5)=1 无修正 |
| `rootNumberK_eq_neg_one` | epsilon(E/K) = -1 | 乘性规则 epsilon(E)*epsilon(E^5) |
| `zeroOrderE` | ord_1 L(E) | L 函数层 |
| `zeroOrderE5` | ord_1 L(E^5) | L 函数层 |
| `analyticZeroOrder` | ord_1 L(E/K) | L 函数层 |
| `parity_neg_one` | eps = -1 ==> 阶奇 | 函数方程 |
| `parity_pos_one` | eps = +1 ==> 阶偶 | 函数方程 |
| `zeroOrder_additivity` | Artin 分解加性 | Artin/L 函子性 |
| `zeroOrderE5_eq_zero_of_L_E5_one_ne_zero` | 中心值非零 ==> 阶 0 | 解析性 + Taylor 展开 |

## 4. 定理清单（真证，axiom 闭包 = 声明层 + 基础）

- `oddE` / `evenE5` / `oddK`：奇偶实例化
- `parityK_propagated`：奇偶传播（无需 epsilon(K) axiom）
- `rootNumberK_from_product`：乘性根数数值一致性
- `analyticRankK_ne_two`：解析秩 ≠ 2（直接奇偶版，主定理）
- `rank_two_decomposition`：秩 2 型分解 (0,2)|(1,1)|(2,0)
- `no_type02` / `no_type11` / `no_type20`：三型逐一排除
- `analyticRankK_ne_two'`：解析秩 ≠ 2（型筛版，与直接版殊途同归）
- `zeroOrderE5_eq_zero` / `no_type02_numeric`：数值双保险

## 5. 与 Stage 1 的衔接

- Stage 1：`BSD.Main.analytic_rank_K_eq_one`（解析秩 = 1，L_K′(1) > 0 真证）
- Stage 2：`analyticRankK_ne_two`（解析秩 ≠ 2，纯奇偶）
- 合并结论：**E/Q(√5) 解析秩恰为 1，秩 2 在解析侧不可能**。秩 2 的三种组合型（(0,2)/(1,1)/(2,0)）全部被根数奇偶排除：E 侧 epsilon(E) = -1 排除 (0,2)/(2,0)，E^5 侧 epsilon(E^5) = +1 排除 (1,1)。

## 6. 编译与核验

```powershell
Set-Location c:\proj2
lake build BSD.Stage2.RankTwoExclusion     # 骨架编译
lake env lean BSD/Stage2/_check_stage2.lean # #print axioms 核验
```

统计：库 axiom 新增 13（Stage2 独立层）；sorry = 0。

实际闭包核验（`_check_stage2.lean`，2026-10-07 落盘）：

| 定理 | axiom 闭包 | 说明 |
|---|---|---|
| `analyticRankK_ne_two`（直接版） | propext, Quot.sound + `analyticZeroOrder`, `parity_neg_one`, `rootNumberK`, `rootNumberK_eq_neg_one` | 依赖 epsilon(K) = -1 |
| `analyticRankK_ne_two'`（型筛版） | propext, Quot.sound + 12 声明（E/E5 奇偶 + 加性，**不含 rootNumberK**） | 纯结构，epsilon(K) axiom 冗余 |
| `parityK_propagated` | 同上 12 声明 | 奇偶传播，结构性证明 |
| `zeroOrderE5_eq_zero`（数值） | 桥 axiom + LSeries5 声明层（`L_E5_series_split`, `Lambda_E5`）+ native_decide 计算信任（~60 条） | 独立路径，不含任何奇偶 axiom |

## 7. 边界与后续

- 本骨架锁死的是 **E = 37a1 侧**（epsilon(E) = -1）。换 epsilon(E) = +1 的秩 2 曲线（如 389a1）后，(2,0) 型复活——Stage 2 的约束是"本例特化"。
- 无 mod 4 约束：Q(√5) 不产生零点阶 mod 4 的理论强制；ord >= 3（epsilon = -1 允许 1,3,5,...）仍只能靠数值区间排除（Stage 1 的 L_K′(1) > 0 已排除 >= 2）。
- 后续可选：把 `parity_neg_one`/`parity_pos_one` 的实例化下沉为"函数方程"公理的可证引理（自守 L 层）；把型筛论证并入 Main.lean 的 `analytic_rank_K_eq_one_of_LK_prime_ne_zero` 注释。
