# Probe 389a1 — 秩 2 最小导子曲线的特化边界（恶化曲线 · 第一点）

日期：2026-10-08（数值管线修复并闭合）
位置：`C:\proj2\BSD\Probe389\`
状态：**数值管线闭合 + Lean 骨架落盘编译通过**

---

## 0. 一句话结论

389a1（ε = +1，analytic rank 2，N = 389，唯一 5 百万内非扭 2 秩曲线族首条）实测 Stage2 奇偶型筛的特化边界：
**ε 翻号 ⟹ 奇偶引擎熄火**——(1,1) 仍被奇偶排除，但 (0,2)/(2,0) 复活；Kolyvagin 秩 2 空缺显现（bound=(0,0)）。
恶化曲线第一点量出：**尾收敛 3.24× 变慢（e^{−1.033n} → e^{−0.319n}），主项量级 ×5（L′ ~ 0.31 → L″ ~ 1.52），排除手段从"免费奇偶"退化为"真数据 + 工具空缺"**。

---

## 1. 数值管线（本轮修复并闭合）

### 1.1 关键修复：数点漏无穷远点

官方 Cremona aplist（`aplist.00000-09999`，`37 a` 行）证实：
`a₂(37a1) = −2, a₃ = −3`——而我的旧数点给 −1/−2。根因：

```
a_p = p + 1 − #E(F_p)          #E(F_p) 含无穷远点
    = p + 1 − (N_affine + 1)   N_affine = 仿射点数（我的数点）
    = p − N_affine              ← 正确公式
```

修复后 389a1 前 20 项 `[1,-2,-2,2,-3,4,-5,0,1,6,-4,-4,-3,10,6,-4,-6,-2,5,-6]`
与官方 anlist 完全一致；**Fricke 自洽 f(i/N) = −ε·N·f(i) 通过（389a1 比值 1.0000）**。

### 1.2 收敛级数管线（Mellin 分裂 + 上半不完全 Γ）

```
F(s) = S1(s) + N^{1−s}(2π)^{2s−2}/Γ(s) · S2′(s)/epsL
S1  = Σ a_n n^{−s} Γ(s, b_n)/Γ(s),   S2′ = Σ a_n n^{s−2} Γ(2−s, b_n),   b_n = 2πn/√N
```
（第二项除以根数 epsL 而非常数 eps——前期修复；Γ 上不完全函数最优截断——前期修复）

### 1.3 最终数值（Q=3000，h→0 扫描）

| 量 | 独立管线实测 | 文献权威值（Sage Dokchitser） | 吻合 |
|---|---|---|---|
| L″(389a1, 1) | 1.5185 → 1.5187（h→0） | **1.51863300057685** | ~0.01% |
| L′(37a1, 1) | 0.305986（h=0.01） | **0.305999773834052** | ~0.004% |
| L(389a1, 1) | 1.37e−9 ≈ 0 | 0（rank 2） | ✓ |

## 2. 数据源与交叉验证链

| 事实 | 来源 | 状态 |
|---|---|---|
| 389a1 = [0,1,1,−2,0]，N=389，|T|=1，生成元 (0,0),(1,0) | Cremona Table 2 / LMFDB | 已核 |
| analytic rank = 2（pari/rubinstein/sympow/magma/zero_sum 五算法） | Sage ell_rational_field 文档 | 已核 |
| ε(E)=+1、坏素 a₃₈₉=+1（split mult） | LMFDB / 本地 a_p | 已核 |
| ε(E⁵)=+1：χ₅(389) = (389 mod 5 = 4) = +1，gcd(389,5)=1 无局部修正 | 局部根数计算 | 已核 |
| ε(E/K) = ε(E)·ε(E⁵) = +1（K=Q(√5)） | 乘积规则 | 已核 |
| Kolyvagin bound = **(0,0)**（秩 2 无欧拉系支撑） | Sage sha_tate 文档 | 已核 |
| Heegner 点数值 0（秩 2 无 Heegner 支撑） | Sage heegner 文档 | 已核 |
| 秩 2 最小导子 = 389（Buhler–Gross–Zagier 经典） | LMFDB / 文献 | 已核 |

## 3. 恶化曲线 · 第一数据点（Lean 骨架记录）

```
                   37a1（秩 1，ε=−1）          389a1（秩 2，ε=+1）
尾收敛系数 b = 2π/√N     1.032949                  0.318570        （慢 3.24×）
主项                       L′(1) ≈ 0.306             L″(1) ≈ 1.519  （×5）
L(1) 行为                   ε=−1 强制 L(1)=0          实测 ~1e−9 ≈ 0
奇偶筛                     三型全灭（免费）            (1,1) 灭；(0,2)/(2,0) 复活
Kolyvagin                  rank-1 欧拉系可用         bound = (0,0) —— 工具空缺
排除总代价                  零数值输入                  真数据（L″≠0）+ 工具空缺
```

**机制诊断**：奇偶筛的电源是"存在一个 ε = −1"。秩 2 ⟹ 根数 +1 ⟹ 全偶 ⟹ 奇偶筛退化为只杀 (1,1)。这不是算术障碍而是**机制失效**：**"为何不是 2"在 ε=+1 处不可由奇偶免费回答**。

**Kolyvagin 空缺的定位**：bound=(0,0) 不是矛盾（389a1 的秩 2 本身被五算法与 L″(1) 判定），而是**一般机器的空缺**：秩 2 无统一判定工具（Heegner 点/欧拉系都是秩 1 工具）。这正是"复杂性阈值"的第一手证据——**阈值不在"判定不可能"（字面 false：秩 29 可判定），而在"统一机制失效"**（H¹⁰(𝒪_K) 不可判定已由 Koymans–Pagano 2024 / Shlapentokh–Vasquez–Vogt 2025 证明；PPVW 2021 启发式给开放秩有界）。

## 4. Lean 骨架（Probe389.lean）

模块 `BSD.Probe389.Probe389`，**编译 exit 0**（`lake build BSD.Probe389.Probe389`，832 jobs），
闭包核验 `_check_probe389.lean` 通过（探针定理仅依赖探针 axiom + propext，无 Stage2/Main 泄漏）。

- **axiom 层（14 个）**：rootNumberE389/E3895/K389 及其 =1 实例；zeroOrderE389/E3895/analyticZeroOrder389；
  parity_neg_one/parity_pos_one（与 Stage2 同形状）；zeroOrder_additivity389（Artin 分解）；
  **analyticRankE389_eq_two**（数据：LMFDB/Sage 五算法 + 独立 L″(1) 数值）；
  LDoublePrime389 + LDoublePrime389_nonzero（数值锚点 1.518633）；
  KolyvaginBound389 + kolyvaginBound389_eq_zero（秩 2 空缺锚点）。
- **真证定理层（12 个）**：
  - `evenE389 / evenE3895 / evenK389`：ε=+1 ⟹ 全偶（Stage2 的 odd 对应版）；
  - `parityK389_propagated`：偶+偶=偶经加性传播（不需 ε(K) axiom）；
  - `rootNumberK389_from_product`：ε(E/K) = ε(E)·ε(E⁵) = +1；
  - `no_type11_probe`：(1,1) 仍被奇偶排除；
  - `type20_parity_compatible / type02_parity_compatible`：**(2,0)/(0,2) 奇偶兼容（复活演示，显式 witness）**；
  - `rank_two_decomposition389`：additivity + rank=2 ⟹ 三型；
  - `rankTwo_survivors_after_parity`：型筛后幸存 (0,2)/(2,0)；
  - `parity_sieve_fails_for_epsilon_plus_one`：ε=+1 下奇偶筛**不能**给出"秩 ≠ 2"；
  - `rank2_parity_compatible`：秩 2 与全部奇偶约束相容。

**与 Stage2 的对照**（骨架注释已写明）：37a1/K 秩 2 三路奇偶排除（免费）；389a1/K 秩 2 复活（真数据）。
用户上轮要求的"型筛论证并入 Main.lean"已完成（(iii) 段，`analytic_rank_K_eq_one_of_LK_prime_ne_zero` docstring）。

## 5. 文件清单

| 文件 | 内容 |
|---|---|
| `Probe389.lean` | Lean 骨架（14 axiom + 12 真证定理） |
| `_check_probe389.lean` | 闭包核验（#check + #print axioms） |
| `probe389_numeric.py` | 数值主管线（含本轮 a_p 修复） |
| `quick_test.py`–`quick_test4.py`, `diag1–3.py`, `debug_gamma.py` | 公式/Γ/ε 符号/Fricke 交叉验证脚本 |
| `probe389_summary.md` | 本文档 |

## 6. 未决项与下一步

- **未决（小）**：37a1 的 Fricke 比值 0.946（非精确 1）——不影响主结论（L′ 已 0.004% 吻合），来源待查（疑 ε 在 37 处或 a_{37^k} 组装的次级残差）。
- **建议下一探针（恶化曲线第二点）**：N=5077a1（秩 3，ε=−1，Buhler–Gross–Zagier 经典）——**秩 3 回到 ε=−1**，奇偶筛再次免费灭 (0,3)/(1,2)/(2,1)/(3,0) 中的哪些型？这将区分"恶化由秩驱动"还是"由 ε 驱动"。Koymans–Pagano 秩稳定曲线的构造起点正在 5077a1 附近，可直接接入 H¹⁰(𝒪_K) 不可判定讨论。
- **Lean 升级路径**：parity_neg_one/parity_pos_one/zeroOrder_additivity 的首消目标；LDoublePrime389 → Dokchitser 算法真实现。
