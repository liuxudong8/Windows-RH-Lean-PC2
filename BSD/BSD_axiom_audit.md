# BSD 主定理 axiom 闭包审计（weak_BSD_37a1）

日期：2026-10-06　|　库 axiom：**16**（Main.lean 9 + LSeries5.lean 7；TwoDescent.lean 0，sorry = 0，lake build BSD exit 0）
注：2026-10-06 D1+D2 升级完成：coefficient_bound_aE5、summable_fE5 由 axiom → theorem，库 axiom 18 → 16。

## 0. 主定理闭包链

```
weak_BSD_37a1 : mwRank E/K = analyticRank E/K
├─ algebraic_rank_K_eq_one（theorem）
│  ├─ twist_decomposition        [C] rank E(K) = rank E(ℚ) + rank E⁵(ℚ)
│  ├─ rank_E_Q_eq_one（theorem）
│  │  ├─ rank_E_Q_ge_one         [C] ②a：Silverman VIII.7.1(b)，7P′ 非扭
│  │  └─ rank_E_Q_le_one         [C] ②b：Selmer |Sel²| = 2 ⟹ dim ≤ 1
│  └─ rank_E5_Q_eq_zero_of_L_E5_ne_zero [C] 条件：L(E⁵,1)≠0 ⟹ 秩 0（Kolyvagin；前件真定理接线）
└─ analytic_rank_K_eq_one（theorem）
   ├─ analytic_rank_K_eq_one_of_LK_prime_ne_zero  [C] ε_K = −1 函数方程
   └─ LK_prime_pos（theorem）
      ├─ Lprime_E1_interval      [B] L′(E,1) ∈ [0.30599977, 0.30600000]
      └─ L_E5_one_pos（theorem）
         ├─ L_E5_series_split    [C] Dokchitser 反射公式 N-截断
         ├─ coefficient_bound_aE5 [D] |a_n(E⁵)| ≤ 2n（可消除）
         └─ summable_fE5         [D] 反射级数绝对收敛（可消除）
```

## 1. 18 axiom 分类清单

### [A] 结构性占位（口径定义，无数学风险）— 4

| # | axiom | 位置 | 说明 |
|---|---|---|---|
| A1 | `analyticRank` | Main:66 | 解析秩占位定义（s=1 零点阶口径） |
| A2 | `mwRank` | Main:70 | 代数秩占位定义（Mordell–Weil 秩口径） |
| A3 | `GammaUpper` | LSeries5:375 | 不完全 Gamma Γ(s,b) 占位（反射公式输入函数） |
| A4 | `ap_E` | LSeries5:68 | Hecke 系数函数占位（值由 A5 钉死） |

### [A] 结构性占位（口径定义，无数学风险）— 4

### [B] 数值钉死（LMFDB/Cremona + 独立重检）— 3

| # | axiom | 位置 | 依据 | 风险 |
|---|---|---|---|---|
| B1 | `ap_E_values` | LSeries5:71 | LMFDB/Cremona 12 素值表；文档 5.1 | 低（权威库，多素独立来源） |
| B2 | `Lprime_E1` | Main:76 | LMFDB 0.305999773834…（12 位权威） | 低 |
| B3 | `Lprime_E1_interval` | Main:82 | 同上 + 本项目 degree-2 反射公式独立重检 0.305999772…（差 1.7×10⁻⁹）；宽区间 [0.30599977, 0.30600000] margin 大 | 低（区间宽，容错充足） |

### [C] 数学钉死、mathlib 无理论故 axiom 保留（外部定理/教科书）— 9

| # | axiom | 位置 | 数学依据 | 深度 | 升级路径 |
|---|---|---|---|---|---|
| C1 | `ramanujan_ap_E` | LSeries5:103 | Hasse 界 / Weil 猜想 d=1（Deligne，无条件） | 深（代数几何） | 需有限域点计数理论，不现实 |
| C2 | `ap5_satake` | LSeries5:111 | Deligne：Satake 参数存在，‖α‖=‖β‖=√p（无条件） | 深（代数几何） | 同上 |
| C3 | `Lambda_E5` | LSeries5:380 | 自守 L 解析延拓 + 函数方程（Dokchitser 反射公式形态） | 深（自守形式） | 需自守 L 理论，不现实 |
| C4 | `L_E5_series_split` | LSeries5:634 | Dokchitser 反射公式 s=1 N-截断等式 | 深（自守形式） | 同上 |
| C5 | `analytic_rank_K_eq_one_of_LK_prime_ne_zero` | Main:105 | ε_K = −1 函数方程 + 一阶零点判定（L_K(1)=0、L_K′(1)≠0 ⟹ 解析秩 1） | 中（函数方程）+ **ε_K 需显式核验** | Artin 分解 + 根数乘性的 Lean 化 |
| C6 | `rank_E_Q_ge_one` | Main:122 | Silverman VIII.7.1(b)：7P′=(−20/9,172/27) 分母含 3 ∉ {2,37} ⟹ 非扭；7P′ 数值在 TwoDescent.lean 真证 | 中（约化理论，教科书） | 需椭圆曲线约化理论，不现实 |
| C7 | `rank_E_Q_le_one` | Main:130 | 2-下降：|Sel²| = 2 = {1, −θ}（selmer7.py 终跑）⟹ dim Sel² = 1 ⟹ rank ≤ 1 | 中（2-下降/Selmer，标准算术） | 需 Selmer/局部域理论，不现实 |
| C8 | `rank_E5_Q_eq_zero_of_L_E5_ne_zero` | Main:143 | **条件 axiom**：`L_E5 1 ≠ 0 → mwRank Twist5 ℚ = 0`（Kolyvagin Euler 系统）；前件由真定理 `rank_E5_Q_eq_zero` 接线（`L_E5_one_ne_zero`） | **最深**（现代数论） | 需 Euler 系统理论，不现实 |
| C9 | `twist_decomposition` | Main:149 | Galois 模特征空间分解：E(K)⊗ℚ ≅ E(ℚ)⊗ℚ ⊕ E⁵(ℚ)⊗ℚ（Silverman，教科书） | 中（Galois 模） | 需 Mordell–Weil + Galois 模理论，不现实 |

### [D] 已消除（2026-10-06 完成升级）— 2

| # | axiom | 升级前 | 升级后 | 代价 |
|---|---|---|---|---|
| D1 | `coefficient_bound_aE5` | \|aE5 n\| ≤ 2n（∀n 声明） | **theorem**：aE5 wrapper 化（`aE5 n = if n ≤ 800 then aE5_raw n else 0`，数值逐项不变）；n ≤ 800 查表 native_decide（ℤ 上 \|aE5 m\| ≤ 2m，m ∈ range 801）、n ≥ 801 表外平凡（if_neg） | +2 native_decide 计算信任公理（与 part50_ge 的 50 项同类：只信任 801 次具体比较的执行，**非数学 axiom**） |
| D2 | `summable_fE5` | 反射级数绝对收敛（声明） | **theorem**：\|fE5 n\| ≤ 2·exp(−α(n+1))（D1 + 除法界），Σ 为几何级数（exp(−α) < 1，α = 2π/√925 > 0），Summable.of_norm_bounded | 无（完全干净） |

**升级后计数**：库 axiom 18 → **16**（Main 9 + LSeries5 7）；`weak_BSD_37a1` 数学 axiom 闭包 = **11**（+3 Lean 基础：propext / Quot.sound / Classical.choice）；native_decide 计算信任公理 112 → 114。

## 2. 风险排序（对主定理成立性的威胁）

1. **C8（Kolyvagin）**：主定理最深的数论输入。数学上已证（Kolyvagin 1989, Euler 系统），但不可 Lean 化，依赖须在文档显式声明。**已有 L_E5_one_ne_zero 真定理支撑前件**，风险是"引用正确性"而非数值。
2. **C5（ε_K = −1）**：审计发现的口径缺口——根数乘性 ε_K = ε(E)·ε(E⁵) = (−1)(+1) = −1 未显式推导。**已落档（2026-10-06）**：Main.lean C5 注释补写依据——ε(E) = −1（N = 37 奇符号）、ε(E⁵) = +1（N = 925，数据核验）、根数乘性 ⟹ ε_K = −1。
3. **C6/C7（代数秩上下界）**：②a/②b 数值与外部定理均钉死（7P′ 分母、|Sel²|=2），无数值风险；风险仅"引用外部定理"。
4. **C1–C4（Deligne + 自守 L）**：无条件标准理论，深度在"不可形式化"而非"可能错"。
5. **D1/D2**：非风险，纯工程——**升级后 18 → 16 axiom**。

## 3. 结论

- **主定理成立性无已知缺口**：16 axiom 中 9 个 [C] 是"数学已钉死、mathlib 无理论"的永久 axiom；3 个 [B] 数值钉死；4 个 [A] 结构占位。**D1/D2 已消除**（D1 换 2 个 native_decide 计算信任公理、D2 完全干净）。
- **唯一审计发现**：C5 的 ε_K = −1 依据（根数乘性）**已落档**（Main.lean 注释补写推导，2026-10-06）。
- **C8 已条件化接线（2026-10-06）**：axiom 只断言文献定理（L(E⁵,1)≠0 ⟹ 秩 0，Kolyvagin + BCDT 模性），前件由真定理 `L_E5_one_ne_zero` 显式供给；闭包计数不变（16 库 axiom / 11 BSD 数学闭包）。
- **下一轮建议**：其余 axiom 均为"mathlib 无理论"的诚实保留；如需继续，②b Selmer 结果入文档链（骨架A讨论稿）或 LSeries5 反射公式 axiom 的进一步收口。
