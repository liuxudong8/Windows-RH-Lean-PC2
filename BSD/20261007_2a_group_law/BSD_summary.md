# BSD 库——弱 BSD 秩 1 的 Lean 形式化（状态摘要）

> 更新：2026-10-07 ②a 首轮真证化（Silverman VIII.7.1 触发层 + 群法则）——`Eprime_double`/`Eprime_add` 曲线保持真证（切点加倍/割线加法，因式分解+双方程代入）、2P′..7P′ 链 `P2_eq_double`..`P7_eq_add` 全部由加法公式计算、`P7_X_den_nonbad_factor`（7P′ 分母含素因子 3 ∉ {2,37}）；闭包仅 propext/choice/Quot。编译基线：`lake build BSD` exit 0（3316 jobs）；sorry = 0；库数学 axiom = 14（Main 7 + LSeries5 7，不变）；`rank_E_Q_ge_one` 注释更新（②a 已真证其全部输入，Silverman 定理本身维持外部 axiom）。

## 0. 一句话定位

把《骨架 A 讨论稿》（K = ℚ(√5)，E = 37a1）的"代数秩 = 解析秩 = 1"判定做成 Lean 三层骨架：**对象层真可证，数论/分析深层走声明层（axiom 带待证明注释），拼合层定理成立**。任何 axiom 都有明确的可升级路径，无死路。

## 1. 数学口径（与文档对应）

| 对象 | 口径 | 文档 |
|---|---|---|
| 主曲线 | E = 37a1：y² + y = x³ − x，Δ = −37，N = 37 | 2.1 |
| 域 | K = ℚ(√5)，N_K = 1369，ε_K = −1 | 2.1 |
| 二次扭 | E⁵：Y² = x³ − 25x + 125/4，N(E⁵) = 925，ε(E⁵) = +1 | 5.4(iv) |
| 解析秩(E/K) | = 1：L_K(1) = 0（ε_K = −1）+ L_K′(1) = 1.63858644 = L′(E,1)·L(E⁵,1) ≥ 1.63808 ⊂ (0,∞)（乘积恒等式形态；旧口径 degree-2 反射公式主值 2.433224 弃用） | 4.3, 5.4(iii) |
| 代数秩(E/K) | = 1：rank E(ℚ) = 1 + rank E⁵(ℚ) = 0（二次扭分解） | 2.1, 5.4(iv) |
| E⁵ 解析判定 | L(E⁵,1) ∈ [5.3548616166 ± 1.7×10⁻⁷¹] ⊂ (0,∞)，N = 800，dps = 80 | 5.4(iv) |

E⁵ 局部因子：好素 p∤925 取 a_p = χ₅(p)·a_p(E)（χ₅: mod5 {1,4}→+1, {2,3}→−1）；p=5 加性 a=0；p=37 乘性 a=+1（s=3 闭合比 0.99999967 确定符号与 ε）。

## 2. 文件结构

```
c:\proj2\
├── BSD.lean                 # 库根：import BSD.Main（lake lean_lib 根模块约定）
├── BSD\
│   ├── Main.lean            # 主体：对象层 + 声明层 + 定理层（import BSD.LSeries5）
│   ├── LSeries5.lean        # ① E⁵ 局部因子 + L(1) 反射公式（几何级数尾已闭合）
│   ├── LPrime.lean          # L′(E,1) 级数形态 + 正性（B3-min + ①c，数学 axiom 清零）
│   ├── TwoDescent.lean      # ② E′ 整模型 + 无限阶数值层 + 2-下降骨架（②b 首轮真证层）
│   ├── BSD_summary.md       # 本文件
│   ├── _check_bsd.lean      # #print axioms 核验（weak_BSD_37a1 等）
│   ├── _check_ls5.lean      # #print axioms 核验（LSeries5 各层）
│   ├── _check_1a.lean       # #print axioms 核验（geom_tail_bound 闭合）
│   ├── _check_summable.lean # ①c 复刻探针（lprime1_summable 证明体）
│   ├── _check_2b.lean       # ②b 探针（Eprime_poly_no_root 证明体）
│   ├── _check_2b_ax.lean    # ②b 闭包核验（Eprime_two_torsion_trivial 纯基础）
│   ├── _check_2a.lean       # ②a 探针（Eprime_double/add + 7 倍链证明体）
│   └── _check_2a_ax.lean    # ②a 闭包核验（P7_eq_add/P7_X_den_nonbad_factor 纯基础）
└── lakefile.toml            # [[lean_lib]] name = "BSD"（无 root 字段！）
```

> 陷阱记录：lakefile.toml 的 lean_lib **不支持 root 字段**（那是 lakefile.lean 的）；根模块文件必须是项目根同名 `BSD.lean`（内容仅 import BSD.Main）。`Mathlib.Data.Rat.Basic` 在 4.34 不存在 → 用 `Defs`。`Real.gamma` 是 `Real.Gamma`（大写）。

## 3. 分层与统计

### 3.1 对象层（真 Lean 证明，axiom 闭包干净）

**Main.lean**：`Curve37a1`（Weierstrass 方程）、`Twist5`、`P0 : Point Curve37a1` 且 P0 = (0,0) `by norm_num` 在曲线上。

**LSeries5.lean**（局部因子代数层，7 条已证定理）：
- `chi5` 定义 + `chi5_zero_at_5 / chi5_neg_at_2 / chi5_pos_at_11`
- `ap5` 定义 + `ap5_additive_at_5`（=0）/ `ap5_multiplicative_at_37`（=+1）/ `ap5_sample_2`（=2）/ `ap5_sample_11`（=−5）

**LSeries5.lean**（分析不等式，完整闭合）：
- `tsum_geom_shift`：Σ r^(m+n) = r^m/(1−r)，|r|<1（hasSum_geometric_of_norm_lt_one + mul_left + pow_add + tsum_eq）
- `geom_tail_bound`：Σ e^(−α(N+1+n)) = e^(−α(N+1))/(1−e^(−α))，0<α（r=e^(−α)，exp_lt_one_iff + Real.exp_nat_mul）
- **二者 axiom 闭包 = [propext, Classical.choice, Quot.sound]——纯基础公理**

**LSeries5.lean**（5.4(iv-c) 初等不等式链，全部由 axiom 升级为 theorem）：
- `alpha_gt_2065`：α = 2π/√925 > 0.2065（Real.pi_gt_d4 + Real.sqrt_lt' + lt_div_iff₀）——闭包 = 3 基础公理
- `exp_neg_alpha_lt_8136`：e^(−α) < 0.8136（exp 单调 + Real.exp_bound n=5 部分和下界 + 倒数单调）——闭包 = 3 基础公理
- `exp_neg_alpha_801_lt`：e^(−α·801) < 10⁻⁶⁰（exp_nat_mul 幂 + pow_le_pow_left₀ + ℚ 精确判定）——闭包 = 3 基础 + **native_decide 计算信任公理**（见下注）
- `tail_ivc_bound`：4·e^(−α·801)/(1−e^(−α)) < 10⁻⁵⁸（1−e^(−α) > 0.1864 + mul_le_mul + norm_num）
- `tail_sufficient_pos`：(iv-d) 充分条件 5 − 尾界 > 0（tail_ivc_bound + sub_pos）

> **native_decide 计算信任公理（透明声明）**：801 次幂的 ℚ 判定（(1017/1250)^801 < 10⁻⁶⁰，即 1017^801·10⁶⁰ < 1250^801，约 2500 位 bignum）由 `native_decide` 完成，生成 `exp_neg_alpha_801_lt._native.native_decide.ax_1_1`。这是 Lean 将 bignum 比较委托给已验证 native 编译通道的**计算信任公理**，非数学假设（`decide` 因 kernel 不归约 `Rat.blt` 而失败；`norm_num` 不计算大幂）。可独立复核：1017^801·10⁶⁰ < 1250^801。若需完全 kernel 核验，可改为"阶乘余项链"（exp(−165.4) < 1/10⁶⁰ 的 90! 级数余项上界），留作后续升级。

**LSeries5.lean（5.4(iv-d) 部分和下界块，本窗口落盘）**——`part50_ge : 2.6766 ≤ Σ_{n<50} fE5 n` 已证（N = 50，阈 2.6766，2·LB = 5.35321 > 0，①c 半边闭合）：
- `alpha_lt_2066`：α < 0.2066（Real.lt_sqrt + pi_lt_d4）——闭包 = 3 基础公理
- `exp_neg_alpha_gt_8133`：e^(−α) > 0.8133（Real.exp_bound n=6 上界 + 倒数单调 + exp_neg）——闭包 = 3 基础公理
- `alphaE5` / `fE5`：α 与第 n 项定义（fE5 n = a_{n+1}/(n+1)·e^(−α(n+1))）
- `powE_any` / `powE'_any`：0.8133^n ≤ e^(−αn)（正项）/ e^(−αn) ≤ 0.8136^n（负项，指数形态 rw 闭合）
- 50 条 `term_k`：粗界项 ≤ fE5 项（正/负/零三分支；零分支 `native_decide` 判定 aE5 k = 0）
- `crude50_ge_R`：2.6766 ≤ 50 项粗界（10 分块 ℚ `native_decide` + cast 桥 + nlinarith）——含 native_decide 计算信任公理
- `part50_ge_crude` / `part50_ge`：Σ_{n<50} fE5 ≥ 粗界 ≥ 2.6766（sum_range_succ 展开 + term_k 逐项 + linarith）——闭包 = 3 基础 + term_k/crude50 的 native_decide 计算信任公理，**无数学 axiom**
- 声明层 3 个（见 §3.2）：`L_E5_series_split`、`coefficient_bound_aE5`、`summable_fE5`

**LSeries5.lean（①b 乘性组装，本窗口落盘）**——`axiom coefficient_bound` 已删，改为定理形态（素因子分解组装 τ(n)√n 界）：
- `ppow_0 / ppow_1 / ppow_rec`：素幂系数 a_{p^k} 的递推定义（a_{p^0}=1, a_{p^1}=a_p, a_{p^{k+1}}=a_p·a_{p^k} − p·a_{p^{k−1}}）
- `ap5_satake`（axiom，见 §3.2）：\|\|α\|=\|\|β\|=√p（Deligne/Satake，模性来源）
- `ssum` + `ssum_rec`：幂和 s_k = Σ_{j=0}^k α^{k−j}β^j（Nat.twoStepInduction case zero|one|more）+ Newton 恒等式桥（a_{p^k} = s_k）
- `ppow_eq_ssum`：a_{p^k} = s_k（两条递推同一性，Nat.twoStepInduction）
- `ssum_abs_bound`：\|s_k\| ≤ (k+1)√p^k（三角 + ‖α‖=‖β‖=√p + 幂和项数）
- `ppow_bound`：\|a_{p^k}\| ≤ (k+1)p^{k/2} = (k+1)(√p)^k（ssum_abs_bound + ppow_eq_ssum）
- `prod_le_prod_nonneg` / `abs_prod_int`（\|∏z_i\|=∏\|z_i\|，induction + abs_mul）/ `sqrt_pow_eq` / `sqrt_prod_eq` / `prod_primeFactors_pow_eq`（n = ∏ p^{k_p}，Nat.prod_factorization_pow_eq_self）
- `coefficient_bound_assembled`：\|∏ a_{p^{k_p}}\| ≤ τ(n)·√n（abs_prod_int + prod_le_prod_nonneg + ppow_bound 逐项 + card_divisors + sqrt 组装）
- `coefficient_bound`（新定理形态，同名）：上述 τ(n)√n 界——**闭包 = 3 基础公理 + ap5_satake（声明层）**

### 3.2 声明层（axiom，每个带"待证明"注释与升级路径）

**Main.lean — 7 个**（`analytic_rank_K_eq_one`、`rank_E_Q_eq_one` 已升级为定理；`Lprime_E1` / `Lprime_E1_interval` 已 B3-min 删除，见 §3.3）：

| axiom | 含义 | 升级路径 |
|---|---|---|
| `analyticRank` | 解析秩（函数定义，mathlib 无自守 L） | 自建 L 函数层（LSeries5 方向） |
| `mwRank` | Mordell–Weil 秩（mathlib 无椭圆曲线理论） | 需要全套算术几何 |
| `analytic_rank_K_eq_one_of_LK_prime_ne_zero` | L_K′(1) ≠ 0 ⟹ 解析秩(E/K) = 1（L_K(1) = 0 的函数方程 ε_K = −1 + 解析秩定义） | 函数方程与 Artin 分解的 Lean 实现 |
| `rank_E_Q_ge_one` | rank E(ℚ) ≥ 1（P₀ = (0,0) 无限阶；②a 已真证全部输入） | Silverman VIII.7.1(b) 本体（椭圆曲线约化理论，mathlib 缺失） |
| `rank_E_Q_le_one` | rank E(ℚ) ≤ 1（2-下降 Selmer 计算；E′[2] = {O} 已真证，见 §3.3 ②b） | 三次域类数/单位群/局部可解性（②b 剩余） |
| `rank_E5_Q_eq_zero` | rank E⁵(ℚ)=0（Kolyvagin） | L_E5_one_ne_zero（已闭合）+ Kolyvagin 定理 |
| `twist_decomposition` | rank E(K) = rank E(ℚ) + rank E⁵(ℚ)（Silverman） | Galois 模特征空间分解（③） |

**LSeries5.lean — 9 个**（`L_E5_one_ne_zero` 已降级为定理，见 §3.1）：

| axiom | 含义 | 升级路径 |
|---|---|---|
| `ap_E` | a_p(E)（点计数） | 有限域点计数（数学上可行，工程量大） |
| `ap_E_values` | 抽样值表（a₂=−2, …, a₅₉=8） | 由 ap_E 点计数计算推出 |
| `ramanujan_ap_E` | \|a_p(E)\| ≤ 2√p（Deligne） | 不可 Lean（Weil 猜想级）——永久 axiom 风险 |
| `ap5_satake` | \|\|α\|=\|\|β\|=√p（E⁵ 在 p 处 Frobenius 特征值，Deligne） | 不可 Lean（Weil 猜想级）——永久 axiom 风险；供 ppow_bound 用 |
| `GammaUpper` | 不完全 Gamma Γ(s,b) | mathlib 无；可加积分定义（大工程） |
| `Lambda_E5` | Dokchitser 反射公式（N=925, ε=+1） | 自守 L 理论——不可 Lean（永久 axiom 风险） |
| `L_E5_series_split` | L_E5 1 = 2·(Σ_{n<N} fE5 n) + 2·∑'_{n≥N} fE5(n+N)（反射公式截断拆分） | ①c 尾界拼接定理（N=50 起点） |
| `coefficient_bound_aE5` | \|aE5 n\| ≤ 2n（表口径，1≤n≤50 块判定已过） | 由 coefficient_bound + 素幂递推 |
| `summable_fE5` | fE5 可和（尾的几何级数控制） | ①a geom_tail_bound + 绝对可和 |

### 3.3 定理层（拼合）

- `LK_prime_pos`：L_K′(1) > 0（真定理；axiom 闭包 = `Lprime_E1_pos` 定理（B3-min 已收口）+ `L_E5_one_pos` 定理 + LSeries5 声明层 + 基础；`lprime1_summable` 已 ①c 定理化；数值下界 1.63808 = 0.30599977 × 5.3532）
- `analytic_rank_K_eq_one`：解析秩(E/K) = 1（**由 axiom 升级为 theorem**：`analytic_rank_K_eq_one_of_LK_prime_ne_zero`（声明）+ `LK_prime_pos`）
- `algebraic_rank_K_eq_one`：mwRank E(K) = 1（rw 拼合，axiom 闭包 = 声明 + 基础）
- `rank_E_Q_eq_one`：rank E(ℚ) = 1（**由 axiom 升级为 theorem**：`le_antisymm rank_E_Q_le_one rank_E_Q_ge_one`，② 结构化拼合）
- `analytic_rank_K_eq_one'`：解析秩 = 1（rw 引用 `analytic_rank_K_eq_one`）
- `weak_BSD_37a1`：mwRank = analyticRank（弱 BSD 秩 1 成立）
- 均无 sorry；`weak_BSD_37a1` 的 `#print axioms` 闭包见下注

> **B3-min 收口（2026-10-07）**：`Lprime_E1` / `Lprime_E1_interval` 两个裸数值 axiom（LMFDB 0.305999773834…）已整体删除，替换为公式形态真定理链：
> `LPrime.lprime1 = 2·∑' aE(n+1)/(n+1)·E1(2π(n+1)/√37)`（E = 37a1 反射公式一阶导级数形态，N=37, ε=−1）→ `LPrime.lprime1_pos : 0 < lprime1`（部分和 ≥ 0.0557 vs 尾项 |·| ≤ 0.0125，margin 充分）→ `Main.Lprime_E1_pos`。
> `LPrime.lean` 4.5–4.11 块全部闭合（`lake env lean BSD/LPrime.lean` exit 0）；`lake build BSD` exit 0。
> **①c 复刻收口（2026-10-07）**：`lprime1_summable` axiom → theorem（级数绝对收敛，几何级数闭合）。证明体：逐项界 `|aE(n+1)/(n+1)·E1(bn(n+1))| ≤ (2/1.03)·e^{−1.03(n+1)}`——`aE_bound`（n≤100 分支 + 表外 0）+ `E1_le`（E₁ ≤ e^{−b}/b）+ `b1_gt_103`（bₙ ≥ 1.03n ⟹ bn ≥ 1.03、e^{−bn} ≤ e^{−1.03n}）组合，右侧几何级数可和（`hasSum_geometric_of_norm_lt_one` + `pow_succ` 移位 + `exp_nat_mul`），`Summable.of_norm_bounded` 闭合。
> `#print axioms LK_prime_pos` 复核：**无 `lprime1_summable`**；数学 axiom 仅剩 LSeries5 声明层（`L_E5_series_split`、`Lambda_E5`）+ 基础（propext/choice/Quot）+ native_decide 计算信任公理（aE_bound 表）。LPrime.lean 数学 axiom 清零。
> 4.11 形态教训（勿再踩）：`mul_le_mul_of_nonneg_left` 生成 c·a ≤ c·b（左乘），右乘需 `_right`；`Real.exp_le_exp` 现代版 iff 无参；`norm_tsum_le_tsum_norm` 需 `Summable ‖·‖`（用 convert + `Real.norm_eq_abs` 从 `Summable |·|` 构造，勿 simpa 直转——abs_div/abs_mul 归约不对称）；ℕ/ℝ cast 形态（`↑(n+4)` vs `↑(n+3)+1`）非 DefEq，用显式形态等式 `g_sum_eq1/g_sum_eq2/g_sum_abs` + rw 转换（`congr 1` 只留未自动闭合的分母目标；分母 `rw [Nat.cast_add]; ring` 或直接 `ring`）。

> 注：`weak_BSD_37a1` 的 axiom 闭包（`lake env lean BSD/_check_bsd.lean`）现为：`analytic_rank_K_eq_one_of_LK_prime_ne_zero`（Main 声明）+ `analyticRank`、`mwRank`、`rank_E_Q_ge_one`、`rank_E_Q_le_one`、`rank_E5_Q_eq_zero`、`twist_decomposition` + LSeries5 声明层（`Lambda_E5`、`L_E5_series_split`、`coefficient_bound_aE5`、`summable_fE5` 等）+ native_decide 计算信任公理 + 基础（propext/choice/Quot）。数值判定 L_K′(1) > 0 已真证（B3-min + ①c 后 LPrime 端零 axiom），K 端不再依赖反射公式的区间算术；代数秩端 rank_E_Q_eq_one 已分解为 ge/le 双声明（2-下降 ②）。

## 4. 编译与核验

```powershell
Set-Location c:\proj2
lake build BSD            # 全库；日志 > build_*.txt
lake env lean BSD/_check_bsd.lean   # #print axioms 核验
```

统计：`(Select-String -Path BSD\*.lean -Pattern "^axiom ").Count`——库代码 = 14（Main 7 + LSeries5 7；`_check_*.lean` 的核验脚本不计；TwoDescent.lean 无 axiom）；sorry 应为 0。

## 5. 状态与路线

**已闭合**：库结构、对象层、局部因子恒等式、几何级数尾（①a）、定理层拼合、(iv-c) 初等不等式链（5 条 theorem，含 native_decide 计算信任公理的透明标注）、**(iv-d) 部分和下界块**（`part50_ge` 2.6766 ≤ Σ_{n<50} fE5 n，50 项逐项 + 10 分块 cast 桥，axiom 闭包无数学假设——只含 native_decide 计算信任公理）、**①c 后半**（尾界三件套 + 合成 `L_E5_one_pos`/`L_E5_one_ne_zero`，axiom 16 → 15，sorry = 0）、**①b（素幂递推全链 + 乘性组装 → `coefficient_bound` 新定理形态）**；`lake build BSD` exit 0，axiom 15 = 15（−coefficient_bound +ap5_satake），sorry = 0。
**本窗口（任务 1+2，2026-10-06）**：K 端口径同步——Main.lean 顶部注释与 `analytic_rank_K_eq_one` docstring 由旧口径（2.433224，degree-2 反射公式 + N_K = 1369，错 48.5%）改为乘积恒等式口径（L_K′(1) = 1.63858644 ≥ 1.63808）；新增 §2b 声明层（`Lprime_E1`、`Lprime_E1_interval`、`analytic_rank_K_eq_one_of_LK_prime_ne_zero`）+ 真定理 `LK_prime_pos`（0 < L_K′(1)，闭包 = 区间声明 + `L_E5_one_pos` 定理）；**`analytic_rank_K_eq_one` 由 axiom 升级为 theorem**（弱 BSD 主定理的 K 端数值判定不再依赖反射公式区间算术）；库 axiom 15 → 17（Main 6 → 8），sorry = 0，`lake build BSD` exit 0。

**本窗口（② 2-下降，2026-10-06）**：`rank_E_Q_eq_one` 从单 axiom 升级为结构化判定——Main.lean 拆为 `rank_E_Q_ge_one` + `rank_E_Q_le_one` 双声明，`rank_E_Q_eq_one` 变为定理（`le_antisymm`）；新建 `BSD/TwoDescent.lean`（`lake build BSD.TwoDescent` exit 0）：E′ 整模型 Y² = X³ − 16X + 16（Δ′ = 2¹²·37）真证数值层（`Pprime`/`P2..P7` norm_num 在曲线上、`toEprime_preserves`、`delta_prime_set`）；无限阶支撑 = 7P′ = (−20/9, 172/27) 的 X 坐标分母含素因子 3 ∉ {2, 37}（坏约化素）⟹ Silverman VIII.7.1(b) ⟹ P₀ 非扭（Lutz–Nagell 候选整点恰为 P′, 2P′, 3P′, 5P′ 的倍数，不能单独排除）；2-下降域 K = ℚ(θ)（θ³ − 16θ + 16）论证骨架入注释；数值核验 `two_descent_check.py` 落盘（2P′..12P′、E[2]=E[3]={O}、Lutz–Nagell 候选、三次域数据）；库 axiom 17 → 18（Main 8 → 9），sorry = 0，`lake build BSD` exit 0，`weak_BSD_37a1` 闭包换入 `rank_E_Q_ge_one`/`rank_E_Q_le_one`。

**②b Selmer 完整数值计算（2026-10-06 收口）**：TwoDescent.lean 注释同步域算术口径——Δ_f = 9472 为多项式判别式；θ 三实根 ⟹ K 全实（r₁ = 3, r₂ = 0，单位秩 2）；π = θ/2 满足 2-Eisenstein 多项式 T³ − 4T + 2 ⟹ 𝒪_K = ℤ[π]、**Δ_K = 148、导子 c = 8**（k_arithmetic3.py 数值钉死：h_K = 1、2 = 𝔭₂³（e=3, f=1, 𝔭₂=(π)）、37 = 𝔭₃₇,₁·𝔭₃₇,₂²、δ(P′) = −θ = (0,−2,0)、N(−θ) = 16）。**Selmer 终跑 selmer7.py**（修正局部可解模型：ξ 局部可解 ⟺ ξ = 1 或 ∃x：f(x) ∈ K_v*² 且 (x−θ)ξ ∈ K_v*²；p2: 2¹⁴ 环全查、p37: 37⁴ 环双素片）：K(S,2) 候选（素分量 8 × 单位 8 = 64，|c| ≤ 120 最小 log-det 基本单位对）经 N ∈ ℚ*² 过滤 8 个，局部检查得 **|Sel²| = 2 = {(1,0,0), (0,−2,0) = −θ = δ(P′)}**（−θ 全局部可解：p37₁ ✓ p37₂ ✓ p2 ✓，命中 x = 1：f(1) = 1 平方、(1−θ)(−θ) ∈ K₂*² ⟹ δ(P) = 1−θ ≡ −θ，P = (1,1) ∈ E′(ℚ)）。⟹ dim Sel² = 1 ⟹ **rank E(ℚ) ≤ dim Sel² = 1**（E(ℚ)[2] = {O}），与 LMFDB 37.a1（rank = 1、Sha[2] = 0 ⟹ Sel² = E(ℚ)/2E(ℚ)）一致。**工程收口**：−θ 显式加入候选（δ 理论保证 δ(P′) ∈ Sel²），|Sel²| 结论不依赖基本单位对的唯一性；全部 ②b 脚本（k_arithmetic3/selmer2..7/dbg*）已备份至 Windows-RH-Lean-PC-2\_tmp_skA\_twodescent\。

**本窗口（D1+D2 升级 + 闭包审计，2026-10-06）**：`BSD_axiom_audit.md` 产出主定理闭包审计（18 axiom 分类：4 结构 [A] + 3 数值 [B] + 9 外部定理 [C] + 2 可消除 [D]；唯一发现 = C5 ε_K = −1 依据未显式落档）。**D1+D2 升级 theorem**：(D1) `coefficient_bound_aE5`——aE5_table.lean 定义结构改 wrapper（`aE5_raw` 802 分支原表 + `aE5 n = if n ≤ 800 then aE5_raw n else 0`，数值逐项不变），n ≤ 800 查表（native_decide ℤ 上 |aE5 m| ≤ 2m，m ∈ range 801）+ n ≥ 801 表外平凡（if_neg）；(D2) `summable_fE5`——|fE5 n| ≤ 2·exp(−α(n+1))（D1 + 除法界）+ Σ 几何级数（exp(−α) < 1，α = 2π/√925 > 0）+ Summable.of_norm_bounded，**完全干净**。**库 axiom 18 → 16**（Main 9 + LSeries5 7），`weak_BSD_37a1` 数学闭包 = 11 + 3 基础（propext/Quot/choice），native_decide 计算信任 112 → 114（+2 = D1 查表）；`lake build BSD` exit 0（3314 jobs）。

**本窗口（①c 复刻，2026-10-07）**：`lprime1_summable` axiom → theorem（LPrime.lean 最后一个数学 axiom 清除）。数学链：逐项界 `|aE(n+1)/(n+1)·E1(bn(n+1))| ≤ (2/1.03)·e^{−1.03(n+1)}`——`aE_bound`（n≤100 native_decide 分支 + 表外 0）、`E1_le`（E₁(b) ≤ e^{−b}/b）、`b1_gt_103`（bₙ ≥ 1.03n ⟹ bn ≥ 1.03、e^{−bn} ≤ e^{−1.03n}，`mul_le_mul` 组合）；右侧几何级数可和（`hasSum_geometric_of_norm_lt_one` + `pow_succ` 移位 + `exp_nat_mul`（先 `mul_comm`）+ `hq1.summable.mul_left`），`Summable.of_norm_bounded` 闭合。**库 axiom 15 → 14**（Main 7 + LSeries5 7），`#print axioms LK_prime_pos` 数学闭包 = LSeries5 `L_E5_series_split`/`Lambda_E5` + Main 声明层 + 基础（propext/choice/Quot）+ native_decide 计算信任公理，**无任何 LPrime axiom**；`lake build BSD` exit 0（3316 jobs）；`LPrime.lean` 独立编译 exit 0（探针 `_check_summable.lean` 先验证证明体）。①c 形态教训入 §3.3 4.11 段：`← pow_succ`（q^n·q 移位）、`exp_nat_mul` 需先 `mul_comm`、`Int.cast_abs`（@[simp] 但 ℤ→ℝ 形态需 `simp` 一步）、`neg_le_neg` 后负号绑定需 `rw [neg_mul]`、`(bn)⁻¹` vs `1/bn` 非 DefEq 需 `simpa`、doc comment 内 unicode（`−`/`①`）曾致 lexer 报错——注释改纯 ASCII。

**本窗口（②b 首轮 Lean 化，2026-10-07）**：`rank_E_Q_le_one` 依赖链的 ℚ 端真证化——TwoDescent.lean 新增两个真定理：`Eprime_poly_no_root`（X³ − 16X + 16 无 ℚ 根：有理根定理——r = n/d（互素）⟹ d | n³ ⟹（`Nat.Coprime.dvd_of_dvd_mul_left` 两步剥平方）d | 1 ⟹ d = 1 ⟹ r ∈ ℤ；n | 16 ⟹ |n| ≤ 16 ⟹ `interval_cases` 33 case `norm_num` 排除）与 `Eprime_two_torsion_trivial`（E′[2](ℚ) = {O}，eqn 代入 Y = 0 后调前定理）。`#print axioms BSD.Eprime_two_torsion_trivial` 闭包 = **仅 propext/choice/Quot.sound**（纯基础，真定理确认，原数值核验 two_descent_check.py 升级）。Main.lean `rank_E_Q_le_one` 注释同步：口径显式化——2-下降作用在 E′ 上，E 与 E′ 差一个 2-同源（`toEprime_preserves`，平移+缩放），同源保持 Mordell–Weil 秩（标准事实）⟹ rank E = rank E′ ≤ 1。axiom 数不变（14：Main 7 + LSeries5 7），`lake build BSD` exit 0（3316 jobs）+ `lake build BSD.TwoDescent` exit 0；weak_BSD_37a1 数学闭包不变。**②b 剩余**：K = ℚ(θ) 三次域类数/单位群（h_K = 1、𝒪_K = ℤ[π]）与局部可解性（selmer7.py 数值已收口）的完整 Lean 化——需类域/局部域理论（mathlib 缺失，大工程）。

**本窗口（②a 首轮真证化，2026-10-07）**：`rank_E_Q_ge_one`（Silverman VIII.7.1）的 Lean 可证部分全部真证——axiom 边界推到 Silverman 定理本体单点。
- **§1b 数值触发层**（TwoDescent.lean）：`P7_X_den`（P7.X 分母 = 9 = 3²，Rat 最简归一）、`three_prime`（decide）、`three_not_bad`（3 ≠ 2 ∧ 3 ≠ 37）、`P7_X_den_nonbad_factor`（3 | P7.X.den ∧ 3 ∉ 坏集）——Silverman 论证的输入事实。
- **§1c 群法则真证**：`Eprime_double`（切点加倍 λ = (3x²−16)/(2y)，需 P.Y ≠ 0；E′[2] = {O} 保证非 2-扭）与 `Eprime_add`（割线加法 λ = (y₂−y₁)/(x₂−x₁)，需 x₁ ≠ x₂）的**曲线保持性**：field_simp 消分母 + ring_nf 做差归零——加倍差恰为 `64y⁶(y²−x³+16x−16)`（`hfac` 因式分解 + `hE` 代入 P.eqn）；加法差含奇次幂项，先 `show` 幂拆分（P.Y³ → P.Y·P.Y²、P.Y⁴ → (P.Y²)² 等）再双方程代入 + ring。
- **7 倍链**：`P2_eq_double`、`P3_eq_add`..`P7_eq_add`（2P′..7P′ = (0,4),(4,4),(−4,−4),(8,−20),(1,−1),(24,116),(−20/9,172/27)）——原 two_descent_check.py 数值核验**升级为加法公式真证计算**。
- **闭包核验**（`_check_2a_ax.lean`）：`P7_eq_add`、`P7_X_den_nonbad_factor` 均**仅 propext/choice/Quot.sound**。Main.lean `rank_E_Q_ge_one` 注释更新（②a 已真证全部输入）。`lake build BSD` exit 0（3316 jobs）、`BSD.TwoDescent` exit 0；axiom 数不变（14），sorry = 0。
- **工程备注**：命名空间为 `BSD`（非模块名 `BSD.TwoDescent`）；结构相等用 `congr 1 <;> norm_num`（proof 字段由 congr 自动跳过）；Eprime_double 探针先于并入验证（`_check_2a.lean` 全程绿）。

**待办（按量级排序）**：
- ②b `rank_E_Q_le_one`：Selmer 数值计算已收口（|Sel²| = 2 = {1, −θ}，dim = 1 ⟹ rank ≤ 1，selmer7.py）；Lean 侧 `rank_E_Q_le_one` 仍为 axiom（2-下降理论 + 局部可解性的完整 Lean 化需类域/局部域理论，mathlib 缺失；数学依据已由 selmer7.py + LMFDB 钉死）。剩余待做：基本单位对的唯一性严格化（可选，|Sel²| 结论不依赖）、selmer7 结果入文档链（骨架A讨论稿）
- **补 C5 ε_K = −1 依据**（闭包审计发现）：根数乘性 ε_K = ε(E)·ε(E⁵) = (−1)(+1) = −1 未显式落档——补进 Main.lean 注释 + 骨架A讨论稿 4.3
- ②a 剩余：Silverman VIII.7.1(b) 本体（扭点 x 坐标分母只含坏约化素因子）——需要完整椭圆曲线约化理论（mathlib 缺失）；②a 已真证其**全部输入**（`Eprime_double`/`Eprime_add` 曲线保持、2P′..7P′ 链、`P7_X_den_nonbad_factor` 分母坏因子），axiom 边界已推到 Silverman 定理单点
- ③ `twist_decomposition`：Galois 模分解（数学证明已有，Lean 化大）

**永久 axiom 风险（诚实标注）**：`ramanujan_ap_E`（Deligne）、`ap5_satake`（Deligne，①b 引入）、`Lambda_E5`（自守 L）——mathlib 无对应理论，除非引入完整模形式/自守理论，否则以 axiom 形式保留并在文档中声明"数值/文献已验证"。`ap5_satake` 与原 `coefficient_bound` 同为"对象层真证、深层声明层带待证明注释"路线上的等价取舍：`coefficient_bound`（任意 n 的 τ(n)√n 界）被拆为"可证组装（乘性+素幂递推）+ 单个 Deligne 输入（Satake 参数）"。

## 6. 关联产物

- 讨论稿：《弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx》（SHA256=6D3C37…FEB2）
- 数值管线：`_tmp_skA\verify_E5.py` / `verify_E5_iii.py` / `E5_out.txt`（a₃₇=+1 确定、L(E⁵,1) 区间）
- 域基础设施：`OrderPreservingBijection/QuadraticFieldFive.lean`（GoldenInt、phi²=phi+1、norm）
