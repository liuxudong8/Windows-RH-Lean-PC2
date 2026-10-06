# BSD 库——弱 BSD 秩 1 的 Lean 形式化（状态摘要）

> 更新：2026-10-06 ①b 素幂递推+乘性落盘轮。编译基线：`lake build BSD`，exit 0；sorry = 0；数学 axiom = 15（Main 6 + LSeries5 9；§5 (iv-d) 新增声明 + native_decide 计算信任公理，见 §3.1/§3.2）。

## 0. 一句话定位

把《骨架 A 讨论稿》（K = ℚ(√5)，E = 37a1）的"代数秩 = 解析秩 = 1"判定做成 Lean 三层骨架：**对象层真可证，数论/分析深层走声明层（axiom 带待证明注释），拼合层定理成立**。任何 axiom 都有明确的可升级路径，无死路。

## 1. 数学口径（与文档对应）

| 对象 | 口径 | 文档 |
|---|---|---|
| 主曲线 | E = 37a1：y² + y = x³ − x，Δ = −37，N = 37 | 2.1 |
| 域 | K = ℚ(√5)，N_K = 1369，ε_K = −1 | 2.1 |
| 二次扭 | E⁵：Y² = x³ − 25x + 125/4，N(E⁵) = 925，ε(E⁵) = +1 | 5.4(iv) |
| 解析秩(E/K) | = 1：L_K(1) = 0（ε_K = −1）+ L_K′(1) ∈ [2.4332226, 2.4332261] ⊂ (0,∞) | 4.3, 5.4(iii) |
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
│   ├── BSD_summary.md       # 本文件
│   ├── _check_bsd.lean      # #print axioms 核验（weak_BSD_37a1 等）
│   ├── _check_ls5.lean      # #print axioms 核验（LSeries5 各层）
│   └── _check_1a.lean       # #print axioms 核验（geom_tail_bound 闭合）
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

**Main.lean — 6 个**：

| axiom | 含义 | 升级路径 |
|---|---|---|
| `analyticRank` | 解析秩（函数定义，mathlib 无自守 L） | 自建 L 函数层（LSeries5 方向） |
| `mwRank` | Mordell–Weil 秩（mathlib 无椭圆曲线理论） | 需要全套算术几何 |
| `analytic_rank_K_eq_one` | 解析秩(E/K)=1（4.3/5.4(iii) 区间判定） | LSeries5 反射公式 + 区间算术（①c） |
| `rank_E_Q_eq_one` | rank E(ℚ)=1（LMFDB，生成元 (0,0)） | 2-下降 + 高度（②） |
| `rank_E5_Q_eq_zero` | rank E⁵(ℚ)=0（Kolyvagin） | L_E5_one_ne_zero + Kolyvagin 定理 |
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

- `algebraic_rank_K_eq_one`：mwRank E(K) = 1（rw 拼合，axiom 闭包 = 6 声明 + 基础）
- `analytic_rank_K_eq_one'`：解析秩 = 1
- `weak_BSD_37a1`：mwRank = analyticRank（弱 BSD 秩 1 成立）
- 均无 sorry；`#print axioms` 闭包含声明的 6 个 + propext/choice/Quot

## 4. 编译与核验

```powershell
Set-Location c:\proj2
lake build BSD            # 全库；日志 > build_*.txt
lake env lean BSD/_check_bsd.lean   # #print axioms 核验
```

统计：`(Select-String -Path BSD\*.lean -Pattern "^axiom ").Count`（当前 15：Main 6 + LSeries5 9）；sorry 应为 0。

## 5. 状态与路线

**已闭合**：库结构、对象层、局部因子恒等式、几何级数尾（①a）、定理层拼合、(iv-c) 初等不等式链（5 条 theorem，含 native_decide 计算信任公理的透明标注）、**(iv-d) 部分和下界块**（`part50_ge` 2.6766 ≤ Σ_{n<50} fE5 n，50 项逐项 + 10 分块 cast 桥，axiom 闭包无数学假设——只含 native_decide 计算信任公理）、**①c 后半**（尾界三件套 + 合成 `L_E5_one_pos`/`L_E5_one_ne_zero`，axiom 16 → 15，sorry = 0）、**①b（本窗口落盘）**：素幂递推全链（ppow/ssum/Newton/ppow_eq_ssum/ssum_abs_bound/ppow_bound）+ 乘性组装（prod_le_prod_nonneg/abs_prod_int/sqrt_pow_eq/sqrt_prod_eq/prod_primeFactors_pow_eq/card_divisors）→ `coefficient_bound_assembled` + `coefficient_bound` 新定理形态（原 axiom 已删）；`lake build BSD` exit 0，axiom 15 = 15（−coefficient_bound +ap5_satake），sorry = 0。

**待办（按量级排序）**：
- ② `rank_E_Q_eq_one`：2-下降（大）
- ③ `twist_decomposition`：Galois 模分解（数学证明已有，Lean 化大）

**永久 axiom 风险（诚实标注）**：`ramanujan_ap_E`（Deligne）、`ap5_satake`（Deligne，①b 引入）、`Lambda_E5`（自守 L）——mathlib 无对应理论，除非引入完整模形式/自守理论，否则以 axiom 形式保留并在文档中声明"数值/文献已验证"。`ap5_satake` 与原 `coefficient_bound` 同为"对象层真证、深层声明层带待证明注释"路线上的等价取舍：`coefficient_bound`（任意 n 的 τ(n)√n 界）被拆为"可证组装（乘性+素幂递推）+ 单个 Deligne 输入（Satake 参数）"。

## 6. 关联产物

- 讨论稿：《弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx》（SHA256=6D3C37…FEB2）
- 数值管线：`_tmp_skA\verify_E5.py` / `verify_E5_iii.py` / `E5_out.txt`（a₃₇=+1 确定、L(E⁵,1) 区间）
- 域基础设施：`OrderPreservingBijection/QuadraticFieldFive.lean`（GoldenInt、phi²=phi+1、norm）
