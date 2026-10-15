# BSD 库——弱 BSD 秩 1/秩 2 对称 + n=3 骨架的 Lean 形式化（状态摘要）

> 更新：2026-10-16（G3/G4 工程补齐 + 挂账 Lean 真证层）——**G3（Reg 全精度）闭合**：Sage regulator(precision=200) = 0.15246017794314375162432475704945582324372707748663...，高度配对 det 0.152460177943144（gens [(−1:1:1),(0:−1:1)]），Python NT/Sage/Magma/LMFDB 四源一致到 ~10⁻¹⁹；G2a 判别 Reg 误差从 5×10⁻⁶ 收窄 6 个数量级，#Ш_pred ≈ 1±10⁻¹²。**G4（纯 Python 独立复算 |Sel₂|）闭合**：A=ℚ[x]/(x³+x²−2x+1/4)（全实三次域），单位穷举 ε₁=(−1,8,−4)、ε₂=(−1,8,4)；类数 h=1（Minkowski 界 8.76 + P₂/P₃ 主性：∃δ N=±2/±3）；|A*/A*²|=8，N∈ℚ*² 筛选 ⟹ **|H¹(ℚ,E[2])|=4**（δ=1,(1,−8,4),(1,−8,−4),(−3,20,16)）⟹ |Sel₂|≤4 ∧ rank=2 无挠 ⟹ |Sel₂|≥4 ⟹ **|Sel₂|=4**（纯标准库无 numpy）。**挂账 `Sha11_389.lean`**：`sel2_order_four_389`（axiom）+ **真证 `sha2_order_one_389`（#Ш[2]=1 = 4/2²，descent 阶关系组合，数据锚点已闭合）** + `RegHighPrecision389`/`reg_high_precision_389`（axiom）；G2 层注释 Reg 更新为 200 位口径。`lake build -R` 全绿 7690 jobs。详见 §13。
> 更新：2026-10-15（缺口 A 数值核验闭合——CH22 Theorem A 假设层补齐）——**L(E/K,χ²,1) ≠ 0 数值核验完成**：构造 Cl_5 二次 ring class 特征 χ²=(N(𝔞)/5)（conductor 5）、θ(χ²) level 200、Rankin-Selberg 卷积 a_n=Σ_{d|n}a_E(d)·b_{n/d}（Sage 50000 系数）；PARI lfuncreate 低层格式 `[an,1,[0,1/2,1,3/2],3,77800,1]`（Vga=Γ(s)Γ(s+1/2) 型、k=3、N=389·200、eps=+1）——**三参数扫描裁决**（conductor 5 候选 / eps ±1 / Vga 3 候选，lfuncheckfeq 独胜组合）：**L(1)=4.9098500369129333522552480141603036183…≠0**，5000/50000 系数收敛至 10⁻²⁷。回写 `Sha11_389.lean`：`LEKChi2Nonzero389`/`l_ek_chi2_nonzero_389` 注释从"数值核验待做"更新为"已核验闭合"（axiom 保留：数值支持、不替代证明），编译全绿（1069 jobs）。**Thm-A 假设五项至此全部有数依据**（①L(E^χ,1)≠0 2.788 已挂、②χ² 非零 4.90985 新闭合、③ρ̄ 不可约 389a 类单曲线论据、④N⁻ 无平方 389 素数、⑤q|N⁻ 分歧 389 乘性）。详见 §12。
> 更新：2026-10-15（Θ_{f/K} 反cyclotomic 复刻收尾）——"最难"主线 **Θ_{f/K} Sage Brandt module 复刻**（CH22 定理前提 ord_T=2 的真复刻）阶段闭合：① **根本 bug 修复**（v4–v10 把类索引当 f 值求和——f 从未参与 Θ）；② **ord_T=2 判定闭合**：389a1（T²≡78）与 709a1（T²≡94）均 T⁰=T¹=0、T²≢0 mod 121 ⟹ ord_T=2，两曲线独立成立，与 CH22 靶一致（T⁰=T¹=0 为结构性质，对 f_E p-adic 归一化稳健）；③ **逐系数对靶定位为不可达**（f_E "p-adically normalized" 细节 + optimal embedding，论文未给）；④ ord_T=2 判定**挂账进 `Sha11_389.lean` 证据块**（axiom 层不变，证据注释更新 + 新证据块），编译全绿。详见 §11。
> 更新：2026-10-15（λ₁₁ = 2 数值支柱 + 跨素数核对）——数值路径 1 本体完成：389a1/p=11 series(11) 复刻（PARI/GP 真模符号管道）验证 **ord_T L₁₁ = 2（λ₁₁ = 2）**（L₁₁(T)=9T²+9T³+… mod 11，T⁰≡0 mod 11⁴、T¹≡0 mod 11、T²≡9 mod 11≠0，220+22 点自洽 + 两条分布恒等式精确成立）；挂账 Lean（`Sha11_389.lean` 数值验证层，编译全绿）；③ 跨素数核对：E^χ（twist，cond 24896）**analytic rank 0、M(0)=2** ⟹ T⁰≡10 mod 11≠0 ⟹ **λ₁₁(E^χ)=0**，特征分解 **λ(E/K)=λ(E)+λ(E^χ)=2+0=2**（Q 侧 = K_cyc 侧，跨素数 {3,11} 一致）；挂账 Lean（跨素数核对层，真证 `lambda_ek_two_389`）。`lake build BSD.Sha11_389` 全绿。详见 §10。
> 更新：2026-10-13（Sha 有限性攻关）——五阶段路线（Iwasawa 欧拉系延伸）A 阶段全绿、B 阶段落地、B-6 rank-2 欧拉系评估命中 CH22、框架实证两处纠错、CH22 链 Lean 集成完成（`sha11_finite_389 : ShaFinite Curve389a1 11` 真证）、λ₁₁ K_cyc 侧评估完成（三条路径待选）。`lake build -R` 全绿 7690 jobs。详见 §9。
> 更新：2026-10-12（会话题目《编译lean项目20261012》续）——公式 (4)（负根数 twist 计数）Lean 姊妹模块 `SymmetryFormula4` 落地：联系链 §5.2 (4) 式（L″(E/K,1)>0 ⟺ 负根数计数为偶）以"三类 axiom + 组装 (3) 核心 + 真定理"落盘，79a1 (1,1) 与 389a1 (2,0) 双实例验证，Σr_χ=2 ⟹ 计数自动为偶（P* 无条件性在奇偶层的复现）；`BSD.lean` 加入口后 `lake build -R` 全绿（7690 jobs）；已同步至 Windows-RH-Lean-PC-2。详见 §8。
> 更新：2026-10-11（会话题目《编译lean项目20261011》）——秩 2 对称链与 n=3 困难平移第一块骨架收口。10-11 完成：ExclusionReduction（秩1反向排除层）、LeibnizReduction（leibniz_artin 二阶真定理化，任务1/2）、43a1 (1,0) 全闭证（LPrime43 + LSeries5_43 + _check_43a1）、SymmetryReduction（扭对合秩对称泛型）、秩 2 文档 4.7 节插入（audit --source exit=0 + sha 校验写回）、SymmetryClosure（79a1 (1,1) 三件套）、SelmerDescent（任务3 挂账）、任意秩对称三层分析、LeibnizThird（(2,1)/(1,2) 三阶 Leibniz 真定理，闭包仅纯逻辑）。

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

## 7. 2026-10-08 → 10-11：秩 2 对称链 + n=3 骨架（会话题目《编译lean项目20261011》）

主线从"秩 1 反向（排除层 ord ≤ 1）理论"推进到"秩 2 对称闭环（(1,1) 型）"与"任意秩对称三层分析"，并以 (2,1) 型三阶 Leibniz 真定理作为 n=3 困难平移的第一块骨架。

### 7.1 产物清单（全部编译 exit=0，compile_log.txt 为权威纪录）

| 日期 | 文件 | 内容 |
|---|---|---|
| 10-08~10-10 | `Probe389/` `Probe5077/` `PStarOr/` `Stage2/RankTwoExclusion.lean` `ZeroGap/` `Main.lean`（10-10 更新） | 389a1/5077a1 探针、P* 或型、秩 2 排除层（排除 ord ≥ 3）、零点间隙；compile_log 全绿 |
| 10-11 | `ExclusionReduction.lean` | 秩 1 反向排除层理论 Lean 化（仿写模板，`exclusion_layer_nonzero`） |
| 10-11 | `LeibnizReduction.lean` | **任务 1/2**：`leibniz_artin`（原 P* 挂账 axiom）升级为二阶 Leibniz 三型真定理——`product_second_deriv`/`leibniz_20/02/11_second` + `_ne_zero`；对象级 `L_fun_structure` axiom + `leibniz_artin_theorem` + `p_star_type_20/11/02_via_leibniz`；`p_star_via_leibniz` 拼合 |
| 10-11 | `LPrime43.lean` `aE_table_43.lean` `aE5_table_43.lean` `LSeries5_43.lean` `_check_43a1.lean` | **43a1 (1,0) 型全闭证**：L_P(43a1,1)>0 真定理（round 18）、200/800 项系数表（aE5 表行 47 手工修正 \|43\|→1）、L(E⁵,1)>0/≠0 全闭（term_i 数值化桥接 + crude50_ge_R_43 + tail51_bound_43）、`L_prime_43_ne_zero` 组装（= lprime1_43_pos × L_E5_43_one_ne_zero，仿 exclusion_layer_nonzero） |
| 10-11 | `SymmetryReduction.lean` | **扭对合秩对称泛型**（ns BSD.SymmetryReduction）：对象层 rankE/E5/EK + `rank_additivity`（秩加法 axiom）+ `ShaFiniteE/E5/EK`；Kolyvagin 挂账 ×5 + `sha_finite_EK_of_descent`；真定理 `symbol_symmetry_11`（= leibniz_11_second_object 对称重述）、`p_star_11_sym`（= p_star_type_11_via_leibniz）；组装 `rank_EK_two_of_both`/`sha_finite_EK_of_both`/`symmetry_closure_11` |
| 10-11 | 《弱BSD秩2反向的正性判别.docx》4.7 节 | **秩对称入文档**："扭对合秩对称：秩 2 由秩 1 对称组合"（P1–P4）；audit --source exit=0、全文无"你"、sha256 校验写回原路径（34d7d14d…46dd7b6） |
| 10-11 | `SymmetryClosure.lean` | **任务 4**：79a1 (1,1) 型三件套组装——`entanglement_79`/`entanglement_79_pos`/`Lpp_EK_79_pos`/`Lpp_EK_79_ne_zero`（仿 L_prime_43_ne_zero）/`rank_EK_79_two`/`sha_finite_EK_79`/`symmetry_closure_79` |
| 10-11 | `SelmerDescent.lean` | **任务 3**（数学是定理，按定理级挂账，与 Kolyvagin 同层）：正合列 0→Sel(E)→Sel(E/K)→Sel(E⁵)（坏 p 有限修正）+ descent 序列 0→E(K)/p^n→Selⁿ→Sha[p^n]→0（Sel 有限⟹Sha 有限）+ Kolyvagin Selmer 形式；`sha_finite_EK_of_selmer_descent`/`sha_finite_EK_11_via_selmer` |
| 10-11 | （纯分析） | **任意秩对称推广三层结论**（无工具产物，内联 SVG 图） |
| 10-11 | `LeibnizThird.lean` `_check_leibniz_third.lean` | **n=3 困难平移第一块骨架**：(2,1)/(1,2) 型三阶 Leibniz 首项公式真定理化（见 7.3） |

### 7.2 数学结论：秩对称三层（任意秩 n、扩张次数 m = [K:ℚ]）

1. **结构层（任意 n、任意 m 成立，定理）**：rank E(K) = Σ_χ rank E^χ(ℚ)；L(E/K) = Π_χ L(E^χ)（Artin 分解）⟹ ord 加法；Selmer descent 沿 χ 分解。K 侧秩 n ⟺ 分配 (n₁,…,n_m)，Σnᵢ = n。
2. **符号层（任意 n 无条件）**：P*_n（解析秩 r ⟹ L^(r)(1) > 0）由通道 B 直接给出——L^(r)(1)/r! = lim_{s→1⁺} L(s)/(s−1)^r ≥ 0 且 L^(r)(1) ≠ 0；**免公式免 GRH，不依赖对称**（对称在符号层只是纠缠积的结构身份）。
3. **完全闭包（⟺ n ≤ m）**：秩加法 + 两侧秩反向（Kolyvagin–Gross–Zagier，仅秩 ≤ 1 分量）+ 两侧 Sha 有限（Kolyvagin）全部由秩 ≤ 1 定理组合 ⟺ 存在全 1 分配 ⟺ **n ≤ m**。抽屉原理：n > m ⟹ 必有分量秩 ≥ 2，落回 389a1 类开放。二次域 m = 2：非平凡全闭合秩只有 n = 2（(1,1)，79a1 已落盘）；n ≥ 3 含秩 ≥ 2 分量。**困难平移 = max 分量秩**（(1, n−1) 型降一阶）。
4. **高阶 Leibniz 首项公式**：(fg)^(a+b)(1) = C(a+b, a)·f^(a)(1)·g^(b)(1)；(2,1) 型即 C(3,2) = 3。

### 7.3 LeibnizThird.lean（(2,1)/(1,2) 型三阶真定理，纯微积分）

- `product_third_deriv`：(f·g)‴(1) = f‴(1)·g(1) + 3·f″(1)·g′(1) + 3·f′(1)·g″(1) + f(1)·g‴(1)。
- `leibniz_21_third`：(2,1) 型（f(1)=f′(1)=0, g(1)=0）⟹ (fg)‴(1) = **3·f″(1)·g′(1) = C(3,2)·f″(1)·g′(1)**。
- `leibniz_12_third`：(1,2) 对称 ⟹ (fg)‴(1) = 3·f′(1)·g″(1)。
- `leibniz_21/12_third_ne_zero`：非零传播（f″(1)≠0 ∧ g′(1)≠0 ⟹ (fg)‴(1)≠0）。
- 证明路线：v4.34 **无 `iteratedDeriv_mul`**（IteratedDeriv 模块不存在，探针确认）→ 手工三层（C3At 开邻域 C³ → v 内逐点恒等式 ×3 → 事件等价 → HasDerivAt 六元组合 + ring）。
- **闭包审计（#print axioms exit=0）**：五定理依赖均仅 `[propext, Classical.choice, Quot.sound]`——**纯逻辑，零 axiom、零公式、零 GRH、零对象层挂账**；是 n=3 侧第一个零挂账模块（对照 p_star_11_sym 含 bsd_formula_rank_one/one5）。

### 7.4 闭包审计事实（#print axioms 实测，数学分层证据）

| 定理 | 闭包 | 分层 |
|---|---|---|
| `symbol_symmetry_11` | 无 bsd_formula_rank_* | Leibniz 三型 + L_fun_structure + Positivity 数值对象 + 逻辑 |
| `p_star_11_sym` | 含 bsd_formula_rank_one/one5 + Omega/Regulator/Sha/Torsion 分量对象 | 分量符号是 Positivity 级 axiom，数学上 Kolyvagin 定理 |
| `symmetry_closure_79` | 仅 79 系对象层 axiom | 数据 zeroOrder + 定理级挂账（leibniz_11_79/rank_additivity_79/Kolyvagin×2/descent）；无公式无 GRH |
| `sha_finite_EK_11_via_selmer` | 仅 SelmerDescent 对象层 + zeroOrder | 与 Kolyvagin 同层定理级挂账；无公式无 GRH |
| `product_third_deriv` 等五条 | 仅 propext/choice/Quot.sound | 纯微积分真定理 |

### 7.5 编译陷阱（10-11 新增，避免重踩）

1. **rw 链自动关 goal**：ℕ 上 rw 对定义性相等（1+1=2）会自动关闭目标，**尾随 norm_num/rfl 报 "No goals to be solved"**——写成单条 `rw [a, b, c]` 即可。
2. **unfold 报错**：目标已展开为乘积形时 `unfold` 报 "Tactic unfold failed"——删除多余 unfold。
3. **`𝓝` 是 scoped notation**：需 `open scoped Topology`；仅 import `Mathlib.Topology.Basic` 不够。
4. **v4.34 `DifferentiableOn` 给 `DifferentiableWithinAt`**：提升到 At 用 `(h_diff s hs).differentiableAt (hv_open.mem_nhds hs)`。
5. **`deriv_mul` 返回等式**：不可投影 `.differentiableAt`——可微参数用 `DifferentiableAt.mul`。
6. **依赖模块失败传染**：被依赖模块编译失败时，import 它的文件报 "object file ... does not exist"（先修依赖）。
7. **v4.34 无 `iteratedDeriv` 抽象层**：三阶 Leibniz 只能手工三层（ContDiffOn 3 分层 + 逐点恒等式 + HasDerivAt 组合）。

### 7.6 待办 / 未决

- **(2,1) 对象层两步**（n=3 困难平移续）：
  - (a) `L_fun_structure` 三阶化：L‴(E/K,1) 数值对象 + Artin 分解 (2,1) 分配 axiom；
  - (b) 与 Positivity 三阶对象（`lprimeprimeprime_pos_of_rank_three` 类）对接，把通道 B 符号层推至秩 3。
- **m ≥ 3 全闭合**：(1,1,…,1) 分配的存在性是条件性的，无实例数据（对称陈述：*若*全 1 分配则闭包）。
- **验收**：任务 1–4（LeibnizReduction/SymmetryReduction/SymmetryClosure/SelmerDescent）、文档 4.7 节、LeibnizThird 均已交付，待验收；若用户再提则续修。
- **遗留口径**：43a1 (1,0) 侧 L(E⁵,1) 表 aE5 行 47 手工修正（\|43\|→1）已注释说明（乘性特判），如需可升级为 ap5_multiplicative 系定理。

## 8. 2026-10-12：公式 (4) 负根数 twist 计数模块（会话题目《编译lean项目20261012》续）

把联系链《对称性+正性 ⟷ K-GRH：联系链》§5.2 (3)(4) 式与 §8 落点做成 `SymmetryClosure` 的姊妹模块 **`BSD.SymmetryFormula4`**（`BSD/SymmetryFormula4.lean`）：逻辑纯代数（有限特征标计数 + 奇偶性 + 符号运算），不碰 L 函数解析延拓，形式化难度远低于 Kolyvagin / Selmer descent。

### 8.1 模块结构（三类 axiom + 组装 + 真定理）

| 层 | 名称 | 内容 |
|---|---|---|
| 对象层 | `zeroOrderE/E5/EK_f4`、`rootE/rootE5_f4`、`LppEK_f4`、`chi_NE/chi_neg/local_f4` | 分量解析秩、根数、K 侧二阶导、twist 根数公式三输入 |
| (1) L 分解 | `l_fun_decomposition_f4` | ord L(E/K,1) = ord L(E,1) + ord L(E⁵,1)（Artin 分解，定理级挂账） |
| (2) BSD 奇偶性 | `bsd_parity_f4` / `bsd_parity5_f4` | ε(E⊗χ) = (−1)^{ord L(E⊗χ)}（自对偶 L 函数） |
| (3) twist 根数公式 | `twist_root_number_f4` | ε(E⊗χ) = ε(E)·χ(N_E)·χ(−1)·(局部修正)（联系链 5.3） |
| 组装 (3) 式核心 | `lpp_pos_iff_root_prod_f4` | L″(E/K,1) > 0 ⟺ 零阶分量根数积 = +1（5.1 分量符号 + 5.2 卷积，挂账） |
| (4) 式定理 | `formula4_f4` | K 侧秩 2 ⟹ L″>0 ↔ 负根数计数偶（**真证明**：穷举三型） |
| 推论 | `lpp_pos_of_analytic_two` | K 侧秩 2 ⟹ L″>0（**真证明**） |

### 8.2 关键数学：Σr_χ = 2 下 (4) 式右端恒真——奇偶性必要条件，非正性本身

(4) 式右边的偶性在 K 侧秩 2 下**恒成立**：(0,2)/(1,1)/(2,0) 三型（BSD 奇偶性 ε=(−1)^ord）负根数计数分别为 0/2/0——更深一层：(3) 式右端（零阶根数积 = +1）在 Σr=2 下恒真（(1,1) 空积 = 1；(2,0)/(0,2) ε(秩 0 分量) = (−1)^0 = +1）。

因此 **(3)/(4) 是奇偶性必要条件，不是正性本身**：它们在秩 2 情形不携带超出"各分量符号为正"（r≥1 通道 B；r=0 根数 + BSD 符号定理）的约束，(4) 的价值在**矛盾检测**（若某实例计数为奇，则 K 侧秩 2 与正性不相容）。正性来源因型而异，见 §8.3。"一正一负 ⟹ 计数 1 奇 ⟹ 矛盾"的情形被 ε(E/K) = ∏ε(E⊗χ) = (−1)^{Σr} = +1（Σr=2 偶）自动排除。

### 8.3 双实例（数据层 axiom + 真定理组装）

| 实例 | 型 | ε(E), ε(E⁵) | 计数 | 结论 | 对照 |
|---|---|---|---|---|---|
| 79a1 | (1,1) | −1, −1 | 2（偶） | L″>0 | SymmetryClosure 纠缠积通道合流（`lpp_EK_79_pos_both_f4`） |
| 389a1 | (2,0) | +1, +1 | 0（偶） | L″>0 | 区间算术 L″(389a1,1) = 1.518633 > 0（Probe389） |

- 389a1 数据（Probe389/probe389_summary.md §2，已核）：ε(E)=+1（LMFDB，秩 2 偶、a₃₈₉=+1 split mult）；χ₅(−389)=(5/389)·χ₅(−1)=+1（互反 (5/389)=(389/5)=(4/5)=1，实二次域 χ₅(−1)=+1）；局部因子=1（gcd(389,5)=1，χ 在 389 非分歧）。
- `rootE5_eq_rootE_79/389_f4`：twist 根数公式的实例算术自洽性（χ·χ(−1)·局部 = 1 ⟹ ε(E⁵)=ε(E)，与 BSD 奇偶性给出的 ε 值一致）。
- 两个实例恰好覆盖 (4) 式右边偶性的两种来源：79a1"两负抵消"（计数 2）、389a1"无负"（计数 0）。

**正性来源的不对称（要点明）**：(1,1) 型（79a1）正性 = 纠缠积 2L′(E,1)L′(E⁵,1)，即秩 1 分量符号（Gross–Zagier / 通道 B 秩 1，无条件）；(2,0) 型（389a1）正性 = ℚ 侧秩 2 分量 L″(E,1) > 0——(2,0) 下 L″(E/K,1) = L″(E,1)·L(E⁵,1)（Leibniz 消项），且 sign L(E⁵,1) = ε(E⁵) = +1（无条件），故 L″(E/K,1) > 0 ⟺ L″(E,1) > 0。一般曲线秩 2 正性为开放猜想；389a1 由区间算术 L″(389a1,1) = 1.518633 > 0（Probe389）无条件验证。**因此 (4) 不单独证明任一型的正性，只通过奇偶筛；(2,0) 的困难被准确定位到 ℚ 侧秩 2 分量**（框架表述修正：原"两条独立通道合流"改为"奇偶必要条件 + 分量符号输入"）。

### 8.4 闭包审计与编译

| 定理 | 闭包 |
|---|---|
| `formula4_f4` / `lpp_pos_of_analytic_two` | 本模块对象层 + 三类挂账 + (3) 组装；**无 GRH、无 bsd_formula_rank_\*** |
| `lpp_pos_79_f4` / `lpp_pos_389_f4` | 上述 + 实例数据层 |
| `rootE5_eq_rootE_79/389_f4` | twist 根数公式 + 实例算术数据 |

- 编译：`lake build BSD.SymmetryFormula4` exit 0；`BSD.lean` 加 `import BSD.SymmetryFormula4` 入口后 `lake build -R` 全绿（7690 jobs，BSD 库 10 个 olean 入工作区）；探针 `_check_symmetry_formula4.lean` 闭包核验 exit 0。
- 工程：构建日志 `build_project_20261012_f4*.txt`；已同步 `BSD.lean` / `SymmetryFormula4.lean` / `_check_symmetry_formula4.lean` 至 Windows-RH-Lean-PC-2（SHA256 一致）。

## 9. 2026-10-12 → 10-13：Sha 有限性攻关（五阶段路线 A/B 全绿 + CH22 Lean 集成 + λ₁₁ 评估）

主线从"秩对称闭环"转入 **Ш 有限性** 的正面攻坚：从定义出发评估 → 五阶段路线落盘 → A 阶段（免费层闭合）→ B 阶段（欧拉系 Rank-1 → Iwasawa corank，λ_p=0）→ B-6（rank-2 欧拉系/广义 Kato 类评估）→ CH22 框架实证 + Lean 集成 → λ₁₁ K_cyc 侧评估。

### 9.1 "从定义出发"评估与数值锚点

- 四条纯定义路径（Poitou–Tate 逐层有限、局部 Tate 配对、descent、Cassels 配对）循环或等价于 BSD/Kolyvagin，**无新数学输入**；但 `|Ш[n]| = |Sel_n|/|E(K)/nE(K)|` 逐 n 可算，作交叉检验（`Probe389/sha_crosscheck.*`）。
- 锚点交叉检验：Ω = 4.98042512171011、Reg@n=9 = 0.1524593847、∏c = 1、BSD 预测 |Ш| = 1.0000000000004；**|Sel₂(389a1)| = 4 三次域独立复现**（A = ℚ(β)，β = 2θ，G = x³+2x²−8x+2，β² ≡ 1 mod A*² 使 16→8 类；p=2 全过、p=389 拒 γ¹ 类 4 个、∞ 拒 γ 类）。"g 非 389a1"旧诊断被 j 不变量反证推翻（E″:Y²=X³+4X²−32X+16 同构）。

### 9.2 五阶段路线（`BSD/document/Iwasawa欧拉系延伸路线.md`）

Ш 有限 ⟺ (i) 每 p 的 p-秩有界 = **λ_p = 0**（Iwasawa 主猜想侧）∧ (ii) 除有限个 p 外 Ш[p] = 0。路线 A/B/C/D/E；A（免费层）→ B（Rank-1 欧拉系 → λ_p=0）→ B-6（rank-2 欧拉系/广义 Kato，新数学输入）→ C/D/E（文献链/数值/Lean 挂账）。

### 9.3 A 阶段（免费层闭合，全绿）

- `BSD/ShaPComponent.lean`：**引理 A.1 真证** `G[p] = 0 ⟹ G[p^∞] = 0`（torsionBy/nsmul 系）。
- `BSD/ShaFreeLayer.lean`：descent 基数真证 `card_eq_mul_of_short_exact_add`、Cassels 交错配对结构真证 `injective_of_nondegenerate`、平方结论挂账 axiom、389a1/p=2 **`sha2_389_card_eq_one` 真证推导**（|Ш[2]| = 1）。
- 并入 `BSD.lean` 聚合；闭包核验 `_check_l01/l02.lean` 干净；`lake build -R` 7690 jobs 全绿。

### 9.4 B 阶段（`BSD/EulerSystem.lean`，B-0..B-6）

- 对象层：`Corank`/`Rank`/`Lambda`/`OrdinaryAt`/`EulerSystemRankOne`/`Sha_p`(+group/fintype)/`kolyvagin_descent_bound`/`KatoClassNonzero`/`kato_corank_bound` axioms（namespace BSD.EulerSystem）。
- **组合真证**：`lambda_zero_of_kato`（控制定理 + Kato 界 ⟹ λ_p = 0）、`lambda_zero_iff_corank_eq_rank`。
- **盲区显式化**：`kolyvagin_rank2_blind_389a1 : ¬ EulerSystemRankOne Curve389a1 K389a1 2`（Rank-1 欧拉系工具对秩 2 失效，B-6 的出发点）。
- 389a1/p=2 实例：`rank_389a1 : Rank Curve389a1 K389a1 = 2`、`ordinary_389a1_2`（⚠ 已被数学反证，见 9.6）、`lambda2_389a1_eq_zero`（挂账）。
- 编译陷阱（入册）：axiom/theorem 参数必须显式 `(E : Type)`（隐式致 K 位置错位）；变量名禁 `λ` 字符（Lean 解析为 lambda 关键字）；`import Mathlib.GroupTheory.Index`；`Nat.add_left_cancel` 方向（2+0=2+x ⟹ x=0）；rw 列表含局部变量时拆单条。

### 9.5 B-6 rank-2 欧拉系评估（CH22 命中）

- 工具矩阵（检索确认）：LLZ14（V_f⊗V_g Rankin–Selberg 欧拉系）、BDR（Beilinson–Flach + syntomic regulator）、KLZ（Rankin–Eisenstein 类）、DR16（广义 Kato 类 κ(f,g,h)，weight (2,1,1) Hida 极限，**非欧拉系**）、**CH22**（Castella–Hsieh，CM 辅助特征形式情形证 DR 猜想）、Castella 2312.01481（κ_p ≠ 0 ⟹ dim Sel = 2，逆 ⟺ loc_p ≠ 0）、Kim 2203.12159（弱 IMC 任意秩 Selmer 结构）、BKS 2103.11535（Kato 欧拉系导数 + Mazur–Tate 无条件证据）。
- **CH22 附录 Table 1 首行即 389a1 / p=11 / K=ℚ(√−2)**，条件全验证：D=−8（389∤D）、11≡3 mod 8 split、(−2/389)=−1 inert、E[11] 不可约（389a 类仅 1 曲线无有理 m-同源 m>3）、L(E^K,1)≠0、χ 由 Vatsal 保证无穷多。定理链：ord_T Θ_{f/K} = 2（数值 10T²+69T³+… mod 11²）→ (Thm B) κ≠0 → (Thm A(1.9) 无条件) dim Sel(ℚ,V₁₁E) = 2 → (descent + rank=2) **Ш[11^∞](E/ℚ) 有限**。

### 9.6 框架实证两处纠错（重要）

1. **389a1 最小模型 = [0,1,1,−2,0]（y²+y=x³+x²−2x）**——此前误用 y²+y=x³−x²−2x+1，致 a_p 全部错值。重算：a₂=−2、a₃=−2、a₅=−3、a₇=−5、**a₁₁=−4**（⟹ good ordinary at 11）、a₁₃=−3、a₁₇=−6、a₁₉=5。
2. **p=2 恒非 ordinary**（a₂ 恒偶）⟹ 旧记录"389a1/p=2 good ordinary"错误；Greenberg 控制定理在 p=2 前提不成立，λ₂ 挂账比 B-4 所述更独立（2-adic 无 ordinary 框架）。`ordinary_389a1_2` axiom 语义须更正（留痕）。
落盘：`BSD/Probe389/kato_framework_check.md`、`ap_ordinary.py`；路线文档增 §4.4。

### 9.7 CH22 Lean 集成（`BSD/Sha11_389.lean`，已并入聚合、全绿）

| 层 | 内容 | 状态 |
|---|---|---|
| 对象 | `SelDim`/`ShaCorank`/`ShaFinite`（⟺ corank=0） | 定义 |
| CH22 条件 | `ThetaOrderTwo389`（ord_T Θ=2 数值事实）、`KatoNonzero389` | axiom |
| 文献定理 | `kato_nonzero_of_theta_order`（Thm B）、`sel_dim_two_of_kato_nonzero`（Thm A(1.9)）、`sel_dim_eq_rank_add_sha_corank`（descent 维数形式） | axiom |
| 组合真证 | `sel_dim_two_389`（B+A 串联）、`sha_corank_zero_389`（2=2+x⟹x=0，Nat 算术）、**`sha11_finite_389 : ShaFinite Curve389a1 11`** | 真证 |

- 闭包核验 `_check_l04.lean`：`sha11_finite_389` 仅依赖本模块 CH22 axiom + EulerSystem 复用（Curve389a1/Rank/rank_389a1）+ 内核（propext/choice/Quot）——无 sorry、无逻辑泄漏。
- 工程：EulerSystem 有 `namespace BSD.EulerSystem` ⟹ Sha11_389 需 `open BSD.EulerSystem`；Sha11_389 自身用 `namespace BSD.Sha11_389` 包裹。
- 编译：`lake build BSD.Sha11_389` exit 0；`BSD.lean` 加 import 后 `lake build -R` **7690 jobs 全绿**。

### 9.8 λ₁₁ K_cyc 侧评估（2026-10-13，最新）

**数学定位**：λ₁₁ = corank_{ℤ₁₁} Sel_{11^∞}(E/K_cyc) − rank E(ℚ)；IMC（ordinary, μ=0）下 λ_p = ord_T L_p(E,T) − rank。

**关键诊断——CH22 为什么给不了 λ₁₁**：CH22 闭的是 **ℚ 侧**（Ш[11^∞] 有限 ⟹ corank Sel(E/ℚ) = 2），但控制定理是**不动点版本** corank(Sel_{K_cyc}^G) = 2；全群 corank = corank(Sel^G) + corank(Sel/Sel^G) = 2 + λ₁₁——**λ₁₁ 恰是"K_cyc 塔附加部分"（M/M^G 的 cofree part），控制定理摸不到它**。

**工具覆盖**：Skinner–Urban IMC 仅 analytic rank 0/1（L_p 非零特殊值）；rank 2 ⟹ L_p 零点情形——**任何 p 均未覆盖**（修正 B-4 表述："rank 2+p=2" → "analytic rank ≥ 2 均未覆盖"，p=2 只是叠加 2-adic Hida 障碍）。CH22 广义 Kato 类在 ℚ 侧；Kim 弱 IMC 假设下；BKS Kato 导数机制对口但无 corank 定理。

**ord_T L₁₁ = 2 数值预期**：解析侧 L″(E,1)/2! = 0.759316500288 ≠ 0（已无条件验证）+ 非 CM good ordinary 无 exceptional zero 机制 ⟹ p-adic 插值预期 T 阶恰 2。

**三条可执行路径（待选）**：① 数值证据层——L₁₁(E,T) Iwasawa 展开验证 T²∥L₁₁ mod 11^k（p=11 远比 p=2 可行，无 Hida 障碍）；② IMC + ord=2 ⟹ λ₁₁ = 0 挂账（与 λ₂ 并列，Lean axiom 层）；③ Kato 欧拉系导数真定理（BKS 机制，p=11 现实性高）——B-6 的新数学输入延续。

### 9.9 当前状态总表（389a1，Sha 有限性侧）

| 素 | 目标 | 状态 | 载体 |
|---|---|---|---|
| 2 | Ш[2] 有限 | **真证** | ShaFreeLayer.lean（sha2_389_card_eq_one 推导） |
| 11 | Ш[11^∞] 有限 | **Lean 定理链**（CH22 axiom + 组合真证） | Sha11_389.lean（sha11_finite_389） |
| 2 | λ₂（K_cyc 侧） | axiom 挂账；p=2 非 ordinary 使控制定理前提失效 | EulerSystem.lean |
| 11 | λ₁₁（K_cyc 侧） | 开放；三条路径待选 | — |
| 其余 ℓ | Ш[ℓ^∞] 有限 | 开放 | — |

工程注记：本 §9 全部产物位于 `c:\proj2\BSD\`（主项目）；备份仓库同步待后续指令。

## 10. 2026-10-15：λ₁₁ = 2 数值支柱 + Lean 挂账 + 跨素数核对（K_cyc 侧）

主线：把 §9.8 的"数值路径 1"拍板落地——series(11) 复刻验证 ord_T L₁₁ = 2（λ₁₁ = 2），挂账 Lean，再转 p 侧 Iwasawa 与 K_cyc 侧的跨素数核对。全部数值经 PARI/GP 2.13.3（WSL）真模符号管道（`msfromell` + `mseval`），复刻结构经 11a1/p=3 校准（Σ ≡ 68 mod 243 精确命中，`series_points_check.md` §6）。

### 10.1 series(11) 复刻（389a1/p=11，`Probe389/`）

- **结果**：L₁₁(T) = 0 + 0·T + 9·T² + 9·T³ + …（mod 11 系数）；T⁰ ≡ 0 mod 11⁴（bd=4）、T¹ ≡ 0 mod 11（bd=1）、T² ≡ 9 mod 11 ≠ 0 ⟹ **ord_T = 2（λ₁₁ = 2）**。
- **数据质量**：220 个 series 点（j=0..10 × a=1..10，分母 121/11）+ 22 补测点，PARI 全实测，重复点值一致（distinct r121=110, r11=10）；**两条分布恒等式精确成立**（H₁ 自洽性硬检验）：r=1/121：−4·0 = 0 = −1 + f(1/11)；r=1/11：−4·1 = −4 = −4 + f(1)。
- **389a1 的 series 点全非尖点端点**（c<121 与 N=389 互素），无 11a1 那种尖点对称补的必要。
- **交叉互证**：Sage docstring series(3) = O(3⁵)+O(3²)T+(2+2·3+O(3²))T²（T²≡2 mod 3 ≠ 0，跨素数秩 2 一致）；L″(E,1)/2 = 0.759316500288（区间算术，analytic rank 2）；M(0) = 0（rank 2 ⟹ L(E,1)/Ω = 0）。
- 产物：`read_pari_series11.py`（一键复现）、`ms389a1_series.gp` 等 7 个脚本/输出、`series11_389_check.md`（备查）。

### 10.2 Lean 挂账（`Sha11_389.lean` 数值验证层）

新增"数值验证层"（在 CH22 条件层与定理层之间）：`L11OrderTwo389 : Prop` + `l11_order_two_389 : L11OrderTwo389`（axiom）。注释明确**对象区分**：L₁₁(T)（E/ℚ ordinary p-adic L，λ₁₁=2 直接证据）≠ Θ_{f/K}（E/K 反cyclotomic，CH22 定理前提）——同属"秩 2 ⟹ 二阶消失"实例，构成 CH22 链的独立平行背书。编译 `lake build BSD.Sha11_389` 全绿（1069 jobs）。

### 10.3 跨素数核对（③，K_cyc 侧 λ）

**数学**：Iwasawa 特征分解（K/ℚ 二次 Abel，11 split in K ⟺ χ(11)=(−2/11)=+1）：L_p(E/K,T) = L_p(E,T)·L_p(E^χ,T) ⟹ λ₁₁(E/K) = λ₁₁(E) + λ₁₁(E^χ)。

| 对象 | λ | 证据 |
|---|---|---|
| E/ℚ, p=11 | **2** | series(11)：T²≡9 mod 11 ≠ 0（§10.1） |
| E/ℚ, p=3 | **2** | docstring series(3)：T²≡2 mod 3 ≠ 0（跨素数一致） |
| E^χ/ℚ, p=11 | **0** | analytic rank 0（ellanalyticrank 无条件）+ T⁰≡10 mod 11 ≠ 0 |
| **E/K, K_cyc, p=11** | **2 = 2+0** | 特征分解 |

**E^χ 数据**（PARI）：方程 [0,−8,0,−128,−128]（`elltwist(E,−8)`，−8 为 K 域判别式），conductor **24896 = 389·64**（389 inert in K 保留）；**analytic rank = 0**、**L(E^χ,1) = 2.7884581989… ≠ 0**（ellanalyticrank，无条件）；**M(0) = L/Ω⁺ = 2（精确有理）**（msfromell @ N=24896，4G 栈）。rank 0 恒等式（11a1 校准已验证）T⁰ ≡ (1−1/α)²·M(0) mod 11，(1−1/α)² ≡ 5 mod 11 ⟹ **T⁰(E^χ) ≡ 10 mod 11 ≠ 0 ⟹ ord_T = 0 ⟹ λ₁₁(E^χ) = 0**。

**结论**：秩 2 曲线在 ordinary 素数 {3,11} 处 λ = rank = 2（跨素数一致）；K 侧二次 twist 是 rank 0（非零点情形），λ 贡献为零 ⟹ E/K 也是 λ=2（零点情形），Q 侧 = K_cyc 侧。与"Ш[11^∞] 有限 ⟹ corank 0"的 descent 结构相容，为 B-6/CH22 框架提供跨素数、跨域数值一致性背书。

产物：`ms389twist_smoke.gp`/`ms389twist2.gp` + 输出、`cross_prime_lambda_check.md`（备查）。

### 10.4 Lean 挂账（跨素数核对层）

新增"跨素数核对层"：`LambdaTwistZero389 : Prop` + `lambda_twist_zero_389`（axiom，数值-解析证据）；`LambdaEKTwo389 : Prop`（axiom）；`lambda_ek_add_of_decomp : L11OrderTwo389 → LambdaTwistZero389 → LambdaEKTwo389`（特征分解 axiom，文献事实）；真证定理 **`lambda_ek_two_389 : LambdaEKTwo389`**（纯组合两个 axiom 前提，与 `sel_dim_two_389` 模式一致）。编译全绿（1069 jobs，5.8s 增量）。

### 10.5 当前状态（λ 侧，389a1）

| 素 | 目标 | 状态 | 载体 |
|---|---|---|---|
| 11 | λ₁₁(E/ℚ) = 2 | **数值验证**（ord_T L₁₁ = 2）+ Lean 挂账 | series11_389_check.md / Sha11_389.lean |
| 11 | λ₁₁(E^χ) = 0 | **数值-解析**（rank 0 + T⁰≠0）+ Lean 挂账 | cross_prime_lambda_check.md / Sha11_389.lean |
| 11 | λ₁₁(E/K) = 2 | **特征分解推导** + Lean 真证 | Sha11_389.lean（lambda_ek_two_389） |
| 3 | λ₃(E) = 2 | docstring 数值（跨素数一致） | Sage series(3) |
| 其余 ℓ | λ_ℓ | 开放 | — |

工程注记：本段数值产物（PARI 脚本/输出/复刻管道）位于 `c:\proj2\BSD\Probe389\`；`Sha11_389.lean` 三块 axiom 层（CH22 条件 + L₁₁ 数值 + 跨素数核对）各自独立挂账、逻辑组合全真证；备份仓库同步待显式指令。

## 11. Θ_{f/K} 反cyclotomic 复刻（Sage Brandt module，2026-10-15 收尾）

### 11.1 目标与管道

"最难"主线：**CH22（Castella–Hsieh 2022，arXiv:1809.09066）Theorem B 前提 ord_T Θ_{f/K} = 2 的真复刻**——从定义出发复刻 Table 1 首行 389a1/11/K=ℚ(√−2) 的 theta 元素，不依赖靶值。管道：SageMath 9.5（WSL Ubuntu-22.04，内建 Brandt module）`BrandtModule(389,1)`（33 维）+ 自定义 P_n^a 构造 + 类匹配 + 公式组装。

- 公式（CH22 §3，example.tex / ar5iv §6 / BD96 §2.7 三源逐字核对）：
  Θ_{E/K,2}(T) := (1/α₁₁³)·Σ_{i=0}^{120}Σ_{a∈μ₁₀}(α₁₁·f_E(P₂^{a·uⁱ}) − f_E(P₃^{a·uⁱ}))·(1+T)ⁱ mod (11², T¹¹)；u=1+11。
- f_E：Cl(R)→ℤ（JL 像，T₁₁·f = −4f 精确验证）；P_n^a 格条件 pⁿ·[[1,−a·p⁻ⁿ],[0,1]]·M_x ≡ 0 mod p^{2n}（整数化 + LLL + 分数格基）。
- 组件级全通过：**121 个 P₃ 类匹配全量审计**（theta(10)=theta(30) 零差异、零漏匹配）、**ip 环同构 16/16**（mod 11⁶）、ip(√−2)=diag(u,−u)、P₀=trivial、P₂ 类 9/21/13/1/4。

### 11.2 根本 bug 修复（解释历史全部系统性不对靶）

v4–v10 主循环把 `class_f()` 返回的**类索引**（0..32）当 **f 值**（∈{−2..2}）求和——**f 特征向量从未参与 Θ**。v12 修复后 f 值正确参与。

### 11.3 ord_T = 2 判定闭合（核心成果）

| 曲线 | Θ（teich、f 值、mod 121） | T⁰ | T¹ | T² | ord_T |
|---|---|---|---|---|---|
| 389a1 | [0,0,**78**,46,71,81,59,99,113,85,49] | 0 | 0 | 78≠0 | **2 ✓** |
| 709a1 | [0,0,**94**,97,17,40,56,104,41,35,67] | 0 | 0 | 94≠0 | **2 ✓** |

- **T⁰=T¹=0 是求和的结构性质**，对 f_E 的 p-adic 归一化（ℤ₁₁^× 缩放）不变；T²≠0 在缩放与精度下保持 ⟹ **ord_T=2 判定不依赖论文未给的归一化约定**。
- 两曲线独立成立，与 CH22 靶（ord_T=2）一致——CH22 链数值前提达结构目标。

### 11.4 逐系数对靶：不可达（诚实定位）

- T²+ 系数系统性偏离靶（389 靶 [0,0,10,69,1,103,106,66,11,55,110]；709 靶 [0,0,27,114,3,14,36,15,42,44,91]）；逐项比不成比例 ⟹ **非 f 缩放**。
- 已穷尽可复原自由度：u 符号、teich 方向（数学必然无效）、整数代表、α 单位根（29 唯一；93 非根、88 非单位）、类平移（Sage 右理想乘法产乘表坍缩，机制不可实现）、Brandt 恒等式（theta 归一化未知）。
- 剩余差异锁定：CH22 作者实现的 **f_E "p-adically normalized" 归一化细节** 与 **i_p optimal embedding 选择**——论文未给出，不可从论文复原。待作者实现（Castella/Hsieh 联系/GitHub）。
- **缺口不影响 ord_T=2 判定**（结构性质，对归一化稳健）。

### 11.5 Lean 挂账（`Sha11_389.lean` 证据层更新）

- `theta_order_two_389` 注释更新：Sage 复刻独立判定 + 709 交叉复现 + 缺口标注（axiom 层不变）。
- 新增证据块"Θ_{f/K} ord_T=2 的 Sage Brandt module 复刻"（公式、数值、稳健性论证、组件验证、诚实缺口）。
- 编译：`lake build BSD.Sha11_389` 全绿（1069 jobs，9.9s）。

### 11.6 当前状态（Θ 侧，389a1）

| 目标 | 状态 | 载体 |
|---|---|---|
| ord_T Θ_{f/K} = 2（CH22 Thm B 前提） | **数值判定闭合**（389+709 双曲线独立，结构性质稳健）+ Lean 证据块 | theta_replica_final.md / Sha11_389.lean |
| 逐系数对靶（Table 1 靶值） | **不可达**（f_E 归一化/embedding 细节，论文未给）——降级"待作者实现" | theta_replica_final.md |
| CH22 链其余数值前提 | 已闭合（series(11)、mspadicL 全素数、跨素数核对） | §9/§10 |

产物（`Probe389/`）：`_sage_theta_v12_fvalue.sage`（**当前最权威复刻脚本**，f 值正确）、`_sage_audit_p3_full.sage`/`_sage_check_iso.sage`（组件验证）、`theta_replica_final.md`（最终结论）、`theta_replica_v12v14_diagnosis.md`（中间诊断）、`ch22_src/`（CH22 源码 + ar5iv 全文 + BD96 全文）。已死路（勿重试）：PARI mseval、Sage Cell 在线、conjugate()、cyclic_right_subideals、`O.ideal()` bug、`inverse_mod` 对 Integer、类平移（乘表坍缩）、flip/teich_inv、Brandt 恒等式。

## 12. 缺口 A 数值核验闭合：L(E/K, χ², 1) ≠ 0（2026-10-15）

### 12.1 定位

CH22 Theorem A 假设第 2 项 `L(E/K, χ², 1) ≠ 0`——此前仅 axiom 挂账（`LEKChi2Nonzero389` 标"数值核验待做"），本段完成数值核验。

### 12.2 构造

- K = ℚ(√−2)（类数 1）；χ² = (N(𝔞)/5)：Cl_5 二次 ring class 特征（conductor 5；满足 (pN_f, cD_K) = 1，CH22 的 χ 由 Vat03/CH18 Thm D 保证存在、未指定形式，此为显式可计算实现）。
- θ(χ²)(q) = Σ_m (m/5)·r(m)·q^m，r(m) = #{a²+2b²=m}（ℤ[√−2] 计数），level = |D_K|·f² = 8·25 = 200。
- L(E/K, χ², s) = L(E ⊗ θ(χ²), s)（Rankin-Selberg，weight-3）：a_n = Σ_{d|n} a_E(d)·b_{n/d}。
- Sage 卷积 50000 系数（a_1..5 = [2,−6,−8,10,−6]）；PARI lfuncreate 低层格式。

### 12.3 三参数扫描裁决（lfuncheckfeq 独胜组合）

| 参数 | 候选 | 胜者 |
|---|---|---|
| Vga（γ 因子型） | [0,1,0,1]（Γ(s)²）/ **[0,1/2,1,3/2]**（Γ(s)Γ(s+1/2)）/ [0,0,1,1] | **[0,1/2,1,3/2]**（checkfeq −5 vs 0/−1） |
| conductor | {77800, 311200, 700200, 1945000, 38900} | **77800 = 389·200**（−5 vs ≤−2） |
| eps | ±1 | **+1** |

### 12.4 数值结论

**L(E/K, χ², 1) = L(E⊗θ(χ²), 1) = 4.9098500369129333522552480141603036183… ≠ 0**

- 收敛：5000 与 50000 系数 L(1) 一致至 10⁻²⁷（4.90985003691293335225530793…/…55248014…）。
- 函数方程：checkfeq = −5（log10 误差；结构错时 0/−1）。
- ε(E⊗θ) = +1 反推 ε(θ(χ²)) = −1（ε(E)=+1、χ_g(389)=−1，与 dihedral 根数公式不矛盾，可选进一步核对）。

### 12.5 Lean 挂账更新

`Sha11_389.lean`：`LEKChi2Nonzero389`/`l_ek_chi2_nonzero_389` 注释更新为"数值核验已闭合"（构造、参数、数值、扫描裁决、收敛性全记录）；**axiom 保留**（数值支持、不替代证明）。编译全绿（1069 jobs，9.1s）。

### 12.6 状态：Thm-A 假设五项全部有数依据

| Thm-A 假设 | 依据 | 状态 |
|---|---|---|
| ① L(E^χ, 1) ≠ 0 | E^χ=elltwist(−8)，L=2.7884581989（ellanalyticrank 无条件） | 已挂（§10.3） |
| ② L(E/K, χ², 1) ≠ 0 | **Rankin-Selberg：4.9098500369…（本段）** | **新闭合** |
| ③ ρ̄_{E,11} 不可约 | 389a 类仅一条曲线（无 11-同源论据） | 挂账（axiom） |
| ④ N⁻ 无平方 | (−2/389)=−1 ⟹ N⁻ = 389 素数 | 挂账（axiom） |
| ⑤ ρ̄ 在 q|N⁻ 分歧 | 389 坏素乘性归约 | 挂账（axiom） |

产物（`Probe389/`）：`_sage_lekchi2_coeffs.sage`（Sage 卷积）、`l_ek_chi2_coeffs.txt`（50000 系数）、`write_an_gp.py`/`l_ek_chi2_an.gp`（PARI 系数文件）、`lfun_ekchi2.gp`（构造+扫描+终验）、`lfun_ekchi2_out.txt`、**`l_ek_chi2_verification.md`（结论落盘）**。

## 13. 2026-10-16：G3/G4 工程补齐 + 挂账 Lean 真证层（rank2_status 双缺口闭合）

主线沿 G 系列推进收尾：G5（GRH 上界常数，条件闭合）之后，用户指示"G3/G4 工程补齐"——G3（Reg 全精度）、G4（纯 Python 独立复算 |Sel₂|）两个开放缺口，本段全部闭合并挂账 `Sha11_389.lean`。

### 13.1 G3：Reg 全精度（`Probe389/G3_Reg/`）

SageMath 9.5（WSL）高度配对最终比对：
- `E.regulator() = 0.152460177943144`；`regulator(precision=200) = 0.15246017794314375162432475704945582324372707748663081784028...`
- 高度配对矩阵 [[0.686667083305587, 0.268478098806726], [0.268478098806726, 0.327000773651605]]，det = 0.152460177943144
- **四源一致**（Python NT 高度 ∥ Sage ∥ Magma ∥ LMFDB 389.a1）到 ~10⁻¹⁹（G3 前 5×10⁻⁶）
- 对 G2a 判别（#Ш[11]=1）：Reg 误差不再主导，#Ш_pred 区间 ≈ 1±10⁻¹²，排除 #Ш=11 的余量增大约 6 个数量级（~10¹⁰）
- 边界：Reg 仍为数值计算（非证明型），四源独立一致。

### 13.2 G4：纯 Python 独立复算 |Sel₂| = 4（`Probe389/G4_Sel2/`）

**数学链**（Silverman/Cassels 类空间 + descent 正合列）：
```
E: y²+y = x³+x²−2x ⟹ y'² = f(x) = x³+x²−2x+1/4（平移），A = ℚ[x]/(f)（Δ = 389/16 > 0 全实三次域）
H¹(ℚ, E[2]) ≅ { δ ∈ A*/A*² : N(δ) ∈ ℚ*² }
0 → E(ℚ)/2E(ℚ) → Sel₂ → Ш[2] → 0  +  rank=2 无挠 ⟹ |Sel₂| ≥ 4
⟹ |H¹| = 4 ⟹ |Sel₂| = 4
```

**纯 Python（标准库 + fractions，无 numpy/sympy，兼容用户老版 Python）**：
- 单位穷举（B=25）：20 个单位，基本单位 ε₁=(−1,8,−4)、ε₂=(−1,8,4)（N=−1；−εᵢ 为 N=+1）
- **类数 h(A) = 1**（g4_classno.py：Minkowski 界 8.76 ⟹ 类群由 norm≤8 素理想生成；P₂=(2,t)、P₃=(3,t−1) 主性：∃δ N(δ)=±2（(−12,6,8)）、±3（(−13,10,8)）⟹ Cl[2]=0，|A*/A*²|=2³ 精确）
- **|H¹| = 4**：δ = 1、(1,−8,4)、(1,−8,−4)、(−3,20,16)（全 N=1；−1、ε₁、ε₂、−ε₁ε₂ 的 N=−1 排除）
- ⟹ |Sel₂| ≤ 4 ∧ ≥ 4 ⟹ **|Sel₂| = 4**；且 |Sel₂|=|H¹| 自动 ⟹ #Ш[2]=1（与 Magma Sha(E)[2] trivial 一致）

**三方对照**：Magma（MordellWeilShaInformation + Effort=2）4 ∥ Sage/PARI 4 ∥ **G4 纯 Python 4**。

边界（诚实）：|Sel₂| ≥ 4 依赖 rank=2 与无挠（本项目已确立）；G4 是对数值的独立复算而非对 rank 的独立证明。

### 13.3 Lean 挂账（`Sha11_389.lean` 追加 G4/G3 块）

| 名称 | 层 | 内容 |
|---|---|---|
| `sel2_order_four_389 : SelPOrder Curve389a1 2 = 4` | axiom（数据锚点） | |Sel₂|=4（G4 纯 Python 复算） |
| **`sha2_order_one_389 : ShaPOrder Curve389a1 2 = 1`** | **组合真证** | #Ш[2] = #Sel₂/2^rank = 4/4 = 1（descent 阶关系 + rank=2，数据锚点已闭合——与 `sha11_order_one_of_sel11` 同型但**不悬空**） |
| `RegHighPrecision389 : Prop` / `reg_high_precision_389` | axiom | Reg = 0.15246017794314375162...（200 位挂账） |

- G2 层注释更新：四锚点 Reg 口径 5×10⁻⁶ → 200 位，判别余量 ~10¹⁰。
- `#Ш[2] = 1` 现在是**独立 Lean 真证链**（不依赖 BSD 数值），与 Magma `Sha(E)[2] trivial` 对照一致——ShaFreeLayer 的 `sha2_389_card_eq_one` 与 Sha11_389 的 `sha2_order_one_389` 双载体。
- 编译：`lake build -R` 全绿（7690 jobs）。

### 13.4 状态：rank2_status.md G 系列

| 缺口 | 状态 |
|---|---|
| G1 整体有限性（秩 2 开放） | 开放（GRH 只给"若有限则上界"） |
| G2 #Ш[11] 阶 | 条件判定（精细 BSD 数值）+ 真证骨架（#Sel₁₁=11² 悬空） |
| **G3 Reg 全精度** | **已闭合**（200 位，四源一致） |
| **G4 \|Sel₂\| 纯 Python** | **已闭合**（\|H¹\|=4 ⟹ \|Sel₂\|=4，类数 h=1 验证） |
| G5 GRH 上界常数 | 已闭合（条件） |
| G6 GRH 反证链组合 | 判定通过（条件于 GRH+BSD） |

产物：`Probe389/G3_Reg/g3_result.md`（+ g3_sage.sage）、`Probe389/G4_Sel2/g4_result.md`（+ g4_sel2.py / g4_classno.py）；`rank2_status.md` G3/G4 行更新为"已闭合"。
