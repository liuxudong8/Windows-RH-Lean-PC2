# λ_p = 0 与几乎处处平凡：从 Rank-1 欧拉系的延伸路线

日期：2026-10-13
状态：**路线确立 · 阶段 A 已闭合（389a1, p=2 免费层）· 阶段 B 起为开放项（axiom 锚点或新输入）**
关联：`Probe389/sha_crosscheck.md`、`Probe389/sel2_final.py`（|Sel₂|=4 三次域复算）、`SymmetryFormula4.lean`

---

## 0. 判词（上一轮结论的固化）

Poitou–Tate 免费机器已给出：∀p,∀n：|Ш[pⁿ]| < ∞、Cassels 配对非退化（|Ш[pⁿ]| 是平方）、奇偶约束（下界型）。整体有限的两个关键步恰在测量范围之外：

- **缺口 (i)**：p-秩有界 ⟺ Iwasawa 不变量 λ_p = 0（K_cyc 上 Sel_{p^∞} 的 corank = rank）。
- **缺口 (ii)**：除有限个 p 外 Ш[p] = 0 —— 等价于解析 p-部分 BSD（L-值整除性），无免费机制。

本文件把"Rank-1 欧拉系 → 这两个缺口"的延伸写成可执行的分阶段步骤。

## 1. 数学基础与符号

- descent 正合列（任意 p，任意 n）：`0 → E(K)/pⁿ → Sel_{pⁿ}(E/K) → Ш[pⁿ] → 0`。
- Ш = ⊕_p Ш[p^∞]（H¹(K,E) = ∪_n H¹(K,E[n]) 的元素皆挠元 ⟹ p-分量分解免费）。
- **Ш 有限 ⟺ (i) 每 p：dim_{𝔽_p} Ш[pⁿ] 有界（n 无关）∧ (ii) 除有限个 p 外 Ш[p] = 0**。
- Iwasawa：K_cyc = K 的 cyclotomic ℤ_p-扩张；corank_{ℤ_p} Sel_{p^∞}(E/K_cyc) = rank E(K) + λ_p（Greenberg 控制定理；需 ordinary + E[p] 的 K_cyc-不变量平凡）。
- 欧拉系：rank 1 的 Heegner/Kolyvagin 欧拉系 → 素数下降给 |Ш[p]| 的显式界；Kato/Beilinson–Flach → Iwasawa corank 的界（λ_p = 0 型）。

## 2. 分阶段步骤

### 阶段 A：免费层闭合（p-分量结构引理）—— 已真，形式化收尾

**引理 A.1（p-群结构）**：对任何挠群 G 与素数 p：`G[p] = 0 ⟹ G[p^∞] = 0`。
证明：若 G[p^∞] 有非零元素，取阶最小的 x（p-幂阶）；则 px 阶更小，由最小性 px = 0，故 x ∈ G[p] = 0，矛盾。∎

**推论 A.2**：`Ш[p] = 0 ⟹ Ш[p^∞](E/K) = 0`。

**实例 A.3（389a1, p=2，已完成）**：
|Sel₂(389a1)| = 4 = 2^{rank 2}（三次域复算，Magma 一致）⟹ |Ш[2]| = 1 ⟹ **Ш[2^∞](E/K) = 0**（A.2）⟹ corank_{ℤ₂} Sel_{2^∞}(E/K) = 2。

**边界（必须写明，否则掩盖缺口）**：A.3 **不**给 λ_2 = 0。λ_2 是 K_cyc 上的量：控制定理给出 corank_{ℤ₂} Sel_{2^∞}(E/K_cyc) = 2 + λ_2；K_cyc 上无增长（λ_2 = 0）是**独立的开放项**（见阶段 C）。

**验收**：A.1 在 Lean 中真证（mathlib：挠群、p-分量、最小阶元素）；A.3 的闭合链写入本文件 §4。

### 阶段 B：欧拉系从 Rank-1 延伸到 Iwasawa（Kato 型）

**机制**（已知结果的延伸逻辑）：
- rank 1：Kolyvagin 下降 —— 对 Kolyvagin 素数 ℓ，欧拉系 c_ℓ 给出 Ш[p] 生成元数的上界（|Ш[p]| ≤ p^k）。
- 一般：Kato 欧拉系（z_K ∈ H¹(ℚ, T_p)，来自 Siegel 单位）—— 若 z_K 的像非零（等价于 L_p(E,·) 的某特殊值非零），则控制 Sel_{p^∞}(E/ℚ_∞) 的 corank ≤ rank ⟹ **λ_p = 0 型界**。这是"rank-1 工具延伸"的真正数学内容：从"Ш[p] 的界"升级为"Iwasawa corank 的界"。

**实例化（389a1）**：
- Kolyvagin bound = (0,0)（已核：rank 2 无欧拉系支撑）——**欧拉系在 rank 2 的盲区是本路线的硬限制**。
- Beilinson–Flach（Lei–Loeffler–Zerbes）对 GL₂×GL₂ 的 Rankin–Selberg 卷积给 rank 0/1；rank 2 开放。

**验收**：把"欧拉系存在（某 p）⟹ Ш[p^∞] 有界 / λ_p = 0"的陈述作为 axiom 锚点挂入 Lean 骨架（参照 Probe389 的 14-axiom 模式）；rank-1 的 Kolyvagin 下降真证部分留作 mathlib 后续。

### 阶段 C：λ_p = 0 的判定（Iwasawa 侧）

**机制**：λ_p = 0 ⟺ Sel_{p^∞}(E/K_cyc) 的 corank = rank ⟺ Iwasawa 特征理想的首项度 = 0（主猜想：χ(E/K_cyc) 由 p-进 L 函数 L_p 生成；L_p 为**单位** ⟺ λ_p = 0）。

**三条途径**（可行性递减）：
1. **axiom 锚点**：λ_p = 0（389a1, p=2）——已知结果未覆盖（Skinner–Urban 覆盖 analytic rank 0/1 的 ordinary 情形；p=2 有 2-adic 困难；rank 2 未覆盖），作 axiom 挂 Lean。
2. **数值探测**：对有限 n 算 |Sel_{2ⁿ}|（4-descent、8-descent……）验证 |Ш[2ⁿ]| = 1 恒成立 —— 这是 Ш[2^∞](E/K) = 0 的数值证据（A.3 已给 n=1；n≥2 是工程量）。
3. **解析交叉**：L_p(E,·) 的单位性数值检验（2-adic 插值）——高成本，低优先。

**验收**：axiom 声明 + 阶段 B/C 的依赖图入 Lean 骨架。

### 阶段 D：几乎处处平凡（缺口 (ii)）

**机制**：除有限个 p 外 Ш[p] = 0 无免费机制；等价于解析 p-部分 BSD（|Ш[p]| 的 p-阶 = L 值的 p-adic 整除性）。结构性免费部分仅：E(K)[p] = 0 对几乎所有 p（E(K) 有限生成）——但与 Ш[p] 无关。

**实例化（389a1）**：BSD 预测 |Ш| = 1（analytic）⟹ 期望 Ш[p] = 0 ∀p。数值验证有限个小 p（3-descent / 5-descent）可行但非必要；解析 p-部分 BSD 作 axiom。

**验收**：axiom 声明（解析 p-部分 BSD ⟹ 几乎处处平凡）；与 |Ш|=1 锚点（sha_crosscheck）交叉记录。

### 阶段 E：Lean 集成与对接

- **真证层**：A.1（p-分量引理）、descent 正合列、Cassels 配对（mathlib 有限群/对偶基元）。
- **axiom 层**：λ_p = 0（389a1, p=2）、欧拉系延伸（rank 2 的 Beilinson–Flach 型）、解析 p-部分 BSD。
- **对接**：BSD.SymmetryFormula4（公式 (4) 奇偶性）、BSD.Probe389.Probe389（axiom 模式复用）。
- **验收**：`lake build -R` 全绿（沿用 c:\proj2 工作区）。

## 3. 依赖图与可行性标注

```
阶段 A（免费/已真）────────────┐
    │ A.1, A.3: Ш[2^∞](E/K)=0   │
阶段 B（欧拉系延伸, axiom/开放）─┤
    │ Kolyvagin rank1→Kato corank│
阶段 C（λ_p=0, axiom/开放）──────┤──→ 缺口(i) 闭合
    │ 主猜想 L_p 单位性          │
阶段 D（几乎处处, axiom/解析BSD）┤──→ 缺口(ii) 闭合
    │ p-部分BSD ⟹ 有限多非平凡   │
阶段 E（Lean 集成）──────────────┘──→ Ш 有限（形式化骨架）
```

## 4. 第一步执行记录（2026-10-13 本轮）

**阶段 A 闭合（389a1, p=2）**：

| 链节 | 依据 | 状态 |
|---|---|---|
| \|Sel₂(389a1)\| = 4 | 三次域复算 `sel2_final.py`（β²≡1 去重 16→8 类；p=2∧p=389∧∞ 判定），与 Magma "2-Selmer rank 2" 一致 | 已证 |
| E(389a1)(ℚ) 秩 2、无 torsion | LMFDB / 生成元 (0,0),(1,0) | 已核 |
| \|E(ℚ)/2\| = 2^rank = 4 | descent 正合列 | 已证 |
| \|Ш[2]\| = 1 | \|Sel₂\|/\|E(ℚ)/2\| = 1 | 已证 |
| **Ш[2^∞](E/K) = 0** | 引理 A.1（p-群最小阶元素论证） | **已证（免费）** |
| corank_{ℤ₂} Sel_{2^∞}(E/K) = 2 | 0→E(K)/2^∞→Sel_{2^∞}→Ш[2^∞]→0 | 已证 |
| λ_2 = 0（K_cyc 侧） | 控制定理 corank = 2 + λ_2 —— **不**由上行推出 | **开放（阶段 C）** |

**结论**：p=2 的"单层平凡 ⟹ 全层平凡"在 389a1 上免费闭合；λ_2 = 0 的 K_cyc 增长是独立开放项，挂阶段 C 的 axiom/数值探测。

### 4.1 阶段 A 形式化（Lean 引理 A.1，2026-10-13 已完成）

**模块**：`BSD.ShaPComponent`（`C:\proj2\BSD\ShaPComponent.lean`，已并入 `C:\proj2\BSD.lean` 聚合）。

- `pPrimaryComponent A p`：p-准素子群定义（`∃ n, pⁿ•x = 0`，AddSubgroup，零/加/负封闭真证）。
- `mem_pPrimaryComponent_iff`：成员条件（`@[simp]`）。
- **`pPrimaryComponent_eq_bot_of_torsionBy_eq_bot`（引理 A.1 真证）**：
  `AddSubgroup.torsionBy A p = ⊥ → pPrimaryComponent A p = ⊥`。
  证明：最小 p-幂阶论证（Nat.find 取最小 n；y = p^(n−1)•x 非零且 p•y = 0 ⟹ y ∈ A[p] = ⊥，矛盾）。
- **闭包核验**（`_check_l01.lean`）：`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`（Lean 内核公理），**无 BSD axiom、无 sorry**——纯群论真证。
- **构建**：`lake build -R` 全绿（7690 jobs，含新模块）。

**数学语义（descent 层应用）**：Ш[p] = 0 ⟹ Ш[p^∞](E/K) = 0。389a1/p=2 实例：
|Sel₂| = 4 = 2^rank（Probe389 三次域复算）⟹ |Ш[2]| = 1 ⟹ **Ш[2^∞](E/K) = 0**（A.1）。
（λ_2 = 0 的 K_cyc 侧仍开放，见阶段 C。）

### 4.2 剩余免费层项形式化（2026-10-13 已完成）

**模块**：`BSD.ShaFreeLayer`（`C:\proj2\BSD\ShaFreeLayer.lean`，已并入 `BSD.lean` 聚合）。

**descent 正合列（真证）**：
- `card_eq_mul_of_short_exact_add`：0 →+ A --f--> B --g--> C →+ 0（f 单、g 满、
  range f = ker g）⟹ **Nat.card B = Nat.card A · Nat.card C**。
  证明：ker g 的 Lagrange 分解（`card_mul_index`）+ 第一同构 B/ker g ≃ range g = C
  （`quotientKerEquivRange` + `range_eq_top`）+ f 单 ⟹ range f ≃ A（`ofInjective`）。
  → 可计算层核心：|Ш[pⁿ]| = |Sel_{pⁿ}| / |E(K)/pⁿE(K)|。

**Cassels 配对（结构真证 + 平方挂账）**：
- `AlternatingPairing`：交错双线性配对 b : G×G → T（`toFun_zero_left/right`、
  `toFun_neg_left/right` 真证）。
- `Nondegenerate` + `leftHom` + `pairingHom`（G →+ Hom(G,T)）+
  **`injective_of_nondegenerate`（真证）**：非退化 ⟹ 诱导同态单射。
- `card_square_of_nondegenerate_alternating`（**axiom 挂账**）：非退化交错配对 ⟹
  |G| 是平方。经典证明 = Sylow 分解 + 双曲分解归纳 |G| = |⟨x⟩|²·|⟨x⟩^⊥/⟨x⟩|；
  完整真证列为阶段 E 后续工程项。

**389a1/p=2 实例（数值 axiom + 真证推导）**：
- `sha2_389_card_eq_one`：**|Ш[2]| = 1**。descent 基数（真证）+ 数值 axiom
  （|Sel₂| = 4 = |E(K)/2E(K)|，Probe389 三次域复算 + LMFDB）。
- 与 A.1 组合：|Ш[2]| = 1 ⟹ Ш[2^∞](E/K) = 0（389a1/p=2 闭合链完整落地 Lean）。

**闭包核验**（`_check_l02.lean`）：`card_eq_mul_of_short_exact_add`、
`injective_of_nondegenerate` 仅依赖 Lean 内核公理（无 axiom、无 sorry）；
`sha2_389_card_eq_one` 依赖实例层挂账 axiom（类型/数值/descent 映射，设计如此）。

### 4.3 阶段 B：欧拉系延伸——定义与分解（2026-10-13 本轮）

**B 的目标命题（λ_p = 0 的欧拉系判据）**：设 E/ℚ 模曲线，p 素数，E ordinary at p。
若存在满足 norm 相容性与非零性的欧拉系（rank 1 的 Kolyvagin/Heegner，或 Kato z_K），则
**corank_{ℤ_p} Sel_{p^∞}(E/K_cyc) = rank_ℤ E(K)，即 λ_p(E/K) = 0**。

**分解 B-0..B-6（依赖序）**：

| 步 | 内容 | 输入 | 输出 | 状态 |
|---|---|---|---|---|
| B-0 | 对象与不变量：Corank、Rank、Lambda；Greenberg 控制定理 corank = rank + λ_p | 定义 | 不变量 + 控制定理 | axiom（数学已核：ordinary + E[p] K_cyc-平凡） |
| B-1 | 欧拉系公理化：Kolyvagin 素数集 𝒫 上的族 {c_ℓ}、norm 相容、可除性 | B-0 | 欧拉系类型 | axiom（Rubin/Howard 框架） |
| B-2 | Kolyvagin 下降（rank 1）：欧拉系 ⟹ \|Ш[p]\| ≤ p^k | B-1 | 界 | axiom（Rubin 1991 / Howard 2004；389a1 盲区核验） |
| B-3 | Kato 型 corank 界：ordinary + z_K ≠ 0 ⟹ corank ≤ rank | B-0 | λ_p=0（rank ≤ 1） | axiom（Kato 2004；389a1 盲区核验） |
| B-4 | 389a1/p=2：λ_2 = 0 锚点 | — | λ_2=0 | axiom（Skinner–Urban 未覆盖 rank 2/p=2） |
| B-5 | Lean 骨架 + 组合真证（控制定理 + Kato 界 ⟹ λ_p=0） | B-0..B-3 | 组合定理 | **本轮完成** |
| B-6 | 后续：rank 2 欧拉系新输入（Beilinson–Flach 高层 / p-adic families） | — | B-3 升级为定理 | 开放 |

**组合真证（B-5，`BSD/EulerSystem.lean`）**：
- `lambda_zero_of_kato`：控制定理（axiom B-0）+ Kato 界 corank ≤ rank（axiom B-3）
  ⟹ **λ_p = 0**（真证：Rank + λ_p ≤ Rank ⟹ λ_p = 0，Nat 算术）。
- `lambda_zero_iff_corank_eq_rank`：控制定理下 λ_p = 0 ⟺ corank = rank（等价判据骨架，
  阶段 C 判定标准）。
- 闭包核验：组合逻辑真证，数学前提为本模块 axiom（欧拉系理论无 mathlib 基础：
  无 Tate 模 / H¹ / Kummer 映射）。

**盲区核验（B-2/B-3 对 389a1）**：
- rank 2 ⟹ Kolyvagin 界平凡（`kolyvagin_rank2_blind_389a1`：无 rank-1 欧拉系）。
- rank 2 ⟹ L(E,1) = 0 ⟹ Kato z_K 强条件不满足（corank ≤ rank 平凡）。
- ⟹ λ_2 = 0 无欧拉系支撑（B-4 直接挂账 axiom）。

**Lean**：`BSD/EulerSystem.lean`（axiom 锚点 + 组合真证），`lake build -R` 全绿（7690 jobs）。

### 4.4 框架实证：广义 Kato 类 ⟹ Ш[11^∞](389a1) 有限（2026-10-13）

B-6 评估落地：rank 2 欧拉系谱系（BDR/Beilinson–Flach/广义 Kato 类）给的是 **ℚ 侧** corank 上界，
不直接给 λ_p（K_cyc 侧），但直接给每素数 p 的 **Ш[p^∞] 有限性**——Sha 有限性的 p-侧闭合。

**CH22（Castella–Hsieh, Forum Math. Sigma 10:e12）对 389a1 完整覆盖**（附录 Table 1 首行即 389a1）：
p = 11（a₁₁ = −4 ≠ 0 mod 11，good ordinary）、K = ℚ(√−2)（11 split、389 inert）、E[11] 不可约、
L(E^K,1) ≠ 0、ord_T Θ_{f/K} = 2（数值：10T²+69T³+… mod 11²）。
定理链：**ord_T Θ = 2 ⟹ κ_{α,α⁻¹} ≠ 0（Thm B）⟹ dim Sel(ℚ,V₁₁E) = 2（Thm A (1.9)，无条件）⟹ Ш[11^∞](E/ℚ) 有限**。

**纠错记录**：① 389a1 最小模型 = y²+y = x³+x²−2x（[0,1,1,−2,0]），先前误用另一方程致 a_p 错值；
② p=2 恒非 ordinary（a₂ 恒偶），"389a1/p=2 good ordinary"旧记录有误——λ₂ 挂账比 B-4 所述更独立。
详见 `BSD/Probe389/kato_framework_check.md`、`BSD/Probe389/ap_ordinary.py`。

**Lean 集成（已并入 BSD 库，全绿）**：`BSD/Sha11_389.lean`（namespace BSD.Sha11_389）——
axiom 层：`SelDim`/`ShaCorank`/`ShaFinite` 对象 + CH22 条件（`ThetaOrderTwo389` 数值事实、
`KatoNonzero389`）+ 文献定理（`kato_nonzero_of_theta_order`＝Thm B、
`sel_dim_two_of_kato_nonzero`＝Thm A(1.9)、`sel_dim_eq_rank_add_sha_corank`＝descent 维数形式）；
组合真证：`sel_dim_two_389`（Thm B+A 串联）、`sha_corank_zero_389`（2=2+x⟹x=0，Nat 算术）、
**`sha11_finite_389 : ShaFinite Curve389a1 11`**（目标定理）。
闭包核验 `_check_l04.lean`：仅依赖本模块 CH22 axiom + EulerSystem 复用（Curve389a1/Rank/rank_389a1），
无 sorry、无逻辑泄漏。已并入顶层 `BSD.lean` 聚合，`lake build -R` 7690 jobs 全绿。

## 5. 后续步（按序执行）

1. **阶段 A 形式化**：引理 A.1（真证）＋ descent 基数（真证）＋ Cassels 配对结构（真证）
   ＋ 389a1/p=2 闭合链实例。—— **已完成（2026-10-13）**；
   剩余：Cassels 平方结论的完整真证（双曲分解归纳，阶段 E 项）。
2. **阶段 C-2 数值探测**（可选，工程量级）：4-descent 算 \|Sel₄\|，验证 \|Ш[4]\| = 1（预期）。
3. **阶段 B/C axiom 锚点**：λ_p = 0、欧拉系延伸陈述挂入 Lean 骨架。
4. **阶段 D axiom**：解析 p-部分 BSD 陈述。
5. **阶段 E**：`lake build -R` 全绿。
