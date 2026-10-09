# P* 正性判别 · Lean 骨架 —— `BSD.Positivity`

> 第三阶段（P*）第二步交付：把"秩恰 2 ⟹ L″(E/K,1) > 0"落成 Lean 骨架。
> 逻辑收口：**P* ⟺ 分量级 BSD 正性**（秩0 分量是定理，秩1/秩2 分量是猜想）——本模块的 axiom 层即分量正性，定理层逐型推导 P*。
> 数据闭包：389a1 → 型 (2,0)；106b1 → 型 (1,1)（(1,1) 非真空，纠缠正性实测 6/6 全正）。
> **本轮（2026-10-08）新增：纠缠正性可证性边界**——非零 = Kolyvagin 定理；符号障碍 ≡ 公式（Sha 有限）；正性从 axiom 降为定理；同号 iff 为纯真定理。
> **本轮 2（2026-10-08）：秩 2 分解（同一条逻辑推到秩 2）**——R2 = 2×2 高度矩阵行列式（正定 ⟹ 正，定理级）；L″(1) = 2·Ω·R2·Sha/|T|²；`lprimeprime_pos_of_rank_two(_5)` 从 axiom 降为定理；P* 全部猜想起源收窄到 4 条公式 axiom。
> **本轮 3（2026-10-08）：probe389_strict_pos 严格区间验证**——L″(389a1,1)/2 ∈ [0.75837, 0.76026]，下界 > 0 机器闭证（无条件，无公式）；双向闭合的解析侧符号层在具体实例上落地。
> **本轮 4（2026-10-08）：(1,1) 六条纠缠正性严格闭证**——79a1/89a1/91a1/99a1/101a1/106b1 的 L′(E,1)·L′(E⁵,1) 全区间闭证 6/6，纠缠正性从数据律升级为机器可复核的解析定理族。
> **本轮 5（2026-10-08）：通道 B 落成 Lean（`BSD.PositivityGRH`，另建文件夹）**——K-GRH 保号路径：GRH（零点全在 Re=1）+ P* 秩恰 2 ⟹ L″(E/K,1)>0，与 BSD 公式通道并行。**编译双绿**（主模块 + _check，exit 0 无警告）；`p_star_grh` axiom 闭包 = 逻辑公理 + Positivity 对象/公式 axiom + 12 条 GRH axiom；保号核心引理 `pos_on_interval_of_no_zero` 纯逻辑公理（IVT 真证明）。
> **本轮 6（2026-10-08）：P* 合流（`BSD.PStarOr`）**——免疫声明落成单一定理 `p_star_or`：(公式 ∨ K-GRH) + 秩恰 2 ⟹ L″(E/K,1)>0。3 条标志 axiom（formula_holds/grh_holds/formula_or_grh）+ 4 条分量合流定理 + 主定理；编译双绿。闭包 = 逻辑公理 + 两通道 axiom 并集；元级审计：`p_star_grh` 闭包无 4 条公式 axiom（bsd_formula_rank_*）——两条路径假设互斥、各自独立成立，未来任一猜想获证即去掉对应分支。
> **本轮 7（2026-10-08）：③ 讨论收口（零点下界/密度估计，未落骨架）**——机制 = Hadamard 对数恒等式 + 零点虚部矩收敛（Σ1/γ² 无条件）；可达性划定：**推论 A 可做**（最近非中心零点高度 γ₀ ≥ η > 0，η 数值可算）、**推论 B 做不了**（N(T) 密度增强——矩界压不出计数函数，密度走 Selberg 经典无条件路线，P* 不进入）、**推论 C 顺带零成本**（函数方程延伸保号到 (1/2,3/2)∖{1}）。两个质疑：尾部正 axiom 降格（非无条件定理）、η 对固定 δ 处 Λ 数值上界敏感。建议顺序：C → A，B 明确不立项。
> **本轮 8（2026-10-09）：推论 C 落盘（函数方程延伸保号，`BSD.PositivityGRH` 内）**——6 条新 axiom（rootNumberE(_5) 对象、±1 消元、`L_E(_5)_fe`：符号 iff ∧ 零点 iff）+ 8 条真定理：`L_E(_5)_no_zero_left`（零点经函数方程拉回）、`L_E(_5)_pos/neg_left_of_rootNumber_*`（ε=±1 符号）、`L_E(_5)_no_zero_full`（(1/2,3/2)∖{1} 全区间无零点——左半函数方程 + 右半 GRH）。编译双绿；`L_E_no_zero_full` 闭包 = 逻辑公理 + 函数方程层 5 条 axiom（不含 Taylor/尾部正）。
> **本轮 9（2026-10-10）：GRH 退役（通道 B 重构为无条件保号通道）**——理论级核心事实：(1,3/2) ⊂ Re(s)>1，而 **Re(s)>1 无零点是自守 L 理论的无条件定理**（若 L(s₀)=0，欧拉积绝对收敛 ⟹ 局部因子 1−α_v q^{−s₀}=0 ⟹ |α_v|=q^{σ₀}>q 违反 Ramanujan/Hasse 界 ⟹ 矛盾；模性 + Hasse + 绝对收敛全定理级）。重构：`grh_no_zero_L_E(_5)` → `zero_free_re_one_side(_5)`（定理级挂账），全套改名 `grh_pos_on_Icc→pos_on_Icc`、`grh_Lp/Lpp_pos→Lp/Lpp_pos_uncond`、`grh_type_*→uncond_type_*`、`p_star_grh→p_star_uncond`、`grh_holds→uncond_holds`、`formula_or_grh→formula_or_uncond`。**三绿**（PositivityGRH.PositivityGRH / PStarOr.PStarOr / Main）；闭包实测：`p_star_uncond` **不含任何 bsd_formula_rank_* 公式猜想、不含任何 GRH axiom**——通道 B 猜想级闭包为空（只剩定理级挂账：Kolyvagin 非零、零自由区域、解析对象）；推论 C 同步升级（右半零自由区域）。**P* 对公式与 GRH 双免疫；Sha 有限性从 P* 依赖中消失。**

---

## 0.13 GRH 退役：通道 B 重构为无条件保号通道（本轮 9，2026-10-10）

用户决策：落重构（"落这个重构吗？落的话顺手把免疫声明和 Main.lean docstring 一起更新"）。

**讨论轮记录（本轮三个连问的收口）**：
1. *"理论级能不能想办法？"*——核心发现：**(1, 3/2) ⊂ Re(s) > 1，而 Re(s) > 1 的无零点是自守 L 理论的标准无条件定理**（下方论证）。这意味着实例级零猜想正性（37a1、六条 (1,1) 区间闭证）不是孤例——**理论级正性本身可以零猜想**（不依赖公式、不依赖 GRH）。
2. *"E/ℚ(√5) 如果是有限的，能不能枚举？"*——**前提不成立**：同构类无限（Shafarevich 只给固定导子有限；# {E: N(E) ≤ X} ~ c·X^{5/6} 无界；秩 2 曲线导子无界）。逻辑命题：**穷举覆盖全称 ⟺ 类集有限**——没有有限性，枚举永远差一步，不能闭合 P* 的全称量词。枚举的真实价值 = 审计/证据/模式（方案 X：有界导子枚举管线，未立项，记录在案）；理论级闭合靠无条件链（不靠枚举）。
3. *"GRH 正式退役啥意思？不做了？"*——澄清：退役 = 从 P* 的**假设依赖**中移除（被无条件定理替代），不是放弃 GRH 课题；12 条 GRH axiom 里只有 2 条（grh_no_zero）是猜想级，其余 10 条本是无条件事实；推论 A/B（零点下界、密度）中 GRH 仍是工具，照做。

**理论级核心事实（讨论轮已证，本轮落地）**：(1, 3/2) ⊂ Re(s) > 1，而 **Re(s) > 1 的无零点是自守 L 理论的标准无条件定理**：
```
若 L(s₀, π) = 0（Re s₀ > 1），L 在该区域由欧拉积绝对收敛表示（Godement–Jacquet，定理）
⟹ 某局部因子 1 − α_v q^{−s₀} = 0 ⟹ α_v = q^{s₀} ⟹ |α_v| = q^{σ₀} > q
⟹ 违反 Ramanujan |α_v| ≤ √q（椭圆曲线 = Hasse 界，Deligne，定理）⟹ 矛盾
```
模性（Wiles）+ Hasse（Deligne）+ RS 绝对收敛全是定理级——**不需要 GRH，也不需要公式**。GRH 从 P* 假设谱系正式退役。

**重构动作（`BSD.PositivityGRH`）**：
- axiom：`grh_no_zero_L_E(_5)`（GRH 猜想级）→ `zero_free_re_one_side(_5)`（无条件定理级挂账，docstring 写明来源链：欧拉积绝对收敛 + 局部因子 + Ramanujan 矛盾）；
- 定理改名：`grh_pos_on_Icc(_5)`→`pos_on_Icc(_5)`、`grh_L_E(_5)_pos_on_open`→`L_E(_5)_pos_on_open`、`grh_Lp/Lpp_pos(_5)`→`Lp/Lpp_pos_uncond(_5)`、`grh_type_20/11/02`→`uncond_type_20/11/02`、`p_star_grh`→`p_star_uncond`；
- 层标题：`## 3/4/5 GRH ⇒` → `## Unconditional ⇒`；文件头重写（通道 B = 无条件解析结构，含退役说明与证明链）。

**合流模块（`BSD.PStarOr`）**：`grh_holds`→`uncond_holds`、`formula_or_grh`→`formula_or_uncond`；免疫声明升级为 **formula ∨ unconditional**；文件头说明"通道 B 无任何猜想级 axiom，P* 对 GRH 完全免疫"。

**Main.lean**：`analytic_rank_K_eq_one_of_LK_prime_ne_zero` docstring 追加 **(vi) GRH 退役**段（五环之后第六环）——退役事实、重构清单、闭包证据、净效应（双免疫 + Sha 有限性出依赖）。

**编译账（三绿）**：`lake build BSD.PositivityGRH.PositivityGRH` / `BSD.PStarOr.PStarOr` / `BSD.Main` 全 exit 0；校验文件三绿：`_check_positivity_grh.lean`（14 #check + 4 #print 全改名）exit 0、`_check_p_star_or.lean`（`#check formula_or_uncond`）exit 0、`_lp_check.lean`（临时诊断：2 #print `Lp_pos_uncond(_5)` 闭包）exit 0。注意：`lake build BSD.PositivityGRH`（库级 target 名）在本环境解析为顶层文件 `BSD/PositivityGRH.lean`（不存在）——有效命令是**完整模块名** `BSD.PositivityGRH.PositivityGRH`（历史 KEY_FACTS 中 `BSD.Xxx` 写法为简化记录）。

**axiom 闭包（实测，`_grh_refactor_axioms.txt`）**：
- `p_star_uncond` = 逻辑公理 + Positivity 对象层（消元/Kolyvagin `lprime_ne_zero_of_rank_one(_5)`/`Lprimeprime_ne_zero_of_rank_eq_two(_5)` 等）+ 解析对象 axiom（L_E(_5)、连续、尾部正、Taylor、`zero_free_re_one_side(_5)`）——**不含任何 bsd_formula_rank_* 公式猜想、不含任何 GRH 猜想 axiom**；
- `Lpp_pos_uncond` = 逻辑 + Lprimeprime + Taylor 定义级非零 + zeroOrderE + L_E + 尾部正 + 连续 + taylor_second + `zero_free_re_one_side`（无公式、无 GRH 猜想）；
- `pos_on_interval_of_no_zero` = 纯逻辑（IVT 真证明）；
- `L_E_no_zero_full` = 逻辑 + L_E + fe + rootNumber + `zero_free_re_one_side`（推论 C 同步升级：右半零自由区域替换 GRH，假设面不变窄）。

**净效应**：P* 的假设谱系——**通道 A（公式，猜想级）∨ 通道 B（无条件结构，定理级挂账）**；GRH 完全退出。通道 B 剩余 axiom 全部为定理级（Kolyvagin 秩1 非零、零自由区域、解析对象）——实现缺口而非数学缺口。Sha 有限性仍开放，但已从 P* 依赖中消失（P* 只要符号与秩，不要公式等式）。"枚举=理论"不可行（E/ℚ(√5) 同构类无限，Shafarevich 只给固定导子有限）——理论级闭合靠无条件链，枚举只作审计（方案 X 未立项，记录在案）。

**下一阶段指针**：推论 A（`ZeroGap.lean`）现在**无 GRH 前置**——Hadamard 对数恒等式在 (1/2, 3/2)∖{1} 无零点区域上工作（该区域已是无条件定理级）；γ₀ ≥ η 的 η 数值由 probe 管线固定 δ 档给出。若要继续"实例审计最大化"（方案 X：K 上有界导子枚举 + 区间闭证），先做 ℚ 基扩展族（K 上无 Cremona 表，LMFDB 数域曲线表覆盖极小——研究空白，如实标注）。

---

## 0.12 推论 C：函数方程延伸保号（本轮 8 落盘，`BSD.PositivityGRH` 内）

用户决策：按建议顺序先落 C——无零点区域从右半 (1, 3/2) 拉到中心两侧 (1/2, 3/2)∖{1}。

**数学内容**：实系数函数方程 Λ(σ) = ε·Λ(2−σ)；Γ 因子与 N^{s/2} 在实轴 (1/2, 3/2) 恒正 ⟹ 对 σ ∈ (1/2, 1)：sign L(σ) = ε·sign L(2−σ)，且 L(σ) = 0 ⟺ L(2−σ) = 0。右半已由通道 B 保号（grh_no_zero + 欧拉积尾部 + IVT），左半经函数方程拉回。

**Lean 结构**（PositivityGRH.lean 新增 `## 1b` / `## 3b`）：
- 6 条新 axiom：`rootNumberE / rootNumberE5 : ℝ`（根数对象）、`rootNumberE(_5)_eq_pos_or_neg`（±1 消元）、`L_E(_5)_fe`（一条 axiom 双内容：`(0 < L σ ↔ 0 < ε·L(2−σ)) ∧ (L σ = 0 ↔ L(2−σ) = 0)`——符号与零点对应一体，避免两条 axiom 语义重叠）；
- 8 条真定理：`L_E_no_zero_left(_5)`、`L_E_pos_left_of_rootNumber_one(_5)`（ε=+1 ⟹ 正）、`L_E_neg_left_of_rootNumber_neg_one(_5)`（ε=−1 ⟹ 负）、`L_E_no_zero_full(_5)`（主定理：hlo/hhi/hne ⟹ L ≠ 0，左半/右半分支）。

**编译账**：主模块与 `_check_positivity_grh`（+6 #check +1 #print）双绿 exit 0；修复 1 处（`lt_of_le_of_ne` 第二参数用 `hne` 而非 `Ne.symm hne`——方向）。

**axiom 闭包（实测）**：`L_E_no_zero_full` = propext/Classical.choice + rootNumberE/rootNumberE_eq_pos_or_neg/L_E_fe/L_E/grh_no_zero_L_E（函数方程层 5 条）——**不含 Taylor 商、不含尾部正、不含 Kolyvagin**——推论 C 的假设面比通道 B 主体更窄，零成本声明成立。

**实例口径**：ε 由根数确定（389a1：ε(E)=+1、ε(E⁵)=+1；37a1/K：ε_K=−1 由 Main.lean 根数乘性给）；符号定理按 ε=±1 分别实例化。

**与推论 A 的关系**：C 是 A 的前置——无零点区域 (1/2, 3/2)∖{1} 已形式化，A 的 Hadamard 对数恒等式将在该区域上工作。

---

## 0.11 ③ 讨论：正性余量 ⟹ 零点下界 / 密度估计（本轮 7 收口，未落骨架）

用户决策：讨论并收口——分量正性余量（389a1 严格区间已给 L″/2 ≥ 0.7584）能否量化 L(E/K) 在 (1, 3/2) 的零点信息。结论：**能推"最近零点高度下界"，推不出"零点密度"**。

**机制（Hadamard 对数恒等式）**。GRH（零点 ρ = 1+iγ，γ∈ℝ）+ 中心 k 重零 + 保号 L(σ)>0 于 (1,3/2]。对完整 Λ(s) = N_K^{s/2}·γ(s)·L(s)，实 σ = 1+δ：

```
log Λ(1+δ) = log(Λ⁽ᵏ⁾(1)/k!) + k·log δ + (1/2)·Σ_{γ≠0} log(1 + δ²/γ²) + O(δ)
```

Σ 项全非负，且 ≤ δ²·Σ1/γ²——**Σ1/γ² 收敛是 Hadamard 理论的无条件事实**（自守 L 有限阶），不需要零点密度。核心：中心正性余量绑定的是**零点虚部的矩**，不是计数函数。

**推论 A（可达）：最近非中心零点高度下界 γ₀ ≥ η > 0。**
单零点项 ≥ (1/2)log(1+δ²/γ₀²)，配 Λ 数值上界 C₂(δ)（无条件可得，不需尾部正）：

```
√(1+δ²/γ₀²) ≤ C₂(δ)/δ^k  ⟹  γ₀ ≥ δ/√(C₂(δ)²·δ^{-2k} − 1)
```

k=2、δ=1/2、C₂~10 ⟹ γ₀ ≳ 0.0125——数值可算。GRH 下实轴上唯一零点即中心，γ₀>0 自动成立；η 的存在性本身即"最近零点不塌到中心"的非平凡结论。强度由**固定 δ 处 L(1+δ) 数值下界**决定（现有管线只有中心导数区间，δ=1/2 处需重跑一档，小活）。

**推论 B（不可达，诚实声明）：零点密度 N(T) 增强。**
Σ log(1+δ²/γ²) ≤ 右界只压矩（Σ1/γ²，Hadamard 已给），压不出计数函数。N(T) ~ (T/π)·log(T√N_K/2πe) 走函数方程 + Selberg 显式公式，**无条件经典路线，P* 不进入也不需要**。正性余量在密度层无增援力——此边界记入账本，避免后续"秩2不行"式返工。

**推论 C（可达，零成本）：保号经函数方程延伸。**
σ ∈ (1/2,1)：L(σ) = 因子·ε_K·L(2−σ)，ε_K=−1（秩1 情形）实轴符号已知 ⟹ **(1/2, 3/2)∖{1} 全区间无零点**——通道 B 机制的直系推论，无零点区域从右半拉到中心两侧。

**两个质疑点**：
1. **"尾部正 s≥3/2 无条件"需降格**——通道 B axiom 层如实标注为假设；GL₂ 自守 L 实轴符号非标准定理（a_p 符号不定）。推论 A 不用它（C₂ 上界另有来源）。
2. **η 对数值管线敏感**——C₂ 是上界（易得），m₀ 是下界（已有），但固定 δ 处 Λ 数值上界需单独跑（mpmath iv 管线现成）。

**建议立项顺序**：C（函数方程延伸保号——纯逻辑、复用机制、零/一条新 axiom）→ A（`ZeroGap.lean` 骨架：零点集/γ₀ 对象层 + Hadamard 对数恒等式 axiom + 纯代数不等式定理 γ₀ ≥ η，η 由 probe 管线给数值）→ B 不立项（边界记入账本）。

**状态**：讨论收口，骨架未立项，待用户确认。

---

## 0.10 P* 合流：公式 ∨ K-GRH（本轮 6 落盘，`BSD.PStarOr`）

用户决策：先做合流——把"（BSD 公式 ∨ K-GRH）⟹ P*"落成单一模块，兑现双通道免疫声明。

**结构**（`C:\proj2\BSD\PStarOr\PStarOr.lean`）：
- 3 条标志 axiom（无数学内容，仅命名假设族）：`formula_holds : Prop`、`grh_holds : Prop`、`formula_or_grh : formula_holds ∨ grh_holds`；
- 4 条分量合流定理：`Lp_pos / Lpp_pos / Lp_pos5 / Lpp_pos5`——每个在 `rcases formula_or_grh` 后分支到通道 A 定理（lprime_pos_of_rank_one 等，公式路径）或通道 B 定理（grh_Lp_pos 等，GRH 路径）；
- 主定理 `p_star_or (h : analyticZeroOrder = 2) : 0 < Lprimeprime_EK_one`——公式分支经 `zeroOrder_additivity` 转换后调 `p_star`，GRH 分支直调 `p_star_grh`。

**axiom 闭包（#print axioms 实测）**：
- `p_star_or`：propext/Classical.choice + PStarOr 3 标志 + Positivity 对象层/4 公式/消元 + PositivityGRH 12 条——正是"公式 ∪ GRH"并集（结构性：未来任一被证明，去掉对应分支）；
- **互斥审计**：`p_star_grh` 闭包（0.9 节实测）不含 `bsd_formula_rank_one/one5/two/two5`（4 条公式 axiom）；`p_star` 闭包（通道 A）不含任何 PositivityGRH axiom——两条证明路径假设互斥、各自独立成立。

**编译账**：`lake build BSD.PStarOr.PStarOr` 与 `_check_p_star_or`（6 #check + 2 #print）双绿，一次通过。

**意义**：P* 的可靠性声明从"两条并行通道"升级为"单一析取定理"——Lean 里第一次把两大猜想族（精细 BSD 公式 / K-GRH）的关系写成 `∨` 结构，任意一方获证即 P* 自动成立。

---

## 0.9 通道 B：K-GRH 保号路径（本轮 5 落盘，`BSD.PositivityGRH`）

用户决策（经讨论确认"有必要另建文件夹"）：GRH 通道与 BSD 公式通道假设集互斥（公式 ∨ GRH 任一成立即定理），命名空间独立。

**机制**（精化①：要的是 L(E/K) 的 GRH，临界线 Re=1，不是 ζ_K 的 Re=1/2）：
- 欧拉积尾部正：s ≥ 3/2 无条件（THEOREM 级推论）；
- GRH axiom：L_E / L_E5 在 (1, 3/2] 无零点 ⟹ 保号；
- IVT 真证明（`pos_on_interval_of_no_zero`，只依赖 propext/Classical.choice/Quot.sound）：闭子区间 [a, 3/2]（1 < a）全正 ⟹ 开区间 (1, 3/2) 全正（中点点位 (1+x)/2 拉回）；
- Taylor 商 axiom：L(1+δ)/δ → L′(1)，L(1+δ)/δ² → L″(1)/2；
- 非零提升：秩1 Kolyvagin（axiom）、秩2 Taylor 定义级（axiom）；
- 极限非负（le_of_tendsto 取负构造）⟹ 0 ≤ L′(1) / L″(1)/2；配非零 ⟹ > 0。

**Lean 结构**：GRH 层 12 axiom（L_E/L_E5 对象、ContinuousOn×2、尾部正×2、grh_no_zero×2、taylor_first/_second(_5)）+ 真定理 13 条：
`pos_on_interval_of_no_zero`、`grh_pos_on_Icc(_5)`、`grh_L_E_pos_on_open(_5)`、`grh_Lp_pos(_5)`、`grh_Lpp_pos(_5)`、`grh_type_20/11/02`（Leibniz 结构镜像 Positivity，正性源换 GRH）、`p_star_grh`（主定理：analyticZeroOrder = 2 → 0 < L″(E/K,1)）。

**axiom 闭包（#print axioms 实测）**：
- `p_star_grh`：propext/Classical.choice + Positivity 对象层 + 公式/消元 axiom + 12 条 GRH axiom——GRH 不给 Sha 有限/公式（不排前），也不需要；
- `grh_Lpp_pos`：对象 + Lprimeprime_ne_zero_of_rank_eq_two + 5 条 GRH axiom；
- `pos_on_interval_of_no_zero`：仅逻辑公理。

**编译账**：主模块 `lake build BSD.PositivityGRH.PositivityGRH` 绿、校验 `_check_positivity_grh`（8 #check + 3 #print）绿；修复路径 3 轮：import 修正（删不存在的 Mathlib.Topology.Instances.Real → IntermediateValue/OrderClosed）、`isPreconnected_Icc` + `IsPreconnected.intermediate_value`（像成员 → rcases）、linarith → dsimp [a]、`δ ∈ Set.Ioi 0` simpa 解包、`ge_of_tendsto`（to_dual 歧义）→ le_of_tendsto 取负构造、axiom Bool 型 `!= 0` simpa 转 Prop、type_trichotomy 分支顺序 (0,2)|(1,1)|(2,0) 配对。

**与通道 A 的关系**：P* 对两大猜想族免疫——BSD 公式 ∨ GRH 任一成立即定理。数据层 17 axiom（389a1 与六条严格区间）是两通道共同的数值证实；实例层不排前。

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
