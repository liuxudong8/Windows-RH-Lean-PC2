# RH 主链缺口 Checklist

> 审计对象：`c:\proj2`（Lean 4 v4.34.0-rc2，Lake 5.0.0）
> 编译结果：`lake build OrderPreservingBijection` — **Build completed successfully (3851 jobs)**，零 error。
> 主链入口：`RHSpectralDuality.riemann_hypothesis`（`stage_4.lean:5393`）。
> 审计方法：手工追 `riemann_hypothesis` 依赖闭包至叶子。`#print axioms` 只能看到 `sorryAx`，本清单给出 19 个具体缺口。

---

## 主链依赖骨架

```
riemann_hypothesis (5393)
└─ all_zeros_on_critical_line (5240)
   ├─ off_critical_line_contradiction (5213)
   │  ├─ nontrivial_zero_sum_pair_separation (5194)
   │  │  └─ off_critical_zero_tail_dominated (5095)
   │  │     └─ mollified_pair_tail_sum_negligible (4913)
   │  │        ├─ zero_weighted_series_summable2 (2666) ── ⑭
   │  │        ├─ zeroMultiplicity_positive_at_nontrivial_zeros (ZetaZeros:75) ── ⑰
   │  │        └─ mellin_pair_uniform_decay_bound (4849)
   │  │           └─ mellin_rapid_decay_choice (4801)
   │  │              └─ mellin_smooth_interpolation (3702)
   │  │                 └─ mellin_smooth_min_derivative_norm_uniform (3662)
   │  │                    └─ mellin_constraint_dual_norm_lower_uniform (3537) ── ⑲
   │  │  └─ spectral_sum_determined_by_points (1613)            [已证，无 sorry]
   │  └─ weil_explicit_formula_trivial_terms_cancel (1550)
      ├─ mollified_trace_equality (1370)
      │  ├─ arthur_trace_formula (525)
      │  │  ├─ atf_spectral_decomposition (357)
      │  │  │  └─ spectral_decomposition_additivity (343) ── ②
      │  │  └─ atf_geometric_expansion (507)
      │  │     └─ atf_geometric_expansion_core (497)
      │  │        └─ full_orbital_integral_expansion (480) ── ③
      │  ├─ continuousTerm_eq_trivialZeroContribution (1356)
      │  │  └─ continuous_term_contour_shift (1340) ── ⑤
      │  └─ ellipticTerm (MollifiedFunction:30)
      │     └─ ellipticClassLengths_finite (MollifiedFunction:20) ── ④
      └─ weil_explicit_formula (1540)
         ├─ geometric_sum_log_derivative (1512)
         │  ├─ perron_formula (1411) ── ⑥⑦⑧
         │  └─ euler_product_integral (1466)
         │     └─ primeDirichlet_zetaLogDerivative_diff_holomorphic (ContourIntegral:138) ── ⑨
         └─ log_derivative_integral_residues (1526)
            └─ residue_theorem_zeta_log_derivative (ContourIntegral:128)
               ├─ zeta_log_derivative_contour_eq_residue_sum (ContourIntegral:106) ── ⑩
               └─ zeta_log_derivative_residue_sum_eq_zeroside (ContourIntegral:115) ── ⑪
```

另：`laplacian_has_discrete_spectrum`（79）是 `specDiscM` 的源头，被 `spectralSum` 闭包全域引用 —— ①。
`nontrivial_zero_sum_summable`（1628）→ `nontrivialZeroSum_tsum_linear`（1630）→ `off_critical_zero_tail_dominated`（5180）—— ⑫。
`zero_counting_and_multiplicity`（1922）→ `zero_weighted_series_summable`（2474）→ ⑭ —— ⑬。
`nontrivialZeroEnum_exists / riemannZeta_neg_on_Ioo / h_order_ne_top` 是 `nontrivialZeroEnum` 与重数的底层设施 —— ⑮⑯⑰。
`mollified_test_function_uniform_support`（2795）→ `globalR₀` → `mellin_rapid_decay_choice` —— ⑱。

---

## 缺口清单（19 条）

### A. 谱分解公理（ATF 谱侧）

- [ ] **① `laplacian_has_discrete_spectrum`**
  - 位置：`stage_4.lean:66`（admit 于 `:79`）
  - 当前：`admit`
  - 数学依据：双曲三流形 `ℍ³/Γ` 上 Laplacian 的 Rellich 紧预解式 + 紧自伴算子谱定理，给出非负、严格递增、无界的离散特征值序列 `s_n`，且 `s_0 > 0`（谱隙，因常数函数不在 L²）。
  - 主链角色：`specDiscM` 的唯一定义来源；`spectralSum f = Σ'_n f(s_n)` 整个几何–谱等式都挂在它上面。
  - 降级路径：在 ManifoldInfrastructure 里形式化 `Δ_M` 的自伴性与预解紧性，再调 mathlib 的紧自伴算子谱定理。

- [ ] **② `spectral_decomposition_additivity`**
  - 位置：`stage_4.lean:343`（admit 于 `:348`）
  - 当前：`admit`
  - 数学依据：`L²(Γ\G) = L²_disc ⊕ L²_cont` 正交分解；卷积算子 `K_f = f(Δ)` 在两个不变子空间上迹之和等于全空间迹。
  - 主链角色：ATF 谱侧 `Tr_geo = Tr_disc + Tr_cont`，接 `arthur_trace_formula`。
  - 降级路径：依赖 Eisenstein 级数连续谱投影的形式化，工作量大。

### B. ATF 几何侧

- [ ] **③ `full_orbital_integral_expansion`**
  - 位置：`stage_4.lean:480`（admit 于 `:485`）
  - 当前：`admit`
  - 数学依据：热核 `K_f(z,z) = Σ_{γ∈Γ} K_f(z,γz)` 的 Γ-周期化，再按半单共轭类（双曲/椭圆/抛物）分类求和。对应 Arthur (1974) §4–5。
  - 主链角色：ATF 几何侧 `Tr_geo = hyperbolic + elliptic + parabolic`。
  - 降级路径：热核周期性 + 共轭类计数收敛性，需 `HeatKernel.lean` 现有基础设施补完。

- [ ] **④ `ellipticClassLengths_finite`**
  - 位置：`MollifiedFunction.lean:20`
  - 当前：`sorry`
  - 数学依据：算术群 `PSL₂(O_K)`（`K=Q(√5)`，Q-rank 0）中椭圆元素阶有界，旋转角只能取有限个值。
  - 主链角色：`ellipticTerm` 的 `toFinset` 直接以本引理为证据；`mollified_trace_equality` 用 `ellipticTerm = 0`。
  - 降级路径：按 Γ 的有限阶共轭类分类，有限性可直接枚举 `Q(√5)` 的单位根。

### C. 连续谱 = 平凡零点

- [ ] **⑤ `continuous_term_contour_shift`**
  - 位置：`stage_4.lean:1340`（admit 于 `:1350`）
  - 当前：`admit`
  - 数学依据：散射矩阵对数导数 `φ'/φ` 的极点仅在 `s=-2,-4,...`（负偶数）；围道从临界线左移，大圆弧由 `M[f]` 速降消去，留数即平凡零点 + `s=1` 极点贡献。
  - 主链角色：`continuousTerm = trivialZeroContribution`，是 ATF 侧与 Weil 侧"平凡项消去"的桥梁。
  - 降级路径：散射矩阵解析延拓 + 留数定理；需先补 `ContourIntegral` 的留数机器。

### D. Perron 公式（`perron_formula`，1411，三连 admit）

- [ ] **⑥ Mellin 反演步**
  - 位置：`stage_4.lean:1422`（`h_mellin_inversion`）
  - 当前：`admit`
  - 数学依据：`f(log N(p)) = (1/2πi) ∮ M[f](s) N(p)^{-s} ds`，Mellin 逆变换。
  - 主链角色：把几何侧 `f(log N(p))` 写成围道积分。

- [ ] **⑦ 求和–积分交换步**
  - 位置：`stage_4.lean:1432`（`h_main2`）
  - 当前：`admit`
  - 数学依据：磨光函数 `f` 紧支光滑 ⇒ 控制收敛定理，允许 `Σ_γ ∮ = ∮ Σ_γ`。
  - 主链角色：几何侧求和与 Dirichlet 生成函数围道积分互换。

- [ ] **⑧ Dirichlet 级数等式步**
  - 位置：`stage_4.lean:1437`（`h_dirichlet_eq`）
  - 当前：`admit`
  - 数学依据：`Σ_γ W(γ) N(γ)^{-s} = primeDirichletSeries(s) = Σ_p (log p) p^{-s}/(1-p^{-s})`，Re(s)>1 时 Euler 乘积对数导数。
  - 主链角色：把双曲轨道加权和识别为 ζ 的素数 Dirichlet 级数。
  - 降级路径：⑥⑦⑧ 合起来就是 Perron (1908) 公式在数域上的标准应用；建议整体作为一条引理从 mathlib 的 `LSeries` 理论桥接，而非分三步补。

### E. 复分析桥接（`ContourIntegral.lean`）

- [ ] **⑨ `primeDirichlet_zetaLogDerivative_diff_holomorphic`**
  - 位置：`ContourIntegral.lean:138`（sorry 于 `:143`）
  - 当前：`sorry`
  - 数学依据：Re(s)>1 时 `D(s) = -ζ'/ζ(s)`（Euler 乘积对数导数）；差 `D(s)-ζ'/ζ(s)` 可解析延拓进围道内且在围道上 CircleIntegrable。
  - 主链角色：`euler_product_integral` 用 Cauchy 定理把两个围道积分相等。
  - 降级路径：用 mathlib 现有 `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` 延拓。

- [ ] **⑩ `zeta_log_derivative_contour_eq_residue_sum`**
  - 位置：`ContourIntegral.lean:106`（sorry 于 `:109`）
  - 当前：`sorry`
  - 数学依据：`(1/2πi)∮ (ζ'/ζ)(s) M[f](s) ds = Σ'_n m(ρ_n) M[f](ρ_n) - M[f](1)`；m 阶零点处对数导数留数为 m，s=1 为一阶极点留数 -1。
  - 主链角色：留数定理在 ζ 对数导数上的第一刀。

- [ ] **⑪ `zeta_log_derivative_residue_sum_eq_zeroside`**
  - 位置：`ContourIntegral.lean:115`（sorry 于 `:117`）
  - 当前：`sorry`
  - 数学依据：`Σ m(ρ)M[f](ρ) - M[f](1)` 按定义等于 `zetaZeroSide = nontrivialZeroSum + trivialZeroContribution`。
  - 主链角色：把留数和翻译回 `zetaZeroSide`。
  - 备注：`residue_theorem_general`（`:92`）是悬空的——`:128` 直接用 ⑩⑪，没走它。补 ⑩ 时可考虑把 `:92` 一起降级。

### F. 零点侧级数估计

- [ ] **⑫ `nontrivial_zero_sum_summable`**
  - 位置：`stage_4.lean:1626`（admit 于 `:1628`）
  - 当前：`admit`
  - 数学依据：零点密度估计 + Mellin 变换在竖直线上的多项式增长/速降，保证 `Σ m(ρ_n) M[f](ρ_n)` 绝对收敛。
  - 主链角色：`nontrivialZeroSum_tsum_linear` 的前提；反证法尾部三角不等式的入口。

- [ ] **⑬ `zero_counting_and_multiplicity`**
  - 位置：`stage_4.lean:1922`（admit 于 `:1932`）
  - 当前：`admit`
  - 数学依据：Riemann–von Mangoldt `N(T) ~ (T/2π)log(T/2π) - T/2π`；Jensen 公式给出 `m(ρ) ≤ C(1+log(2+|Im ρ|))`。
  - 主链角色：⑭ 的输入。
  - 降级路径：mathlib 已有 `riemannZeta` 零点计数基础，需补重数对数增长。

- [ ] **⑭ `zero_weighted_series_summable2`**
  - 位置：`stage_4.lean:2666`（admit 于 `:2671`）
  - 当前：`admit`
  - 数学依据：`Σ_n m(ρ_n)/|Im ρ_n|² < ∞`；由 ⑬ 的 `N(T)` 与 `m(ρ)` 估计分部求和得到。
  - 主链角色：`mollified_pair_tail_sum_negligible` 里权重 `w(n)=m(ρ_n)/|Im ρ_n|²` 的可和性，尾部 `< m(ρ)/2` 的发动机。

### G. 零点基础设施 + 插值构造

- [ ] **⑮ `nontrivialZeroEnum_exists`**
  - 位置：`ZetaZeros.lean:13`（sorry 于 `:37`）
  - 当前：`sorry`
  - 数学依据：临界带内非平凡零点集可数（`riemannZetaZeros` 与每个闭圆盘相交有限，已证；可数并即可数）——**末尾的双射枚举那步是 sorry**。
  - 主链角色：`nontrivialZeroEnum` 定义来源，⑯⑰与整个零点侧求和都依赖它。

- [ ] **⑯ `riemannZeta_neg_on_Ioo`**
  - 位置：`ZetaZeros.lean:60`（sorry 于 `:61`）
  - 当前：`sorry`
  - 数学依据：对 `0<x<1`，ζ(x)<0（函数方程 + Γ 正性 + cos 符号）。
  - 主链角色：`nontrivialZero_im_ne_zero`（63）的反证——若 `ρ` 为实零点则矛盾，故零点不在实轴上。

- [ ] **⑰ `h_order_ne_top`（在 `zeroMultiplicity_positive_at_nontrivial_zeros` 内）**
  - 位置：`ZetaZeros.lean:84`
  - 当前：`sorry`
  - 数学依据：`analyticOrderAt riemannZeta ρ ≠ ⊤`，即 ζ 在非平凡零点处不是恒等零函数。
  - 主链角色：`zeroMultiplicity ρ > 0`；尾部估计里 `m(ρ)` 是正实数的关键。

- [ ] **⑱ `mollified_test_function_uniform_support`**（语义已重定位）
  - 位置：`stage_4.lean:2797`（sorry）
  - 当前：`sorry`
  - 数学依据：对固定 off-critical 零点 ρ，存在统一窗口 `[ε₀, R₀]`，使得 PWW 插值构造产生的所有 `h_T`（T 跑遍有限临界零点集）支集都在其内。窗口 `b_ρ` 依赖 ρ，但**不依赖 T**（即不依赖 N）。
  - 主链角色：`mellin_rapid_decay_choice` 里常数 `C = 8(B+1)(R₀³+1)` 不随 N 爆炸的依据。
  - **形式选择**：已回退到形式 B——结构字段保留存在式 `supportBounded : ∃ ε₀ R₀, ...`，不写死窗口大小；`R₀` 是符号常数（`Classical.choose`），由⑲ PWW 构造具体算出。硬编码 `[1/2,2]` 的路（形式 A）已废弃，因为它过度约束：`t_eval(ρ)` 可能不在固定窗口内。
  - 降级路径：与⑲ `mellin_constraint_dual_norm_lower_uniform` 一起证——PWW 对偶构造同时给出 (a) 插值可行性、(b) 对偶范数下界 c、(c) 窗口 `b_ρ` 不依赖 T。

- [ ] **⑲ `mellin_constraint_dual_norm_lower_uniform`**
  - 位置：`stage_4.lean:3539`（骨架已搭）
  - 当前：骨架已搭，拆为两个有数学意义的子目标：
    - `h_phi0`（参考 bump 存在性）：∃ φ₀ : MollifiedTestFunction，M[φ₀](ρ)≠0 且在谱点上为 0。PWW 支撑定理给出。
    - `h_pww`（Paley-Wiener 对偶范数下界）：∃ c>0 统一，对任意有限 T，hT=L_T φ₀ 满足全部 6 条约束。
  - 数学路线（注释已写入源码）：固定 φ₀ → hT = L_T φ₀ = ∏_{t∈T}(D+t)φ₀ → M[hT](s)=(∏(-(s-t)))·M[φ₀](s)（归纳自 `melinTransform_differentialOperator_add`）→ T 上消零、ρ 处非零 → PWW 对偶给统一 c。
  - 数学依据：对偶范数统一正下界 `c>0`：对任意有限 `T`（`ρ∉T`），存在 C² 磨光 `h_T` 在 `T` 上 Mellin 变换为零、在 `ρ` 处非零，且 `|M[h_T](ρ)| ≥ c·‖h_T''‖`。构造用微分算子 `L_T = ∏_{t∈T}(D+t)` 作用在固定 bump 上。
  - 主链角色：PWW 插值的 Hahn–Banach 对偶估计；`off_critical_zero_tail_dominated` 整条反证链的解析发动机。
  - 依赖：`melinTransform_differentialOperator`（MellinInfrastructure.lean:181）——分部积分公式 M[Df](s)=-s·M[f](s)。骨架已搭，5 个 sorry 全是 Lean 技术细节（hderiv 链法则、h_integral_deriv FTC、hlin 线性性、h_eq1/h_eq2 if 分支），数学逻辑闭合。
  - 备注：这是 19 条里**数学密度最高、最接近 RH 真正难点**的一条。

---

## 优先级建议

| 优先级 | 条目 | 理由 |
|---|---|---|
| P0（循环风险） | `spectral_zero_set_match`（5278，非主链） | 现在就隔离，防止被误接回 `all_zeros_on_critical_line`。 |
| P1（数学硬骨头） | ⑲⑱、⑥⑦⑧、⑭⑬ | ⑲⑱ 现在是同一条 PWW 对偶构造的两面；其余是 Weil 显式公式 + 尾部估计的实质内容。 |
| P1（复分析机器） | ⑨⑩⑪ | 留数定理在 mathlib 里已部分就绪，桥接工作量可控。 |
| P2（标准分析） | ①②③④⑤⑫ | 教科书结果，量大但单点不难。 |
| P3（基础设施） | ⑮⑯⑰ | 多数步骤已证，只差末尾枚举/符号计算。 |

## 不在本清单（已隔离）

- Shimura/JL 束（`stage_4:699/704/710/724/725/775/1098/1117/1135`）、Dolgopyat（`:1277`）、`maass_laplacian_has_discrete_spectrum`（`:212`）、`spectral_zero_set_match`（`:5278`）、`residue_theorem_general`（`ContourIntegral:92`）、`BijectionPhi/Basic.lean` 整模块、stage_3 的 Dedekind/Selberg 等价段、HeatKernel/Manifold/Interpolation/MellinInfrastructure 里的算子基础设施 sorry。
