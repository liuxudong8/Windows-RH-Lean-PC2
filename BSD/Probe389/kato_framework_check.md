# 框架实证：广义 Kato 类 ⟹ corank 上界 ⟹ Ш[p^∞] 有限（389a1 实例）

日期：2026-10-13
状态：**闭环完成**（文献定理链，无猜想缺口）
来源：Castella–Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum Math. Sigma 10 (2022) e12；Castella, arXiv:2312.01481。

## 0. 目标与结论

B-6 的"新数学输入"评估结论：rank 2 欧拉系路线（BDR/Beilinson–Flach 谱系）对 **λ_p** 的贡献是间接的——
它给的是 **ℚ 侧** Selmer 的 corank 上界（dim Sel(ℚ,V_pE) = 2 ⟹ Ш[p^∞] 有限），
而 λ_p 是 **K_cyc 侧**（Greenberg 控制定理），两者不直接等同。
但 ℚ 侧的 Ш[p^∞] 有限性本身就是"Sha 有限性"主线的一半（每素数 p 的 p-侧闭合）。

**框架实证完成**：对 389a1 + p=11，CH22 的定理链在真实 rank 2 曲线上完整跑通：

```
Theorem B (ord_T Θ_{f/K} = 2，数值已验证)  ⟹  κ_{α,α⁻¹}(f,g,g*) ≠ 0
        ⟹  Theorem A (1.9)  ⟹  dim Sel(ℚ, V₁₁E) = 2
        ⟹  rank E(ℚ) = 2  ⟹  T₁₁(Ш)⊗ℚ₁₁ = 0
        ⟹  Ш[11^∞](E/ℚ) 有限（无条件定理）
```

## 1. 条件核查表（389a1 / p=11 / K=ℚ(√−2)）

| CH22 条件 | 389a1 实例 | 状态 |
|---|---|---|
| p > 3 good ordinary | a₁₁ = −4 ≠ 0 (mod 11)，conductor 389 ≠ 11 | ✓ 已核（本文件重算） |
| L(E,1) = 0，sign +1（analytic rank 2 偶数） | LMFDB：rank 2 = analytic rank 2 | ✓ 已知 |
| K 虚二次，判别式与 N_f 互素 | K = ℚ(√−2)，D = −8，389 ∤ D | ✓ |
| p = pp̄ 在 K 分裂 | 11 ≡ 3 (mod 8)，(−2/11) = 1 | ✓ |
| q = 389 inert in K（N_f⁻ = 389 奇数个素数） | (−2/389) = −1 | ✓ CH22 附录已核 |
| L(E, ad⁰(g), 1) = L(E^K,1)·L(E/K,χ,1) ≠ 0 | L(E^K,1) ≠ 0 CH22 已核；χ 由 [48] 保证存在无穷多 | ✓ |
| ρ̄_{E,11} 不可约 | 389a 类仅一条曲线（无 rational m-isogeny，m>3）| ✓ CH22 已核 |
| χ(p̄) ≠ 1（α ≠ β，Hecke 根互异） | CH22 附录设定覆盖 | ✓ |
| **ord_T Θ_{f/K} = 2** | Θ_{f/K} ≡ 10T²+69T³+T⁴+… (mod 11², T¹¹)，Sage Brandt module 验证 | ✓ CH22 Table 1 首行即 389a1 |

## 2. 关键引用定理（精确陈述）

**CH22 Theorem A**（g = θ_ψ 有 CM，满足上表条件）：
- κ_{α,β⁻¹} = κ_{β,α⁻¹} = 0（"坏"类消失）；
- **(1.9) κ_{α,α⁻¹}(f,g,g*) ≠ 0 ⟹ dim_{ℚ_p} Sel(ℚ,V_pE) = 2**（无条件方向）；
- (1.10) 逆方向：dim = 2 且 Sel ≠ ker(Loc_p) ⟹ κ ≠ 0（需要 rank > 0，389a1 满足）。

**CH22 Theorem B**：rank E(ℚ) > 0 时，**ord_T(Θ_{f/K}) = 2 ⟹ κ_{α,α⁻¹} ≠ 0**。
（Θ_{f/K} ∈ ℤ_p[[T]]：E/K 的反cyclotomic p-adic L 函数；leading term 公式任意消失阶成立。）

**descent 序列**：0 → E(ℚ)⊗ℤ_p → Sel(ℚ,V_pE) → T_p(Ш)⊗ℚ_p → 0。
dim Sel = 2 且 rank = 2 ⟹ T_p(Ш)⊗ℚ_p = 0 ⟹ **Ш[p^∞] 有限**。

## 3. 修正记录（本轮纠错）

1. **389a1 最小模型**：正确为 [0,1,1,−2,0] = **y²+y = x³+x²−2x**；先前误用 y²+y=x³−x²−2x+1（导致 a_p 全部错值：a₁₁ 误为 0）。已重算并核对生成元 (0,0),(1,0)（均在该曲线上）。
2. **p=2 非 ordinary**：a₂ = −2 ≡ 0 (mod 2) 恒成立（|a₂|≤2√2），**任何曲线在 p=2 均非 ordinary**。先前记录"389a1/p=2 good ordinary"有误——Greenberg 控制定理的 ordinary 前提在 p=2 不满足，**λ₂(389a1)=0 的挂账比 B-4 记录的更独立**（2-adic 无 ordinary 框架，B-4 axiom 仍成立但理由需修正）。

## 4. 剩余开放项（诚实清单）

1. **λ_p（K_cyc 侧）仍开放**：框架实证给的是 ℚ 侧 Ш[p^∞] 有限，不是 λ_p = 0。389a1/p=11 的 λ₁₁ 仍需 K_cyc 侧工具（Iwasawa 主猜想零点情形）。
2. **其余素数 ℓ ∉ {2, 11}**：Ш[ℓ^∞](389a1) 有限性仍未闭合（2 侧已由 A 阶段 = 0，11 侧现在有限）。
3. **κ ≠ 0 的完全构造性**：CH22 附录的 ord_T Θ = 2 是数值验证（Sage），非纸面证明——但 (1.9) 使结论无条件（前提是 ord = 2 真值，数值到 mod (11²,T¹¹) 已充分——(11^n, T^p) 递推保证）。

## 5. 下一步（按价值排序）

1. **Lean 集成**：把 (1.9)+Theorem B+descent 链写成 `Sha11_389` 定理骨架（文献 axiom 挂账 + 组合真证），并入 EulerSystem.lean 或新模块——直接给 Ш[11^∞] 有限的 Lean 陈述。
2. **λ₁₁ 的 K_cyc 侧**：Iwasawa 主猜想零点情形（Greenberg 弱 IMC + Kim 2203.12159 的任意秩结构），评估 389a1/p=11 适用性。
3. **数值复算**：独立复现 CH22 的 Θ_{f/K} mod (11²) 展开（本机无 Sage，可用 p-adic 算法替代或标注依赖）。
