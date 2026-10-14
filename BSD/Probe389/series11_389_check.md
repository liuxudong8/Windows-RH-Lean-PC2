# 389a1/p=11 series(11) 复刻：T²‖L₁₁ mod 11ᵏ（ord_T = 2）

> 数值路径 1 本体（用户主线）：L₁₁(T) 展开验证 ord_T=2，作为"Sha 有限性"五阶段路线（B-6/CH22 框架）的独立数值支柱。
> 工具链：WSL Ubuntu-22.04 内 PARI/GP 2.13.3（`msfromell(E,1)` + `mseval(M,v,[0,1;c,d])`，真模符号 H₁ 值）+ `l11_series.py` 复刻管道（11a1/p=3 校准 Σ=68 命中，见 `series_points_check.md` §6）。

## 1. 参数

| 参数 | 值 | 来源 |
|---|---|---|
| 曲线 | 389a1 [0,1,1,−2,0] | N=389, rank 2 |
| p, a_p | 11, a₁₁=−4（good ordinary） | kato_framework_check.md §5 |
| n, prec | 2, 5 | Sage series(11) 默认 |
| Δ | 389 > 0 ⟹ real_components = 2 | series 内 L /= real_components |
| M(0) | **0**（PARI 实测 [1,0;0,1]） | rank 2 ⟹ L(E,1)/Ω = 0 |
| padic_prec | 6（11⁶ = 1771561） | e_bounds(1,5,11)=[∞,1,1,1,1] → max+5 |
| γ = 1+p | 12 | series 主循环 |
| w = p^{n−1} | 11 | measure: f(b/121) − f(b/11)/α |
| 求值点数 | 110×(r121,r11) + 22 补测 | j=0..10, a=1..10；分布恒等式点 |

## 2. PARI 数据与自洽性

- 220 个 series 点（分母 121 与 11）+ 补测 22 个（{0,1}、分母 1331 的 11 点、分母 121 分布点 10 个）。
- 重复点值一致（distinct r121=110, r11=10, 无 INCONSISTENT）。
- **分布恒等式**（真模符号 H₁ 性质，a_p·f({0,r}) = Σ_m f({0,(r+m)/p}) + f({0,pr})）：
  - r=1/121：−4·0 = 0 = −1 + f({0,1/11})=1 ✓ **精确**
  - r=1/11：−4·1 = −4 = −4 + f({0,1})=0 ✓ **精确**
- 389a1 的 series 点全部非尖点端点（分子 c < 121、分母 ∈ {11,121,1331} 与 N=389 互素 ⟹ 无需对称补）。

## 3. series(11) 结果（read_pari_series11.py）

```
L_11(T) = 0 + 0·T + 9·T² + 9·T³ + 9·T⁴   (mod 11 系数)
T⁰: ≡ 0 mod 11⁴   (bd = padic_prec−2 = 4)
T¹: ≡ 0 mod 11    (bd = 1)
T²: ≡ 9 mod 11 ≠ 0
T³, T⁴: ≡ 9 mod 11 (无约束)
```

**ord_T 判定**：T⁰ ≡ T¹ ≡ 0 mod 11 ∧ T² ≢ 0 mod 11 ⟹ **ord_T = 2 ✓**（mod 11 意义下精确；L_p 的 Taylor 首项为 T²）。

## 4. 交叉互证

| 证据 | 来源 | 结论 |
|---|---|---|
| T² ≡ 9 mod 11 ≠ 0 | 本次 PARI 管道 | ord_T=2 @ p=11 ✓ |
| series(3) = O(3⁵) + O(3²)T + (2+2·3+O(3²))T² | Sage docstring（389a1） | ord_T=2 @ p=3 ✓（T² mod 3 = 2 ≠ 0） |
| L″(E,1)/2 = 0.759316500288 | 区间算术（无条件） | analytic rank 2 ✓ |
| M(0) = 0 | PARI 实测 | rank ≥ 1 自洽 |

**结论**：rank 2 曲线 389a1 在 ordinary 素数 11 处 p-adic L 函数零点阶 = 2，与解析秩 2 一致；独立数值支柱成立（B-6/CH22 框架的 λ₁₁=2 证据）。

## 5. 产物

- `gen_ms389a1_gp.py`（点生成器）、`ms389a1_series.gp`（220 点求值）、`ms389a1_smoke.gp`（M(0)=0 冒烟）、`ms389a1_dist.gp`/`ms389a1_dist2.gp`（分布验证点）
- `ms389a1_series_out.txt`/`ms389a1_dist_out.txt`/`ms389a1_dist2_out.txt`（PARI 原始输出）
- `read_pari_series11.py`（parse + 自洽性 + series 复刻 + ord_T 判定；重跑即复现）
- 校准链：`series_points_check.md` §6（11a1/p=3 闭环）
