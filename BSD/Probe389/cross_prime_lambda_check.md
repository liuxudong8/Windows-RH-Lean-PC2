# 跨素数核对：p 侧 λ₁₁ = 2 与 K_cyc 侧 λ（K = ℚ(√−2)）

> 主线③：把 series(11) 数值结果（λ₁₁ = 2）转 p 侧 Iwasawa 与 K_cyc 侧的跨素数核对。
> Iwasawa 特征分解：K/ℚ 二次 Abel（11 split in K），
>   L_p(E/K, T) = L_p(E, T) · L_p(E^χ, T)  ⟹  λ_p(E/K) = λ_p(E) + λ_p(E^χ)
> 其中 χ 为 K 的二次特征（χ = (−2/·)），E^χ = 389a1 的二次 twist。

## 1. E^χ 的对象与数据（PARI/GP 2.13.3）

| 量 | 值 | 来源 |
|---|---|---|
| E^χ 方程 | [0, −8, 0, −128, −128]（`elltwist(E, −8)`，−8 为 K 的域判别式） | PARI |
| conductor | 24896 = 389·64 = 389·8²（389 inert in K 保留，2 幂因子来自 twist） | ellglobalred |
| analytic rank | **0** | ellanalyticrank（无条件） |
| L(E^χ, 1) | **2.7884581989766949… ≠ 0** | ellanalyticrank |
| M(0) = L/Ω⁺ | **2（精确有理）** | msfromell（N=24896，4G 栈） |
| χ(11) = (−2/11) | (−1/11)·(2/11) = −1·(−1) = **+1** | Kronecker ⟹ 11 split in K ✓（CH22 条件） |
| a₁₁(E^χ) | χ(11)·a₁₁ = −4（11 仍 good ordinary） | twist 公式 |

## 2. λ(E^χ) 的数值判定（rank 0 恒等式）

rank 0 曲线的 series 常数项恒等式（11a1/p=3 校准已验证：T⁰ = (1−1/α)²·M(0)）：

  T⁰(E^χ) ≡ (1 − 1/α')² · M'(0)  mod 11

- α'（E^χ 在 11 的单位根）：x² − a₁₁'x + 11 = 0，a₁₁' = −4 ⟹ α' = α = 1685（mod 11⁶）
- 1/α ≡ 1625 ≡ 8 mod 11 ⟹ (1 − 1/α)² ≡ 4² ≡ 5 mod 11 ≠ 0
- **T⁰(E^χ) ≡ 5 · 2 ≡ 10 mod 11 ≠ 0** ⟹ **ord_T L_p(E^χ, T) = 0 ⟹ λ₁₁(E^χ) = 0** ✓

## 3. 核对表

| 对象 | λ 不变量 | 证据 | 类型 |
|---|---|---|---|
| E/ℚ, p=11（Q 侧 ordinary） | λ₁₁ = 2 | series(11)：T⁰≡0 mod 11⁴, T¹≡0 mod 11, T²≡9 mod 11 ≠ 0（PARI 管道） | 数值（已交付） |
| E/ℚ, p=3 | λ₃ = 2 | Sage docstring series(3)：T² ≡ 2 mod 3 ≠ 0 | 跨素数一致 |
| E^χ/ℚ, p=11（K 的二次特征 twist） | λ₁₁ = 0 | rank 0（ellanalyticrank）+ T⁰ ≡ 10 mod 11 ≠ 0 | 数值+解析 |
| **E/K, K_cyc, p=11（K = ℚ(√−2)）** | **λ₁₁(E/K) = 2 + 0 = 2** | 特征分解 λ(E/K) = λ(E) + λ(E^χ) | 推导 |

## 4. 结论

1. **跨素数一致**：秩 2 曲线 389a1 在 ordinary 素数 3 与 11 处 λ 不变量均为 2（λ_p = rank）。
2. **K_cyc 侧**：λ₁₁(E/K) = λ₁₁(E) + λ₁₁(E^χ) = 2 + 0 = 2——K 侧与 Q 侧 λ 相同，因为二次特征 twist 是 rank 0（非零点情形），λ 贡献为零。
3. **零点情形**：E/ℚ 与 E/K 均为 λ = 2 > 0（Iwasawa 主猜想零点情形）；E^χ 为 λ = 0（非零点情形）。
4. **与 Sha 有限性路线一致**：λ = rank = 2 与"Ш[11^∞] 有限 ⟹ corank 0"的 descent 结构相容（若 p∤ 其他障碍），为 B-6/CH22 框架提供跨素数、跨域的数值一致性背书。

## 5. 产物

- `ms389twist_smoke.gp`（elltwist/ellanalyticrank/M(0) 冒烟）、`ms389twist2.gp`（4G 栈 msfromell）
- 输出：`ms389twist_smoke_out.txt`、`ms389twist2_out.txt`
- 数据锚：`series11_389_check.md`（λ₁₁=2）、`series_points_check.md` §6（rank 0 恒等式校准）
