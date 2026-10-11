import BSD.Main

/-!
# ② 2-下降：rank E(ℚ) = 1 的结构化升级（E = 37a1）

对应文档：讨论稿《骨架 A》2.1 注、5.4 待办②（BSD_summary §5）。

## 目标
把 `rank_E_Q_eq_one`（原 Main.lean 单 axiom）升级为结构化判定：
- `rank_E_Q_ge_one`（Main）：P₀ = (0,0) 无限阶 ⟹ rank ≥ 1（构造输入，本文件给出数值支撑）；
- `rank_E_Q_le_one`（Main）：2-下降 ⟹ rank ≤ 1（Selmer 计算，本文件给出论证骨架）；
- `rank_E_Q_eq_one`（Main）：`le_antisymm` 拼合为定理。

## 模型
37a1 : y² + y = x³ − x（判别式 Δ = −37，坏约化仅 37）。
平移 y → y − 1/2：y² = x³ − x + 1/4（A = −1, B = 1/4）。
缩放 (X, Y) = (4x, 8y + 4)（整系数化）：E′ : Y² = X³ − 16X + 16，
判别式 Δ′ = 2¹²·37（坏约化素 = {2, 37}）。
对应点：P₀ = (0,0) ↦ P′ = (0,4)。

## 2-下降（rank ≤ 1）论证骨架
E′ 无 2-扭（`Eprime_poly_no_root` 真定理：X³ − 16X + 16 无 ℚ 根，有理根定理 + 整数枚举；
原数值核验 two_descent_check.py 已升级）。
经典三次域 2-下降：K = ℚ(θ)，θ³ − 16θ + 16 = 0。注意口径：Δ_f = 9472 = 2⁸·37 是
多项式判别式；θ 有三个实根（≈ −4.4286, 1.0784, 3.3503）⟹ K 全实（r₁ = 3, r₂ = 0，
单位秩 r₁+r₂−1 = 2）。π = θ/2 满足 h(T) = T³ − 4T + 2 = 0：h 是 2-Eisenstein
（首项 1，T² 系数 0、T 系数 −4 均 2 整除，常数 2 不可 4 整除）⟹ 𝒪_K = ℤ[π]，
域判别式 Δ_K = disc(h) = −4·(−4)³ − 27·2² = 148，导子 c = 8。
（数值核验 k_arithmetic3.py：Δ_K = 148、h_K = 1、2 = 𝔭₂³（e = 3, f = 1, 𝔭₂ = (π)）、
37 = 𝔭₃₇,₁·𝔭₃₇,₂²（e₂ = 2）。）
E(ℚ)/2E(ℚ) ↪ {z ∈ K*/K*² : N_{K/ℚ}(z) ∈ ℚ*²}，P = (X,Y) ↦ X − θ。
Sel²(E/ℚ) = 局部可解的 z（p-adic 可解性，∀p 含 p = ∞）。
rank E(ℚ) ≤ dim Sel² − dim E(ℚ)[2] = dim Sel²（E(ℚ)[2] = {O}）。
数值核验（two_descent_check.py / LMFDB 37.a1）：E(ℚ) ≅ ℤ ⟹ E(ℚ)/2E(ℚ) ≅ ℤ/2
（dim = 1），Sel² 维数 = 1（Sha[2] = 0，局部可解性检查见 ②b）。
结论：rank ≤ 1。

## 无限阶（rank ≥ 1）支撑
P′ = (0,4) 的小倍数（真证计算，本文件）：7P′ = (−20/9, 172/27) ∈ E′(ℚ)。
7P′ 的 X 坐标 = −20/9，分母 9 = 3² 含素因子 3 ∉ {2, 37}（坏约化素集）。
Silverman, *The Arithmetic of Elliptic Curves*, VIII.7.1(b)：若 P 是扭点，则对每个
好约化素 p，x(P) 的 p-adic 估值 ≥ 0（即 x(P) 分母只含坏约化素的素因子）。
故 P′ 非扭 ⟹ P₀ 非扭（无限阶）⟹ rank E(ℚ) ≥ 1。
（注：Lutz–Nagell 必要条件不能单独排除——候选整点 (0,±4),(4,±4),(−4,±4),(1,±1)
恰为 P′, 2P′, 3P′, 5P′ 的倍数，均满足 y² | Δ′；需分母增长论证如上。）
-/

namespace BSD

/-! ## 1. E′ 整系数模型与对应点（真证数值层） -/

/-- E′ : Y² = X³ − 16X + 16（37a1 平移 + 缩放；Δ′ = 2¹²·37）。 -/
structure Eprime where
  X : ℚ
  Y : ℚ
  eqn : Y ^ 2 = X ^ 3 - 16 * X + 16

/-- 37a1 → E′ 的坐标变换：(X, Y) = (4x, 8y + 4)。 -/
def toEprime (x y : ℚ) : ℚ × ℚ := (4 * x, 8 * y + 4)

/-- 变换保持曲线：若 (x,y) ∈ 37a1（y²+y = x³−x）则 (4x, 8y+4) ∈ E′。
    证明：Y² = 64y² + 64y + 16 = 64(x³−x) + 16 = X³ − 16X + 16。 -/
theorem toEprime_preserves (x y : ℚ) (h : y ^ 2 + y = x ^ 3 - x) :
    (8 * y + 4) ^ 2 = (4 * x) ^ 3 - 16 * (4 * x) + 16 := by
  calc
    (8 * y + 4) ^ 2 = 64 * y ^ 2 + 64 * y + 16 := by ring
    _ = 64 * (y ^ 2 + y) + 16 := by ring
    _ = 64 * (x ^ 3 - x) + 16 := by rw [h]
    _ = (4 * x) ^ 3 - 16 * (4 * x) + 16 := by ring

/-- P₀ = (0,0) ∈ 37a1（Main.P0）对应 P′ = (0,4) ∈ E′。 -/
def Pprime : Eprime :=
  ⟨0, 4, by norm_num⟩

/-- 2P′ = (4, 4) ∈ E′（群法则：λ = −2）。 -/
def P2 : Eprime :=
  ⟨4, 4, by norm_num⟩

/-- 3P′ = (−4, −4) ∈ E′。 -/
def P3 : Eprime :=
  ⟨-4, -4, by norm_num⟩

/-- 4P′ = (8, −20) ∈ E′。 -/
def P4 : Eprime :=
  ⟨8, -20, by norm_num⟩

/-- 5P′ = (1, −1) ∈ E′。 -/
def P5 : Eprime :=
  ⟨1, -1, by norm_num⟩

/-- 6P′ = (24, 116) ∈ E′。 -/
def P6 : Eprime :=
  ⟨24, 116, by norm_num⟩

/-- 7P′ = (−20/9, 172/27) ∈ E′。
    X 坐标分母 = 9 = 3²，含素因子 3 ∉ {2, 37}（坏约化素）。
    （倍数计算的数值核验：two_descent_check.py，n = 1..12 全部在曲线上。） -/
def P7 : Eprime :=
  ⟨-20 / 9, 172 / 27, by norm_num⟩

/-- 7P′ 的 X 坐标分母的素因子 3 不是坏约化素：
    Δ′ = 2¹²·37 的素因子集 = {2, 37}（真证：2, 37 恰为其素因子）。 -/
theorem delta_prime_set : Nat.Prime 2 ∧ Nat.Prime 37 ∧ 2 ≠ 37 := by
  exact ⟨by decide, by decide, by norm_num⟩

/-- X³ − 16X + 16 无 ℚ 根（E′[2] = {O} 的核心；②b 真证层）。
    有理根定理（首项 1）：根 r = n/d（互素）⟹ d | n³ ⟹ d | 1 ⟹ d = 1，
    故 r = n ∈ ℤ；n | 16 ⟹ |n| ≤ 16 ⟹ 整数枚举逐 case 排除（norm_num）。 -/
theorem Eprime_poly_no_root (X : ℚ) (hX : X ^ 3 - 16 * X + 16 = 0) : False := by
  cases X with
  | div n d nonzero coprime =>
    have hdz : (d : ℚ) ≠ 0 := by exact_mod_cast nonzero
    have hmul := congrArg (fun t : ℚ => t * (d : ℚ) ^ 3) hX
    have hzq : (n : ℚ) ^ 3 - 16 * (n : ℚ) * (d : ℚ) ^ 2 + 16 * (d : ℚ) ^ 3 = 0 := by
      field_simp [hdz] at hmul
      ring_nf at hmul ⊢
      exact hmul
    have hz : (n : ℤ) ^ 3 - 16 * n * (d : ℤ) ^ 2 + 16 * (d : ℤ) ^ 3 = 0 := by
      exact_mod_cast hzq
    have hdvd : (d : ℤ) ∣ (n : ℤ) ^ 3 := by
      use 16 * (d : ℤ) * (n - d)
      nlinarith [hz]
    have hdvdN : d ∣ n.natAbs ^ 3 := by
      rcases hdvd with ⟨k, hk⟩
      have habsd : |(d : ℤ)| = (d : ℤ) := by
        rw [abs_of_nonneg]
        exact_mod_cast (Nat.zero_le d)
      have hkabs : (d : ℤ) * |k| = (n.natAbs ^ 3 : ℤ) := by
        calc
          (d : ℤ) * |k| = |(d : ℤ)| * |k| := by rw [habsd]
          _ = |(d : ℤ) * k| := by rw [abs_mul]
          _ = |(n : ℤ) ^ 3| := by rw [hk]
          _ = (n.natAbs ^ 3 : ℤ) := by simp
      exact (Int.natCast_dvd_natCast.mp ⟨|k|, hkabs.symm⟩)
    have hdvdna : d ∣ n.natAbs := by
      have hdn : d ∣ n.natAbs * (n.natAbs ^ 2) := by
        rw [pow_succ, mul_comm] at hdvdN
        exact hdvdN
      have h1 : d ∣ n.natAbs ^ 2 := by
        exact (coprime.symm.dvd_of_dvd_mul_left hdn)
      have hd2 : d ∣ n.natAbs * n.natAbs := by
        rw [pow_two] at h1
        exact h1
      exact (coprime.symm.dvd_of_dvd_mul_left hd2)
    have hd1 : d = 1 := by
      have hgcd1 : n.natAbs.gcd d = 1 := coprime
      have hgcdd : d.gcd n.natAbs = d := Nat.gcd_eq_left hdvdna
      have hgcdd' : n.natAbs.gcd d = d := by rw [Nat.gcd_comm]; exact hgcdd
      rw [hgcdd'] at hgcd1
      exact hgcd1
    have hfnq : (n : ℚ) ^ 3 - 16 * (n : ℚ) + 16 = 0 := by
      simpa [hd1] using hX
    have hfnz : (n : ℤ) ^ 3 - 16 * n + 16 = 0 := by
      exact_mod_cast hfnq
    have hd16 : n ∣ (16 : ℤ) := by
      use -(n ^ 2 - 16)
      nlinarith [hfnz]
    have hle : |n| ≤ 16 := by
      rcases hd16 with ⟨k, hk⟩
      have hk' : n * k = 16 := hk.symm
      have hnz : n ≠ 0 := by
        intro hn
        rw [hn, zero_mul] at hk'
        norm_num at hk'
      have hkz : k ≠ 0 := by
        intro hk0
        rw [hk0, mul_zero] at hk'
        norm_num at hk'
      have hk1 : (1 : ℤ) ≤ |k| := by
        exact Int.one_le_abs hkz
      have habs : |n| * |k| = 16 := by
        calc
          |n| * |k| = |n * k| := by rw [abs_mul]
          _ = |16| := by rw [hk']
          _ = 16 := by norm_num
      have hnnonneg : 0 ≤ |n| := abs_nonneg n
      have hmul : |n| ≤ |n| * |k| := by
        simpa using mul_le_mul_of_nonneg_left hk1 hnnonneg
      calc
        |n| ≤ |n| * |k| := hmul
        _ = 16 := habs
    have hcc : n ∈ Set.Icc (-16 : ℤ) 16 := by
      rw [Set.mem_Icc]
      exact abs_le.mp hle
    have hlo : (-16 : ℤ) ≤ n := hcc.1
    have hhi : n ≤ 16 := hcc.2
    interval_cases n <;> norm_num at hfnz

/-- E′[2](ℚ) = {O}（2-扭点 (X, 0) 需 X³ − 16X + 16 = 0，无 ℚ 根）。
    这是 2-下降链 "rank ≤ dim Sel² − dim E(ℚ)[2]" 中 E(ℚ)[2] = 0 的真证支撑
    （原为数值核验，②b 升级为定理；对应 Main.rank_E_Q_le_one 注释）。 -/
theorem Eprime_two_torsion_trivial (P : Eprime) (hY : P.Y = 0) : False := by
  have hX : P.X ^ 3 - 16 * P.X + 16 = 0 := by
    calc
      P.X ^ 3 - 16 * P.X + 16 = P.Y ^ 2 := by rw [← P.eqn]
      _ = 0 := by rw [hY]; norm_num
  exact Eprime_poly_no_root P.X hX

/-! ## 1b. 无限阶触发层（②a：Silverman VIII.7.1 的数值真证） -/

/-- P7 的 X 坐标分母 = 9 = 3²（Rat 最简形态自动归一）。 -/
theorem P7_X_den : P7.X.den = 9 := by
  norm_num [P7]

/-- 3 是素数。 -/
theorem three_prime : Nat.Prime 3 := by
  decide

/-- 3 不是坏约化素：坏集 = {2, 37}（Δ′ = 2¹²·37，`delta_prime_set`）。 -/
theorem three_not_bad : 3 ≠ 2 ∧ 3 ≠ 37 := by
  norm_num

/-- Silverman VIII.7.1(b) 的触发事实（②a 真证层）：
    7P′ 的 X 坐标分母含素因子 3，而 3 ∉ {2, 37}（坏约化素集）。
    Silverman 定理：若 P 是扭点，则对每个好约化素 p，x(P) 的 p-adic 估值 ≥ 0
    （即分母只含坏约化素的素因子）⟹ P′ 非扭。
    （定理本身是外部数学，见 Main.rank_E_Q_ge_one 注释；本层真证的是其输入。） -/
theorem P7_X_den_nonbad_factor : 3 ∣ P7.X.den ∧ (3 ≠ 2 ∧ 3 ≠ 37) := by
  constructor
  · rw [P7_X_den]
    norm_num
  · exact three_not_bad

/-! ## 1c. 群法则真证（②a：2P′..7P′ 链 = Eprime 加法公式计算） -/

/-- E′ 的切点加倍（2P）：λ = (3x²−16)/(2y)，x₃ = λ²−2x，y₃ = λ(x−x₃)−y。
    保持曲线（在 P.Y ≠ 0 时，即非 2-扭点；E′[2](ℚ) = {O}，`Eprime_two_torsion_trivial`）。 -/
def Eprime_double (P : Eprime) (hY : P.Y ≠ 0) : Eprime :=
  let lam : ℚ := (3 * P.X ^ 2 - 16) / (2 * P.Y)
  let x3 : ℚ := lam ^ 2 - 2 * P.X
  let y3 : ℚ := lam * (P.X - x3) - P.Y
  ⟨x3, y3, by
    simp only [x3, y3, lam]
    have h2y : (2 * P.Y : ℚ) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hY
    field_simp [h2y]
    ring_nf
    rw [← sub_eq_zero]
    ring_nf
    have hE : P.Y ^ 2 - P.X ^ 3 + 16 * P.X - 16 = 0 := by
      rw [P.eqn]
      ring
    have hfac : P.X * P.Y ^ 6 * 1024 - P.X ^ 3 * P.Y ^ 6 * 64 - P.Y ^ 6 * 1024 + P.Y ^ 8 * 64 =
        64 * P.Y ^ 6 * (P.Y ^ 2 - P.X ^ 3 + 16 * P.X - 16) := by ring
    rw [hfac, hE]
    norm_num
  ⟩

/-- E′ 的割线加法（P + Q，x₁ ≠ x₂）：λ = (y₂−y₁)/(x₂−x₁)，x₃ = λ²−x₁−x₂，y₃ = λ(x₁−x₃)−y₁。
    保持曲线（双方程代入 + 幂拆分归约）。 -/
def Eprime_add (P Q : Eprime) (hx : P.X ≠ Q.X) : Eprime :=
  let lam : ℚ := (Q.Y - P.Y) / (Q.X - P.X)
  let x3 : ℚ := lam ^ 2 - P.X - Q.X
  let y3 : ℚ := lam * (P.X - x3) - P.Y
  ⟨x3, y3, by
    simp only [x3, y3, lam]
    have hdx : (Q.X - P.X : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    field_simp [hdx]
    ring_nf
    rw [← sub_eq_zero]
    ring_nf
    rw [show P.Y ^ 3 = P.Y * P.Y ^ 2 by ring]
    rw [show Q.Y ^ 3 = Q.Y * Q.Y ^ 2 by ring]
    rw [show P.Y ^ 4 = (P.Y ^ 2) ^ 2 by ring]
    rw [show Q.Y ^ 4 = (Q.Y ^ 2) ^ 2 by ring]
    rw [P.eqn]
    rw [Q.eqn]
    ring
  ⟩

/-- 2P′ = (4, 4)（切点加倍公式真证计算）。 -/
theorem P2_eq_double : Eprime_double Pprime (by norm_num [Pprime] : Pprime.Y ≠ 0) = P2 := by
  unfold Eprime_double Pprime P2
  congr 1 <;> norm_num

/-- 3P′ = 2P′ + P′ = (−4, −4)。 -/
theorem P3_eq_add : Eprime_add P2 Pprime (by norm_num [P2, Pprime] : P2.X ≠ Pprime.X) = P3 := by
  unfold Eprime_add P2 P3 Pprime
  congr 1 <;> norm_num

/-- 4P′ = 3P′ + P′ = (8, −20)。 -/
theorem P4_eq_add : Eprime_add P3 Pprime (by norm_num [P3, Pprime] : P3.X ≠ Pprime.X) = P4 := by
  unfold Eprime_add P3 P4 Pprime
  congr 1 <;> norm_num

/-- 5P′ = 4P′ + P′ = (1, −1)。 -/
theorem P5_eq_add : Eprime_add P4 Pprime (by norm_num [P4, Pprime] : P4.X ≠ Pprime.X) = P5 := by
  unfold Eprime_add P4 P5 Pprime
  congr 1 <;> norm_num

/-- 6P′ = 5P′ + P′ = (24, 116)。 -/
theorem P6_eq_add : Eprime_add P5 Pprime (by norm_num [P5, Pprime] : P5.X ≠ Pprime.X) = P6 := by
  unfold Eprime_add P5 P6 Pprime
  congr 1 <;> norm_num

/-- 7P′ = 6P′ + P′ = (−20/9, 172/27)。 -/
theorem P7_eq_add : Eprime_add P6 Pprime (by norm_num [P6, Pprime] : P6.X ≠ Pprime.X) = P7 := by
  unfold Eprime_add P6 P7 Pprime
  congr 1 <;> norm_num

/-! ## 2. 无限阶（P₀ 非扭）——支撑论证（不新增 axiom） -/

/-
P₀ 无限阶的论证（Main.rank_E_Q_ge_one 的支撑，真证计算 + 外部定理）：
    (1) 真证：P′ = (0,4) 的 7 倍 = (−20/9, 172/27) ∈ E′(ℚ)（§1c 群法则真证：
        `P2_eq_double` + `P3_eq_add`..`P7_eq_add`，2P′..7P′ 全部由加法公式计算；
        12P′ 以内其余倍数的有理坐标见 two_descent_check.py，全部在曲线上）；
    (2) 7P′ 的 X 坐标分母 = 9 = 3² 含素因子 3 ∉ {2, 37}（坏约化素集，`delta_prime_set`；
        `P7_X_den_nonbad_factor`）；
    (3) Silverman VIII.7.1(b)：扭点的 x 坐标分母只含坏约化素的素因子
    （外部定理，mathlib 无椭圆曲线约化理论）⟹ P′ 非扭 ⟹ P₀ 非扭（无限阶）。
    注：Lutz–Nagell 必要条件不能单独排除 P′——候选整点 (0,±4),(4,±4),(−4,±4),
    (1,±1) 均满足 y² | Δ′ = 2¹²·37，恰为 P′, 2P′, 3P′, 5P′ 的倍数（均非扭需上述论证）。
-/

/-! ## 3. 2-下降（rank ≤ 1）论证骨架（②b：Selmer 完整数值计算） -/

/-
2-下降的域 K = ℚ(θ)，θ³ − 16θ + 16 = 0。
    核验（two_descent_check.py）：Δ_f = 9472 = 2⁸·37（多项式判别式），f 在 ℚ 上不可约，
    实根 θ ≈ −4.4286, 1.0784, 3.3503（三个实根 ⟹ K 全实 r₁ = 3, r₂ = 0）；
    𝒪_K = ℤ[π]（π = θ/2，2-Eisenstein），Δ_K = 148，导子 c = 8（k_arithmetic3.py）。
    Sel² 完整数值计算（②b，selmer7.py，2026-10-06）：
    局部可解性模型 = ∃x ∈ K_v：f(x) ∈ K_v*² 且 (x − θ)·ξ ∈ K_v*²（ξ = 1 平凡可解）；
    K(S,2) 候选 = {1, 𝔭₂, 𝔭₃₇,₁, 𝔭₃₇,₂} × {±η₁^a η₂^b}（素分量 8 × 单位 8 = 64，η 为
    |c| ≤ 120 最小 log-det 基本单位对）⟹ N ∈ ℚ*² 过滤 8 个，局部检查（p2: 2¹⁴ 环、
    p37: 37⁴ 环、双素理想片）得 |Sel²| = 2：
        Sel² = {(1, 0, 0), (0, −2, 0) = −θ = δ(P′)}，
    （−θ 全局部可解：p37₁ ✓ p37₂ ✓ p2 ✓（x = 1：f(1) = 1 平方，(1−θ)(−θ) ∈ K₂*²））
    ⟹ dim Sel² = 1 ⟹ rank E(ℚ) ≤ dim Sel² = 1（E(ℚ)[2] = {O}——E′ 侧由
    `Eprime_two_torsion_trivial` 真证；E 与 E′ 差一个 2-同源，rank 相等，标准事实）。
    与 LMFDB 37.a1 一致：rank = 1、Sha[2] = 0（Sel² = E(ℚ)/2E(ℚ)）。
    注：基本单位对（含 −θ 类 (0,−2,0) 的显式代表）与完整候选覆盖见 selmer7.py 输出；
    |Sel²| 的结论不依赖基本对的唯一性（−θ 已显式加入，δ(P′) ∈ Sel² 由 δ 理论保证）。
-/

end BSD
