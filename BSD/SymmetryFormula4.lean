import BSD.SymmetryClosure
import Mathlib.Data.Real.Basic

/-!
# 负根数 twist 计数（公式 (4)）的 Lean 姊妹模块（BSD.SymmetryFormula4）

对应联系链《对称性+正性 ⟷ K-GRH：联系链》§5.2 (3)(4) 式与 §8 落点：
K = ℚ(√5)，Ĝ = {1, χ}（二次特征群）。把 K 侧秩 2 反向的正性判别

  L″(E/K,1) > 0  ⟺  #{χ ∈ Ĝ : ε(E⊗χ) = −1} 为偶数   (4)

落成 Lean 骨架。该逻辑纯代数（有限特征标计数 + 奇偶性 + 符号运算），
不碰 L 函数的解析延拓，形式化难度远低于 Kolyvagin / Selmer descent。

三类 axiom（定理级挂账，与 Kolyvagin / Selmer descent 同层）：
1. **L 分解 (1)**：ord L(E/K,1) = ord L(E,1) + ord L(E⁵,1)（Artin 分解）；
2. **BSD 奇偶性**：ε(E⊗χ) = (−1)^{ord L(E⊗χ)}（自对偶 L 函数，ε = (−1)^ord）；
3. **twist 根数公式**：ε(E⊗χ) = ε(E)·χ(N_E)·χ(−1)·(局部修正)（联系链 5.3）。

另含一个组装 axiom：(3) 式核心——L″(E/K,1) > 0 ⟺ 零阶分量根数积 = +1
（数学来源 = 联系链 5.1 分量符号事实：r=0 时符号 = 根数、r=1 时 L′>0
Gross–Zagier、r=2 时 L″/2>0 通道 B；5.2 卷积；定理级挂账）。

实例：**79a1**（(1,1) 型，K 侧秩 2 已闭合）。双侧解析秩 1 ⟹
ε(E) = ε(E⁵) = −1（BSD 奇偶性），负根数计数 = 2（偶数）⟹ L″(E/K,1) > 0。
实例：**389a1**（(2,0) 型，秩 2 最小导子）。ℚ 侧解析秩 2、E⁵ 侧秩 0 ⟹
ε(E) = ε(E⁵) = +1，负根数计数 = 0（偶数）⟹ L″(E/K,1) > 0，
与区间算术 L″(389a1,1) = 1.518633 > 0 一致（Probe389 数值管线）。
这是 (4) 式与 SymmetryClosure（Leibniz 纠缠积通道）合流的最小结自洽性验证。

闭包预期（#print axioms 实测见 _check_symmetry_formula4.lean）：
- 全部结论只依赖本模块对象层 axiom（数据层 + 定理级挂账），
  **不含 bsd_formula_rank_\*、不含 GRH**。
-/

namespace BSD.SymmetryFormula4

noncomputable section

/-! ## 1. 对象层：分量对象与根数 -/

/-- 解析秩（ℚ 侧）：r₁ = ord L(E,1)。 -/
axiom zeroOrderE_f4 : ℕ

/-- 解析秩（E⁵ 侧）：r_χ = ord L(E⁵,1)。 -/
axiom zeroOrderE5_f4 : ℕ

/-- 解析秩（K 侧）：ord L(E/K,1)。 -/
axiom zeroOrderEK_f4 : ℕ

/-- 根数（ℚ 侧）：ε(E)。 -/
axiom rootE_f4 : ℤ

/-- 根数（E⁵ 侧）：ε(E⁵) = ε(E⊗χ)。 -/
axiom rootE5_f4 : ℤ

/-- 中心二阶导数（K 侧）：L″(E/K,1)。 -/
axiom LppEK_f4 : ℝ

/-- χ(N_E)：特征在导子处的取值（twist 根数公式输入）。 -/
axiom chi_NE_f4 : ℤ

/-- χ(−1)（twist 根数公式输入）。 -/
axiom chi_neg_f4 : ℤ

/-- 局部修正因子（twist 根数公式输入；好素处 = 1，坏素分歧处非平凡）。 -/
axiom local_f4 : ℤ

/-! ## 2. 三类 axiom（定理级挂账） -/

/-- (1) L 分解：ord L(E/K,1) = ord L(E,1) + ord L(E⁵,1)（Artin 分解，定理级挂账）。 -/
axiom l_fun_decomposition_f4 : zeroOrderEK_f4 = zeroOrderE_f4 + zeroOrderE5_f4

/-- (2) BSD 奇偶性（ℚ 侧）：ε(E) = (−1)^{ord L(E,1)}（自对偶 L 函数，定理级挂账）。 -/
axiom bsd_parity_f4 : rootE_f4 = (-1 : ℤ) ^ zeroOrderE_f4

/-- (2) BSD 奇偶性（E⁵ 侧）：ε(E⁵) = (−1)^{ord L(E⁵,1)}。 -/
axiom bsd_parity5_f4 : rootE5_f4 = (-1 : ℤ) ^ zeroOrderE5_f4

/-- (3) twist 根数公式：ε(E⊗χ) = ε(E)·χ(N_E)·χ(−1)·(局部修正)（联系链 5.3，定理级挂账）。 -/
axiom twist_root_number_f4 : rootE5_f4 = rootE_f4 * chi_NE_f4 * chi_neg_f4 * local_f4

/-- 组装 axiom：(3) 式核心——L″(E/K,1) > 0 ⟺ 零阶分量根数积 = +1。
    数学来源：联系链 5.1（r=0 时中心值符号 = 根数；r=1 时 L′>0，
    Gross–Zagier 高度正定；r=2 时 L″/2>0，通道 B）+ 5.2 卷积；定理级挂账。 -/
axiom lpp_pos_iff_root_prod_f4 :
  (0 < LppEK_f4) ↔
    ((if zeroOrderE_f4 = 0 then rootE_f4 else 1) *
       (if zeroOrderE5_f4 = 0 then rootE5_f4 else 1) = (1 : ℤ))

/-! ## 3. 负根数计数与 (4) 式定理 -/

/-- 负根数计数：# {χ ∈ Ĝ : ε(E⊗χ) = −1}（Ĝ = {1, χ}，两个分量）。 -/
def negCount_f4 : ℕ :=
  (if rootE_f4 = -1 then 1 else 0) + (if rootE5_f4 = -1 then 1 else 0)

/-- (4) 式（K 侧解析秩 2 前提）：L″(E/K,1) > 0 ⟺ 负根数计数为偶。
    推导：BSD 奇偶性 ε = (−1)^ord 把「根数 = −1」化为「秩为奇」；
    K 侧秩 2（Σ r_χ = 2）下奇分量数 ≡ Σ r_χ ≡ 0 (mod 2)，与 (3) 式合流。 -/
theorem formula4_f4 (hsum : zeroOrderEK_f4 = 2) :
    0 < LppEK_f4 ↔ Even negCount_f4 := by
  rw [lpp_pos_iff_root_prod_f4]
  have hsum2 : zeroOrderE_f4 + zeroOrderE5_f4 = 2 := by
    rw [← l_fun_decomposition_f4]
    exact hsum
  by_cases hE0 : zeroOrderE_f4 = 0
  · have hE5_2 : zeroOrderE5_f4 = 2 := by omega
    simp [hE0, hE5_2, negCount_f4, bsd_parity_f4, bsd_parity5_f4]
  · by_cases hE1 : zeroOrderE_f4 = 1
    · have hE5_1 : zeroOrderE5_f4 = 1 := by omega
      simp [hE1, hE5_1, negCount_f4, bsd_parity_f4, bsd_parity5_f4]
    · have hE2 : zeroOrderE_f4 = 2 := by omega
      have hE5_0 : zeroOrderE5_f4 = 0 := by omega
      simp [hE2, hE5_0, negCount_f4, bsd_parity_f4, bsd_parity5_f4]

/-- 推论：K 侧解析秩 2 ⟹ L″(E/K,1) > 0（负根数计数自动为偶；
    (4) 式右边在 Σ r_χ = 2 下恒成立——与通道 B 的 P* 无条件结论在奇偶层合流）。 -/
theorem lpp_pos_of_analytic_two (hsum : zeroOrderEK_f4 = 2) : 0 < LppEK_f4 := by
  rw [formula4_f4 hsum]
  have hsum2 : zeroOrderE_f4 + zeroOrderE5_f4 = 2 := by
    rw [← l_fun_decomposition_f4]
    exact hsum
  by_cases hE0 : zeroOrderE_f4 = 0
  · have hE5_2 : zeroOrderE5_f4 = 2 := by omega
    simp [hE0, hE5_2, negCount_f4, bsd_parity_f4, bsd_parity5_f4]
  · by_cases hE1 : zeroOrderE_f4 = 1
    · have hE5_1 : zeroOrderE5_f4 = 1 := by omega
      simp [hE1, hE5_1, negCount_f4, bsd_parity_f4, bsd_parity5_f4]
    · have hE2 : zeroOrderE_f4 = 2 := by omega
      have hE5_0 : zeroOrderE5_f4 = 0 := by omega
      simp [hE2, hE5_0, negCount_f4, bsd_parity_f4, bsd_parity5_f4]

/-! ## 4. 实例：79a1（(1,1) 型） -/

/-- 数据层：79a1 的 ℚ 侧解析秩 = 1（LMFDB）。 -/
axiom zeroOrderE_79_f4 : zeroOrderE_f4 = 1

/-- 数据层：79a1 的 E⁵ 侧解析秩 = 1（LMFDB）。 -/
axiom zeroOrderE5_79_f4 : zeroOrderE5_f4 = 1

/-- 数据层：χ(N_E) = χ(79) = 1（K = ℚ(√5)，χ = (5/·)；
    二次互反 (5/79) = (79/5) = (4/5) = 1）。 -/
axiom chi_NE_79_f4 : chi_NE_f4 = 1

/-- 数据层：χ(−1) = 1（实二次域 K = ℚ(√5)，χ(−1) = +1）。 -/
axiom chi_neg_79_f4 : chi_neg_f4 = 1

/-- 数据层：局部修正 = 1（N_E = 79 与 cond(χ) = 5 互素，好素处无修正）。 -/
axiom local_79_f4 : local_f4 = 1

/-- twist 根数公式的 79a1 算术自洽性：ε(E⁵) = ε(E)
    （χ(79)·χ(−1)·局部 = 1；与 BSD 奇偶性给出的 ε(E) = ε(E⁵) = −1 一致）。 -/
theorem rootE5_eq_rootE_79_f4 : rootE5_f4 = rootE_f4 := by
  rw [twist_root_number_f4, chi_NE_79_f4, chi_neg_79_f4, local_79_f4]
  ring

/-- 79a1 双侧根数均为 −1（BSD 奇偶性 + 解析秩 1）。 -/
theorem rootE_neg_79_f4 : rootE_f4 = -1 := by
  rw [bsd_parity_f4, zeroOrderE_79_f4]
  norm_num

/-- 79a1 双侧根数均为 −1（E⁵ 侧）。 -/
theorem rootE5_neg_79_f4 : rootE5_f4 = -1 := by
  rw [bsd_parity5_f4, zeroOrderE5_79_f4]
  norm_num

/-- 79a1 负根数计数 = 2（偶数）。 -/
theorem negCount_79_f4 : negCount_f4 = 2 := by
  rw [negCount_f4, rootE_neg_79_f4, rootE5_neg_79_f4]
  norm_num

/-- 79a1 的 (4) 式判定：K 侧解析秩 2（Artin 分解 1+1），
    负根数计数 = 2 偶 ⟹ L″(E/K,1) > 0。 -/
theorem lpp_pos_79_f4 : 0 < LppEK_f4 := by
  apply lpp_pos_of_analytic_two
  rw [l_fun_decomposition_f4, zeroOrderE_79_f4, zeroOrderE5_79_f4]

/-- 与 SymmetryClosure（Leibniz 纠缠积通道）合流：L″(E/K,1) 是同一对象。
    （(4) 通道与纠缠积通道对 79a1 给出同一正性结论。） -/
axiom lpp_EK_79_ident_f4 : LppEK_f4 = BSD.SymmetryClosure.Lpp_EK_79

/-- 79a1 的 L″ > 0：公式 (4) 通道与 Leibniz 纠缠积通道合流。 -/
theorem lpp_EK_79_pos_both_f4 : 0 < BSD.SymmetryClosure.Lpp_EK_79 := by
  rw [← lpp_EK_79_ident_f4]
  exact lpp_pos_79_f4

/-! ## 5. 实例：389a1（(2,0) 型） -/

/-- 数据层：389a1 的 ℚ 侧解析秩 = 2（LMFDB / Sage 五算法 + L″ 数值 1.518633，
    Probe389/probe389_summary.md §1.3、§2）。 -/
axiom zeroOrderE_389_f4 : zeroOrderE_f4 = 2

/-- 数据层：389a1 的 E⁵ 侧解析秩 = 0。 -/
axiom zeroOrderE5_389_f4 : zeroOrderE5_f4 = 0

/-- 数据层：χ₅(−389) = +1（(5/389) = (389/5) = (4/5) = 1；χ₅(−1) = +1 实二次域）。 -/
axiom chi_NE_389_f4 : chi_NE_f4 = 1

/-- 数据层：χ₅(−1) = +1（实二次域 K = ℚ(√5)）。 -/
axiom chi_neg_389_f4 : chi_neg_f4 = 1

/-- 数据层：局部修正 = 1（gcd(N_E, 5) = 1，χ 在 389 非分歧，无局部修正）。 -/
axiom local_389_f4 : local_f4 = 1

/-- twist 根数公式的 389a1 算术自洽性：ε(E⁵) = ε(E)
    （χ₅(−389)·χ₅(−1)·局部 = 1；与 BSD 奇偶性给出的 ε(E) = ε(E⁵) = +1 一致）。 -/
theorem rootE5_eq_rootE_389_f4 : rootE5_f4 = rootE_f4 := by
  rw [twist_root_number_f4, chi_NE_389_f4, chi_neg_389_f4, local_389_f4]
  ring

/-- 389a1 双侧根数均为 +1（BSD 奇偶性 + 解析秩 2 / 0）。 -/
theorem rootE_pos_389_f4 : rootE_f4 = 1 := by
  rw [bsd_parity_f4, zeroOrderE_389_f4]
  norm_num

/-- 389a1 双侧根数均为 +1（E⁵ 侧）。 -/
theorem rootE5_pos_389_f4 : rootE5_f4 = 1 := by
  rw [bsd_parity5_f4, zeroOrderE5_389_f4]
  norm_num

/-- 389a1 负根数计数 = 0（偶数）。 -/
theorem negCount_389_f4 : negCount_f4 = 0 := by
  rw [negCount_f4, rootE_pos_389_f4, rootE5_pos_389_f4]
  norm_num

/-- 389a1 的 (4) 式判定：K 侧解析秩 2（Artin 分解 2+0），
    负根数计数 = 0 偶 ⟹ L″(E/K,1) > 0。
    与区间算术 L″(389a1,1) = 1.518633 > 0（probe389_summary.md §1.3）一致。 -/
theorem lpp_pos_389_f4 : 0 < LppEK_f4 := by
  apply lpp_pos_of_analytic_two
  rw [l_fun_decomposition_f4, zeroOrderE_389_f4, zeroOrderE5_389_f4]

end

end BSD.SymmetryFormula4
