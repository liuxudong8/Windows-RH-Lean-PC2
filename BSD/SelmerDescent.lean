import BSD.SymmetryReduction

/-!
# Selmer descent 挂账：正合列 0 → Sel(E) → Sel(E/K) → Sel(E⁵)（BSD.SelmerDescent）

任务 3：二次 descent 的 Sel 层形式化。数学上全部是**标准定理**（无条件），
Lean 因缺代数数论库（Selmer 群、descent 理论）而按**定理级挂账**，与
Kolyvagin（`BSD.SymmetryReduction.sha_finite_E_of_rank_le_one` 等）同层。

## 分层

1. **对象层**：Selmer p^∞ 有限性命题（ℚ 侧 / E⁵ 侧 / K 侧），
   与 `BSD.SymmetryReduction.ShaFiniteE/E5/EK` 同类。

2. **二次 descent 正合列（挂账 axiom，数学定理）**：
   0 → Sel(E,ℚ,p^∞) → Sel(E/K,p^∞) → Sel(E⁵,ℚ,p^∞) → 0
   （坏 p 处有限修正）。推论：两端 Sel 有限 ⟹ K 侧 Sel 有限
   （正合列中间群的有限性由两端给出）——`selmer_finite_EK_of_both`。

3. **descent 序列（挂账 axiom，数学定理）**：
   0 → E(K)/p^n ·E(K) → Selⁿ(E/K) → Sha(E/K)[p^n] → 0，
   逐 n 成立；由此 Selmer p^∞ 有限 ⟹ Sha(E/K) 有限——
   `sha_finite_of_selmer_finite`。

4. **Kolyvagin 的 Selmer 形式（挂账 axiom，数学定理）**：
   解析秩 ≤ 1 ⟹ Sel(E/ℚ,p^∞) 有限（欧拉系统控制 Selmer 群）——
   `sel_finite_E_of_rank_le_one` / `sel_finite_E5_of_rank_le_one`。

## 组装

`sha_finite_EK_of_selmer_descent`（泛型，前提 两侧解析秩 = 1）与
`sha_finite_EK_11_via_selmer`（(1,1) 型对象级，前提 两侧解析秩 = 1）：
Kolyvagin（Selmer 形式）×2 ⟹ 两侧 Sel 有限 ⟹（正合列）K 侧 Sel 有限
⟹（descent 序列）K 侧 Sha 有限——即 `BSD.SymmetryReduction.ShaFiniteEK`。

闭包预期（#print axioms 实测见 _check_selmer_descent.lean）：
- 全部结论只依赖本模块对象层 axiom（Selmer 有限性 + 正合列 + descent 序列
  + Kolyvagin Selmer 形式），**不含 bsd_formula_rank_\*、不含 GRH**；
  挂账层级与 SymmetryReduction 的 Kolyvagin/descent 完全一致（数学定理级）。
-/

namespace BSD.SelmerDescent

noncomputable section

/-! ## 1. 对象层：Selmer p^∞ 有限性命题 -/

/-- Selmer p^∞ 有限性（ℚ 侧）。数学语义：Sel(E,ℚ,p^∞) 有限。 -/
axiom SelFiniteE : Prop

/-- Selmer p^∞ 有限性（E⁵ 侧）。 -/
axiom SelFiniteE5 : Prop

/-- Selmer p^∞ 有限性（K 侧）。 -/
axiom SelFiniteEK : Prop

/-! ## 2. 二次 descent 正合列（数学定理级挂账） -/

/-- **二次 descent 正合列**（挂账 axiom，数学定理）：
    0 → Sel(E,ℚ,p^∞) → Sel(E/K,p^∞) → Sel(E⁵,ℚ,p^∞) → 0
    （坏 p 处有限修正；χ-不变子群 / χ-反不变商）。
    推论（标准）：两端 Sel 有限 ⟹ 中间 Sel 有限。
    数学依据：Gal(K/ℚ) 特征分解下的 Selmer 群长正合列——无条件定理；
    Lean 缺代数数论库（Selmer 群、descent 理论），挂账。 -/
axiom selmer_finite_EK_of_both : SelFiniteE → SelFiniteE5 → SelFiniteEK

/-! ## 3. descent 序列：Sel 有限 ⟹ Sha 有限（数学定理级挂账） -/

/-- **descent 序列**（挂账 axiom，数学定理）：
    0 → E(K)/p^n·E(K) → Selⁿ(E/K) → Sha(E/K)[p^n] → 0 逐 n 成立；
    故 Selmer p^∞ 有限 ⟹ Sha(E/K) 有限。
    数学依据：经典 descent 正合列 + 挠群结构（Kummer 理论）——无条件定理；
    Lean 缺代数数论库，挂账。 -/
axiom sha_finite_of_selmer_finite : SelFiniteEK → BSD.SymmetryReduction.ShaFiniteEK

/-! ## 4. Kolyvagin 的 Selmer 形式（数学定理级挂账） -/

/-- Kolyvagin（Selmer 形式，ℚ 侧）：解析秩 ≤ 1 ⟹ Sel(E/ℚ,p^∞) 有限。
    欧拉系统控制 Selmer 群；模曲线类内已证。 -/
axiom sel_finite_E_of_rank_le_one : BSD.Positivity.zeroOrderE ≤ 1 → SelFiniteE

/-- Kolyvagin（Selmer 形式，E⁵ 侧）。 -/
axiom sel_finite_E5_of_rank_le_one : BSD.Positivity.zeroOrderE5 ≤ 1 → SelFiniteE5

/-! ## 5. 组装：K 侧 Sha 有限（Sel 层 descent 链） -/

/-- 泛型组装：两侧解析秩 = 1 ⟹ Sha(E/K) 有限。
    链：Kolyvagin（Selmer 形式）×2 ⟹ 两侧 Sel 有限 ⟹（正合列）K 侧 Sel 有限
    ⟹（descent 序列）K 侧 Sha 有限。 -/
theorem sha_finite_EK_of_selmer_descent (hE1 : BSD.Positivity.zeroOrderE = 1)
    (hE5_1 : BSD.Positivity.zeroOrderE5 = 1) : BSD.SymmetryReduction.ShaFiniteEK := by
  exact sha_finite_of_selmer_finite
    (selmer_finite_EK_of_both
      (sel_finite_E_of_rank_le_one (by simp [hE1]))
      (sel_finite_E5_of_rank_le_one (by simp [hE5_1])))

/-- (1,1) 型对象级组装：与 `BSD.SymmetryReduction.sha_finite_EK_of_both`
    结论一致（两侧秩 1 ⟹ Sha(E/K) 有限），但有限性来源走 Sel 层 descent 链
    （正合列 + descent 序列），比 Kolyvagin 直接形式更细一层。 -/
theorem sha_finite_EK_11_via_selmer (hE1 : BSD.Positivity.zeroOrderE = 1)
    (hE5_1 : BSD.Positivity.zeroOrderE5 = 1) : BSD.SymmetryReduction.ShaFiniteEK :=
  sha_finite_EK_of_selmer_descent hE1 hE5_1

end

end BSD.SelmerDescent
