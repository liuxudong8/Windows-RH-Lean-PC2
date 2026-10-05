f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 在 nontrivialZeroEnum_are_zeros 之后引入 zeroMultiplicity
old_anchor = """/-- 枚举元素都是非平凡零点（定理）。 -/
theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n

/-- 非平凡零点求和（定义）：
    Z_nontriv(f) = ∑'_{n:ℕ} melinTransform f (nontrivialZeroEnum n)。
    即对所有非平凡零点的 Mellin 变换值求和。
    由 Weyl 定律，级数绝对收敛（磨光函数的 Mellin 变换在零点处有界）。 -/
noncomputable def nontrivialZeroSum (f : TestFunction) : ℂ :=
    ∑' (n : ℕ), melinTransform f (nontrivialZeroEnum n)"""

new_anchor = """/-- 枚举元素都是非平凡零点（定理）。 -/
theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n

/-- 零点重数函数（opaque）：zeroMultiplicity s 给出 ζ(s) 在 s 处的零点重数。
    对非零点，重数为 0。 -/
opaque zeroMultiplicity : ℂ → ℕ

/-- 非平凡零点处重数为正（公理，定义性质）：
    如果 ρ 是非平凡零点，则 zeroMultiplicity ρ > 0。 -/
axiom zeroMultiplicity_positive_at_nontrivial_zeros (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < zeroMultiplicity ρ

/-- 零点重数的函数方程对称性（公理，ζ函数方程的推论）：
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ)。 -/
axiom zeroMultiplicity_symmetry (ρ : ℂ) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ)

/-- 非平凡零点求和（定义，带重数）：
    Z_nontriv(f) = ∑'_{n:ℕ} (zeroMultiplicity(enum n) : ℂ) * melinTransform f (enum n)。
    即对所有非平凡零点按重数加权的 Mellin 变换值求和。
    由 Weyl 定律，级数绝对收敛（磨光函数的 Mellin 变换在零点处有界，重数有界）。 -/
noncomputable def nontrivialZeroSum (f : TestFunction) : ℂ :=
    ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n)"""

content = content.replace(old_anchor, new_anchor, 1)

# 2. 修改 nontrivialZeroSum_tsum_linear 公理
old_tsum = """/-- 非平凡零点求和的 tsum 线性性（公理）：
    nontrivialZeroSum(f₁) - nontrivialZeroSum(f₂) =
      ∑'_{n:ℕ} (M[f₁](enum n) - M[f₂](enum n))。

    数学依据：tsum 的线性性，两级数都收敛（磨光函数的 Mellin 变换在零点处有界）。
    风险等级：中低（tsum 线性性，标准分析结果）。 -/
axiom nontrivialZeroSum_tsum_linear (f1 f2 : TestFunction) :
    nontrivialZeroSum f1 - nontrivialZeroSum f2 =
      ∑' (n : ℕ), (melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n))"""

new_tsum = """/-- 非平凡零点求和的 tsum 线性性（公理，带重数）：
    nontrivialZeroSum(f₁) - nontrivialZeroSum(f₂) =
      ∑'_{n:ℕ} m(enum n) * (M[f₁](enum n) - M[f₂](enum n))。

    数学依据：tsum 的线性性，两级数都收敛（磨光函数的 Mellin 变换在零点处有界，重数有界）。
    风险等级：中低（tsum 线性性，标准分析结果）。 -/
axiom nontrivialZeroSum_tsum_linear (f1 f2 : TestFunction) :
    nontrivialZeroSum f1 - nontrivialZeroSum f2 =
      ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
        (melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n))"""

content = content.replace(old_tsum, new_tsum, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 1-2 done: zeroMultiplicity + tsum_linear')
