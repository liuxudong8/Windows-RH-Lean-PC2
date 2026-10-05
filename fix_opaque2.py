f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 非平凡零点的枚举（opaque）：
    nontrivialZeroEnum : ℕ → ℂ 枚举所有临界带内的非平凡零点。
    由 Weyl 定律，非平凡零点可数，因此存在这样的枚举。 -/
opaque nontrivialZeroEnum : ℕ → ℂ

/-- 非平凡零点枚举的覆盖性（公理）：
    对任意非平凡零点 ρ（ζ(ρ)=0 且 0<Re(ρ)<1），存在 n 使得 nontrivialZeroEnum n = ρ。
    风险等级：第一档（Weyl 定律的直接推论，非平凡零点可数）。 -/
axiom nontrivialZeroEnum_covers_all (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    ∃ (n : ℕ), nontrivialZeroEnum n = ρ

/-- 非平凡零点枚举的单射性（公理）：
    nontrivialZeroEnum 是单射，每个非平凡零点恰好出现一次。
    风险等级：第一档（可数集可以无重复枚举）。 -/
axiom nontrivialZeroEnum_injective : Function.Injective nontrivialZeroEnum

/-- 枚举元素都是非平凡零点（公理）：
    对任意 n，nontrivialZeroEnum n 是非平凡零点（ζ=0 且 0<Re<1）。
    风险等级：第一档（枚举的定义性质）。 -/
axiom nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1"""

new = """/-- 非平凡零点枚举的存在性（公理，第一档）：
    存在单射 e : ℕ → ℂ，枚举所有临界带内的非平凡零点。
    由 Weyl 定律，非平凡零点可数，因此存在这样的无重复枚举。
    风险等级：第一档（Weyl 定律 + 可数集枚举定理）。 -/
axiom nontrivialZeroEnum_exists :
    ∃ (e : ℕ → ℂ),
      (Function.Injective e) ∧
      (∀ (n : ℕ), _root_.riemannZeta (e n) = 0 ∧ 0 < (e n).re ∧ (e n).re < 1) ∧
      (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), e n = ρ)

/-- 非平凡零点的枚举（定义，由存在性公理通过 Classical.choose 给出）：
    nontrivialZeroEnum : ℕ → ℂ 枚举所有临界带内的非平凡零点。 -/
noncomputable def nontrivialZeroEnum : ℕ → ℂ :=
    Classical.choose nontrivialZeroEnum_exists

/-- 非平凡零点枚举的性质（定理，由 Classical.choose_spec 推出）。 -/
theorem nontrivialZeroEnum_spec :
    (Function.Injective nontrivialZeroEnum) ∧
    (∀ (n : ℕ), _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧ 0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1) ∧
    (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ (n : ℕ), nontrivialZeroEnum n = ρ) :=
    Classical.choose_spec nontrivialZeroEnum_exists

/-- 非平凡零点枚举的覆盖性（定理）。 -/
theorem nontrivialZeroEnum_covers_all (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    ∃ (n : ℕ), nontrivialZeroEnum n = ρ :=
    nontrivialZeroEnum_spec.2.2 ρ

/-- 非平凡零点枚举的单射性（定理）。 -/
theorem nontrivialZeroEnum_injective : Function.Injective nontrivialZeroEnum :=
    nontrivialZeroEnum_spec.1

/-- 枚举元素都是非平凡零点（定理）。 -/
theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: nontrivialZeroEnum -> def, 3 axioms -> theorems')
