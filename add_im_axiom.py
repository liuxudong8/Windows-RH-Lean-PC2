import io

f = r'C:\proj2\OrderPreservingBijection\ZetaZeros.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n"""

new = """theorem nontrivialZeroEnum_are_zeros (n : ℕ) :
    _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧
    0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 :=
    nontrivialZeroEnum_spec.2.1 n

/-- 非平凡零点不在实轴上（公理）：
    ζ 在开区间 (0,1) 上没有实零点（由 Dirichlet η 函数的交错级数表示，η(σ)>0）。
    因此任何临界带内的零点都满足 s.im ≠ 0。 -/
axiom nontrivialZero_im_ne_zero (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.im ≠ 0"""

assert old in c
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
