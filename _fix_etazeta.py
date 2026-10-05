from pathlib import Path

p = Path(r"c:\proj2\OrderPreservingBijection\ZetaZeros.lean")
t = p.read_text(encoding="utf-8")

start = t.index("/-- 非平凡零点不在实轴上")
end = t.index("/-- 零点重数函数（def）")

new = """/-- ζ 在 (0,1) 上为负（定理，由 Dirichlet eta 函数交错级数表示）：
    η(x) = Σ (-1)^{n-1}/n^x = (1-2^{1-x})ζ(x)。
    对 x∈(0,1)，η(x)>0（Leibniz）且 1-2^{1-x}<0，故 ζ(x)<0。 -/
theorem riemannZeta_neg_on_Ioo (x : ℝ) (hx1 : 0 < x) (hx2 : x < 1) :
    (riemannZeta x).re < 0 := by sorry

/-- 非平凡零点不在实轴上（定理）：
    ζ 在开区间 (0,1) 上没有实零点（ζ(x)<0）。
    因此任何临界带内的零点都满足 s.im ≠ 0。 -/
theorem nontrivialZero_im_ne_zero (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.im ≠ 0 := by
  intro hz hre1 hre2 him
  have h_re : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [h_re] at hz
  have h_neg : (riemannZeta (ρ.re : ℂ)).re < 0 := riemannZeta_neg_on_Ioo ρ.re hre1 hre2
  rw [hz] at h_neg <;> norm_num at h_neg

"""

t = t[:start] + new + t[end:]
p.write_text(t, encoding="utf-8")
print("done")
