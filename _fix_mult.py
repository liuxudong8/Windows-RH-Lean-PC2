from pathlib import Path

p = Path(r"c:\proj2\OrderPreservingBijection\ZetaZeros.lean")
t = p.read_text(encoding="utf-8")

# Find and replace from "theorem zeroMultiplicity_positive" to the symmetry sorry
import re
# Find the block starting at the positive theorem
start = t.index("theorem zeroMultiplicity_positive_at_nontrivial_zeros")
# Find the end: the line after "sorry" of symmetry
end_marker = "    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by\n  sorry"
end = t.index(end_marker) + len(end_marker)

new_block = """theorem zeroMultiplicity_positive_at_nontrivial_zeros (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < zeroMultiplicity ρ := by
  intro hz hre1 hre2
  have hne1 : ρ ≠ 1 := by
    intro h; rw [h] at hre2; norm_num at hre2
  have h_analytic : AnalyticAt ℂ _root_.riemannZeta ρ :=
    _root_.analyticOn_riemannZeta ρ hne1
  have h_order_ne_zero : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ 0 :=
    h_analytic.analyticOrderAt_ne_zero.mpr hz
  have h_order_ne_top : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ ⊤ := by sorry
  have h_goal : zeroMultiplicity ρ ≠ 0 := by
    have h_eq : (zeroMultiplicity ρ : ℕ∞) = _root_.analyticOrderAt _root_.riemannZeta ρ := by
      simpa [zeroMultiplicity, _root_.analyticOrderNatAt] using Nat.cast_analyticOrderNatAt h_order_ne_top
    intro h
    apply h_order_ne_zero
    rw [← h_eq, h] <;> norm_num
  exact_pos h_goal

/-- 零点重数的函数方程对称性（定理，桥接中）：
    ζ(1-s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)。prefactor 在 0<Re(s)<1 内非零解析，
    故 order(ζ, 1-ρ) = order(ζ, ρ)。 -/
theorem zeroMultiplicity_symmetry (ρ : ℂ) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by
  sorry"""

t = t[:start] + new_block + t[end:]
p.write_text(t, encoding="utf-8")
print("done")
