from pathlib import Path

p = Path(r"c:\proj2\OrderPreservingBijection\ZetaZeros.lean")
t = p.read_text(encoding="utf-8")

old = """theorem zeroMultiplicity_symmetry (ρ : ℂ)
    (_ : _root_.riemannZeta ρ = 0) (hre1 : 0 < ρ.re) (hre2 : ρ.re < 1) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by sorry"""

new = """theorem zeroMultiplicity_symmetry (ρ : ℂ)
    (_ : _root_.riemannZeta ρ = 0) (hre1 : 0 < ρ.re) (hre2 : ρ.re < 1) :
    zeroMultiplicity ρ = zeroMultiplicity (1 - ρ) := by
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at hre2; norm_num at hre2
  have hne_nat : ∀ m : ℕ, ρ ≠ -m := by
    intro m h; have : (ρ : ℂ).re ≤ 0 := by rw [h]; simp; rw [this] at hre1; linarith
  let c : ℂ → ℂ := fun s => 2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)
  have h_func : ∀ s, _root_.riemannZeta (1 - s) = c s * _root_.riemannZeta s := by
    intro s; simpa [c] using _root_.riemannZeta_one_sub (fun m => by simpa using hne_nat m) (by simpa using hne1)
  have hG_ne_zero : Complex.Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1
  have hcos_ne_zero : Complex.cos (Real.pi * ρ / 2) ≠ 0 := by
    rw [Complex.cos_eq_zero_iff]; rintro ⟨k, hk⟩
    have h_eq : ρ = (2 * (k : ℂ) + 1) := by
      apply mul_left_cancel₀ (by positivity : (Real.pi : ℂ) / 2 ≠ 0); rw [hk] <;> ring
    have h_re : ρ.re = ((2 * (k : ℂ) + 1) : ℝ) := by rw [h_eq]; simp
    rw [h_re] at hre1 hre2; norm_num at hre1 hre2 <;> linarith
  have hc_ne_zero : c ρ ≠ 0 := by
    simp only [c, mul_ne_zero_iff]; exact ⟨by positivity |>.imp hG_ne_zero, hcos_ne_zero⟩
  have hc_analytic : AnalyticAt ℂ c ρ := by
    fun_prop
  have hζ_analytic : AnalyticAt ℂ _root_.riemannZeta ρ := _root_.analyticOn_riemannZeta ρ hne1
  have h_order_c : _root_.analyticOrderAt c ρ = 0 :=
    hc_analytic.analyticOrderAt_eq_zero.mpr hc_ne_zero
  have h_eq1 : (fun s : ℂ => _root_.riemannZeta (1 - s)) = fun s => c s * _root_.riemannZeta s := by
    funext s; exact h_func s
  have h_order1 : _root_.analyticOrderAt (fun s : ℂ => _root_.riemannZeta (1 - s)) ρ =
      _root_.analyticOrderAt _root_.riemannZeta ρ := by
    rw [h_eq1]
    have h := _root_.analyticOrderAt_mul hc_analytic hζ_analytic
    rw [h, h_order_c, zero_add]
  have h_comp : _root_.analyticOrderAt (fun s : ℂ => _root_.riemannZeta (1 - s)) ρ =
      _root_.analyticOrderAt _root_.riemannZeta (1 - ρ) := by
    exact _root_.analyticOrderAt_comp_of_deriv_ne_zero
      (g := fun s => (1:ℂ) - s) (by fun_prop) (by simp [deriv_id]; norm_num)
  have h_final : _root_.analyticOrderAt _root_.riemannZeta (1 - ρ) = _root_.analyticOrderAt _root_.riemannZeta ρ :=
    h_comp.symm.trans h_order1
  have h_top1 : _root_.analyticOrderAt _root_.riemannZeta ρ ≠ ⊤ := by sorry
  have h_top2 : _root_.analyticOrderAt _root_.riemannZeta (1 - ρ) ≠ ⊤ := by sorry
  have h_nat : (zeroMultiplicity (1 - ρ)) = zeroMultiplicity ρ := by
    simp only [zeroMultiplicity]
    congr 1
    · exact h_final.symm
    · exact h_final
  exact h_nat.symm"""

assert old in t
t = t.replace(old, new, 1)
p.write_text(t, encoding="utf-8")
print("done")
