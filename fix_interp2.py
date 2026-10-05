path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Fix 1: ellipticVanishes in E0=0 case
content = content.replace(
    "    let mf : MollifiedTestFunction :=\n      { toTestFunction := f0\n        supportSeparated := h_support\n        ellipticVanishes := by simpa [ellipticTerm] using h_E0 }",
    "    have h_ev : ellipticTerm f0 = 0 := by\n      have h_eq : E0 = ellipticTerm f0 := rfl\n      rw [h_eq] at h_E0; exact h_E0\n    let mf : MollifiedTestFunction :=\n      { toTestFunction := f0\n        supportSeparated := h_support\n        ellipticVanishes := h_ev }"
)

# Fix 2: h_compact in E0≠0 case - choose R >= |l0|
content = content.replace(
    "    have h_compact : \u2203 (R : \u211d), 0 < R \u2227 \u2200 (x : \u211d), |x| > R \u2192 f_fun x = 0 := by\n      rcases f0.hasCompactSupport with \u27e8R, hR_pos, hR\u27e9\n      refine \u27e8R, hR_pos, ?_\u27e9\n      intro x hx\n      by_cases hx_eq : x = l0\n      \u00b7 rw [hx_eq] at hx\n        have h_f0_0 : f0.eval l0 = 0 := hR l0 hx\n        have h_E0_eq : ellipticTerm f0 = 0 := by\n          simp [ellipticTerm, h_f0_0]\n        have h_contra : E0 = 0 := h_E0_eq\n        exact False.elim (h_E0 h_contra)\n      \u00b7 simp only [f_fun, if_neg hx_eq]; exact hR x hx",
    "    have h_compact : \u2203 (R : \u211d), 0 < R \u2227 \u2200 (x : \u211d), |x| > R \u2192 f_fun x = 0 := by\n      rcases f0.hasCompactSupport with \u27e8R0, hR0_pos, hR0\u27e9\n      let R : \u211d := max R0 (|l0| + 1)\n      have hR_pos : 0 < R := by\n        have h1 : 0 < R0 := hR0_pos\n        have h2 : R0 \u2264 R := le_max_left R0 (|l0| + 1)\n        linarith\n      refine \u27e8R, hR_pos, ?_\u27e9\n      intro x hx\n      have h_x_ne_l0 : x \u2260 l0 := by\n        intro h_eq\n        rw [h_eq] at hx\n        have h3 : |l0| \u2264 R := by\n          have h4 : |l0| + 1 \u2264 R := le_max_right R0 (|l0| + 1)\n          linarith\n        linarith\n      simp only [f_fun, if_neg h_x_ne_l0]\n      have h_x_gt_R0 : |x| > R0 := by\n        have h5 : R0 \u2264 R := le_max_left R0 (|l0| + 1)\n        linarith\n      exact hR0 x h_x_gt_R0"
)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed h_compact and ellipticVanishes')
