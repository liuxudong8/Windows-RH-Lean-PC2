path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Fix 1: h_E0 contradiction
content = content.replace(
    "        have h_f0_0 : f0.eval l0 = 0 := hR l0 hx\n        have h_E0' : E0 = 0 := by\n          simp [ellipticTerm, h_f0_0] at h_E0 \u22a2 <;> tauto\n        contradiction",
    "        have h_f0_0 : f0.eval l0 = 0 := hR l0 hx\n        have h_E0_eq : ellipticTerm f0 = 0 := by\n          simp [ellipticTerm, h_f0_0]\n        have h_contra : E0 = 0 := h_E0_eq\n        exact False.elim (h_E0 h_contra)"
)

# Fix 2: h_compact - use refine instead of constructor
content = content.replace(
    "  have h_compact : \u2203 (R' : \u211d), 0 < R' \u2227 \u2200 (x : \u211d), |x| > R' \u2192 f0_fun x = 0 := by\n    use R; constructor\n    \u00b7 have h1 : 0 < \u039b1 := by linarith; exact lt_max_of_lt_left h1\n    \u00b7 intro x hx",
    "  have h_compact : \u2203 (R' : \u211d), 0 < R' \u2227 \u2200 (x : \u211d), |x| > R' \u2192 f0_fun x = 0 := by\n    refine \u27e8R, ?_, ?_\u27e9\n    \u00b7 have h1 : 0 < \u039b1 := by linarith; exact lt_max_of_lt_left h1\n    \u00b7 intro x hx"
)

# Fix 3: h_sum type mismatch
content = content.replace(
    "      have h_main : ellipticTerm f = ellipticTerm f0 + ellipticWeight l0 * (f.eval l0 - f0.eval l0) := by\n        simpa [ellipticTerm, g, g0] using h_sum",
    "      have h_main1 : \u2211 x \u2208 ellipticClassLengths_finite.toFinset, ellipticWeight x * f.eval x =\n          (\u2211 x \u2208 ellipticClassLengths_finite.toFinset, ellipticWeight x * f0.eval x) +\n          (ellipticWeight l0 * f.eval l0 - ellipticWeight l0 * f0.eval l0) := by\n        simpa [g, g0] using h_sum\n      have h_main2 : (ellipticWeight l0 * f.eval l0 - ellipticWeight l0 * f0.eval l0) =\n          ellipticWeight l0 * (f.eval l0 - f0.eval l0) := by ring\n      have h_main : ellipticTerm f = ellipticTerm f0 + ellipticWeight l0 * (f.eval l0 - f0.eval l0) := by\n        simp [ellipticTerm, h_main1, h_main2] <;> ring"
)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed 3 errors')
