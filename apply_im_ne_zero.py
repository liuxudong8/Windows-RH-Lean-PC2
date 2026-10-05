import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# 1. mellin_integral_bound_uniform: add s.im ≠ 0 to statement and intro
old1 = "(∀ (s : ℂ), 0 < s.re → s.re < 1 →\n        ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)) := by\n  intro h M h_bound h_left h_right s hs_re1 hs_re2"
new1 = "(∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n        ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)) := by\n  intro h M h_bound h_left h_right s hs_re1 hs_re2 hs_im_ne_zero"
assert old1 in c, "old1 not found"
c = c.replace(old1, new1)

# 2. mellin_pointwise_dual_norm_bound: add parameter
old2 = "theorem mellin_pointwise_dual_norm_bound (s : ℂ) (hs_re1 : 0 < s.re) (hs_re2 : s.re < 1) :"
new2 = "theorem mellin_pointwise_dual_norm_bound (s : ℂ) (hs_re1 : 0 < s.re) (hs_re2 : s.re < 1) (hs_im_ne_zero : s.im ≠ 0) :"
assert old2 in c, "old2 not found"
c = c.replace(old2, new2)

# 3. Call site 1: add hs_im_ne_zero
old3 = "h_support_h.1 h_support_h.2 s hs_re1 hs_re2\n"
# Need to be careful - there are two call sites. Let's count.
count = c.count(old3)
print(f"found {count} call sites")
# Both need the same change
new3 = "h_support_h.1 h_support_h.2 s hs_re1 hs_re2 hs_im_ne_zero\n"
c = c.replace(old3, new3)

# 4. intro s hs_in hs_re1 hs_re2 -> add hs_im_ne_zero
old4 = "intro s hs_in hs_re1 hs_re2"
new4 = "intro s hs_in hs_re1 hs_re2 hs_im_ne_zero"
assert old4 in c, "old4 not found"
c = c.replace(old4, new4)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
