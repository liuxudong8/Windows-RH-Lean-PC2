import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# 1. mellin_rapid_decay_bound statement
c = c.replace(
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by\n  intro s hs_re1 hs_re2",
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by\n  intro s hs_re1 hs_re2 hs_im_ne_zero"
)

# 2. h_s_im_ne_zero admit -> exact assumption
c = c.replace(
    "    have h_s_im_ne_zero : s.im ≠ 0 := by\n      admit",
    "    have h_s_im_ne_zero : s.im ≠ 0 := hs_im_ne_zero"
)

# 3. mellin_transform_C2_rapid_decay statement
c = c.replace(
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by",
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by"
)

# 4. Call site 4806: mellin_rapid_decay_bound needs s.im≠0
# It's called inside mellin_transform_C2_rapid_decay, which now takes s.im≠0
# The call at 4806 doesn't see s directly - let's check context
# Actually 4806 is the body of mellin_transform_C2_rapid_decay, which has s in scope
# Need to add the argument

# 5. mellin_rapid_decay_choice statement (4820)
c = c.replace(
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 →\n          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / |s.im| ^ 2) := by",
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / |s.im| ^ 2) := by"
)

# 6. Call site 4839: pass hs_im_ne_zero
c = c.replace(
    "    mellin_transform_C2_rapid_decay h (B * max ‖wρ‖ 1) hC2 h_deriv_bound (by positivity) s hs_re1 hs_re2",
    "    mellin_transform_C2_rapid_decay h (B * max ‖wρ‖ 1) hC2 h_deriv_bound (by positivity) s hs_re1 hs_re2 hs_im_ne_zero"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
