import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "  have h_decay : ∀ (s : ℂ), 0 < s.re → s.re < 1 →\n      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2 := by\n    intro s hs_re1 hs_re2",
    "  have h_decay : ∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2 := by\n    intro s hs_re1 hs_re2 hs_im_ne_zero"
)
c = c.replace(
    "      have h11 := h_decay1 s hs_re1 hs_re2",
    "      have h11 := h_decay1 s hs_re1 hs_re2 hs_im_ne_zero"
)
c = c.replace(
    "      have h22 := h_decay2 s hs_re1 hs_re2",
    "      have h22 := h_decay2 s hs_re1 hs_re2 hs_im_ne_zero"
)

# Also fix the outer theorem conclusion
c = c.replace(
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 →\n          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2) := by",
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2) := by"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
