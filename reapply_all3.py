import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "  exact mellin_rapid_decay_bound h B' hC2 hB hB_pos ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_h_left h_h_right h_u_eps0_zero h_u_R0_zero h_u'_eps0_zero h_u'_R0_zero s hs_re1 hs_re2 hs_im_ne_zero",
    "  intro s hs_re1 hs_re2 hs_im_ne_zero\n  exact mellin_rapid_decay_bound h B' hC2 hB hB_pos ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_h_left h_h_right h_u_eps0_zero h_u_R0_zero h_u'_eps0_zero h_u'_R0_zero s hs_re1 hs_re2 hs_im_ne_zero"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
