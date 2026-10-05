import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "  intro s hs_re1 hs_re2\n  have h_decay",
    "  intro s hs_re1 hs_re2 hs_im_ne_zero\n  have h_decay"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
