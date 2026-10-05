import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 nontrivialZeroEnum_im_ne_zero\n",
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 (nontrivialZeroEnum_im_ne_zero n)\n"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
