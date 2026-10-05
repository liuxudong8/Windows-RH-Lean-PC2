import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# At both call sites, nontrivialZeroEnum n is a nontrivial zero, so im ≠ 0
c = c.replace(
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2\n      have h_if",
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 (nontrivialZeroEnum_are_zeros n).1.ne\n      have h_if"
)
c = c.replace(
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2\n    have h_goal",
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 (nontrivialZeroEnum_are_zeros n).1.ne\n    have h_goal"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
