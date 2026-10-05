import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2\n      have h_if",
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 (by admit : (nontrivialZeroEnum n).im ≠ 0)\n      have h_if"
)
c = c.replace(
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2\n    have h_goal",
    "h_decay (nontrivialZeroEnum n) h_re1 h_re2 (by admit : (nontrivialZeroEnum n).im ≠ 0)\n    have h_goal"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
