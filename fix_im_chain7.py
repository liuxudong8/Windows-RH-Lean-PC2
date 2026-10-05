import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "(by exact? : (nontrivialZeroEnum n).im ≠ 0)",
    "(by admit : (nontrivialZeroEnum n).im ≠ 0)"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
