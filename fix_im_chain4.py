import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

c = c.replace(
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 →\n          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2) := by",
    "        (∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2) := by"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
