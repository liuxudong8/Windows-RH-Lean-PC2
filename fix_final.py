# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 Line 4840 附近的错误
old = """        rw [h2] at h1'
        simpa [mul_one] using h1'"""

new = """        rw [h2] at h1'
        have h_final : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ * 1 ≤ C * w n := by
          simpa [w, h_abs_eq, mul_one] using h1'
        exact h_final"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
