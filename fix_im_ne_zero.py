# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 h_im_ne_zero 的证明
old = """      have h_im_ne_zero : (nontrivialZeroEnum n).im ≠ 0 := by
        exact nontrivialZeroEnum_im_ne_zero n"""

new = """      have h_im_ne_zero : (nontrivialZeroEnum n).im ≠ 0 := by
        have h1 : 0 < |(nontrivialZeroEnum n).im| := by
          have h2 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := h_im1
          have h3 : (0 : ℝ) < (2^k : ℝ) := by positivity
          linarith
        exact abs_pos.mp h1"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
