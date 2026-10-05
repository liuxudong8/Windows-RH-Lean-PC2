# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修复 Line 4836 附近的错误
old = """      have h_abs_eq : |(nontrivialZeroEnum n).im|^2 = (nontrivialZeroEnum n).im^2 := by
        simp [sq_abs]
      have h_goal : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ * 1 ≤ C * w n := by
        dsimp only [w]
        have h1 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / |(nontrivialZeroEnum n).im| ^ 2) := by gcongr
        rw [h_abs_eq] at h1
        have h2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / (nontrivialZeroEnum n).im ^ 2) = C * w n := by
          simp [w] <;> rw [h_abs_eq] <;> ring
        rw [h2] at h1
        simpa [mul_one] using h1"""

new = """      have h_abs_eq : |(nontrivialZeroEnum n).im|^2 = (nontrivialZeroEnum n).im^2 := by
        simp [sq_abs]
      have h_goal : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ * 1 ≤ C * w n := by
        dsimp only [w]
        have h1 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / |(nontrivialZeroEnum n).im| ^ 2) := by gcongr
        have h1' : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / (nontrivialZeroEnum n).im ^ 2) := by
          convert h1 using 1
          rw [h_abs_eq]
        have h2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / (nontrivialZeroEnum n).im ^ 2) = C * w n := by
          simp [w, h_abs_eq] <;> ring
        rw [h2] at h1'
        simpa [mul_one] using h1'"""

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
