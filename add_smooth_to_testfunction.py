# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修改 TestFunction 的结构定义
old_struct = '''/-- 紧支集测试函数：f : ℝ → ℂ，存在 R>0 使得 |x|>R 时 f(x)=0。 -/
structure TestFunction where
  toFun : ℝ → ℂ
  hasCompactSupport : ∃ (R : ℝ), 0 < R ∧ ∀ (x : ℝ), |x| > R → toFun x = 0
  isBounded : ∃ (B : ℝ), 0 < B ∧ ∀ (x : ℝ), ‖toFun x‖ ≤ B
  vanishesNearZero : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : ℝ), x < ε → toFun x = 0
  measurable : Measurable toFun'''

new_struct = '''/-- 紧支集测试函数：f : ℝ → ℂ，存在 R>0 使得 |x|>R 时 f(x)=0。 -/
structure TestFunction where
  toFun : ℝ → ℂ
  hasCompactSupport : ∃ (R : ℝ), 0 < R ∧ ∀ (x : ℝ), |x| > R → toFun x = 0
  isBounded : ∃ (B : ℝ), 0 < B ∧ ∀ (x : ℝ), ‖toFun x‖ ≤ B
  vanishesNearZero : ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : ℝ), x < ε → toFun x = 0
  measurable : Measurable toFun
  smooth : ContDiff ℝ ⊤ toFun'''

content = content.replace(old_struct, new_struct)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
