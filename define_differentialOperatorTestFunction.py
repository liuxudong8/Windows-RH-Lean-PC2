# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 替换 differentialOperatorTestFunction 的定义
old_def = '''/-- 微分算子作用在 TestFunction 上（假设 f 是 C^∞ 的）：
    如果 f 是 C^∞ 的紧支函数，那 D f 也是 TestFunction。 -/
noncomputable def differentialOperatorTestFunction (f : TestFunction) : TestFunction := by
  sorry'''

new_def = '''/-- 微分算子作用在 TestFunction 上（假设 f 是 C^∞ 的）：
    如果 f 是 C^∞ 的紧支函数，那 D f 也是 TestFunction。 -/
noncomputable def differentialOperatorTestFunction (f : TestFunction) : TestFunction :=
  { toFun := fun x : ℝ => x * deriv f.eval x
    hasCompactSupport := by sorry
    isBounded := by sorry
    vanishesNearZero := by sorry
    measurable := by sorry }'''

content = content.replace(old_def, new_def)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
