# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 给 zeroTestFunction 补上 smooth 字段
old_zero = '''/-- TestFunction 零元素。 -/
noncomputable def zeroTestFunction : TestFunction :=
  { toFun := fun _ => (0 : ℂ)
    hasCompactSupport := by
      refine ⟨1, by norm_num, ?_⟩
      intro x _; rfl
    isBounded := ⟨1, by norm_num, fun x => by simp⟩
    vanishesNearZero := ⟨1, by norm_num, fun x _ => rfl⟩
    measurable := measurable_const }'''

new_zero = '''/-- TestFunction 零元素。 -/
noncomputable def zeroTestFunction : TestFunction :=
  { toFun := fun _ => (0 : ℂ)
    hasCompactSupport := by
      refine ⟨1, by norm_num, ?_⟩
      intro x _; rfl
    isBounded := ⟨1, by norm_num, fun x => by simp⟩
    vanishesNearZero := ⟨1, by norm_num, fun x _ => rfl⟩
    measurable := measurable_const
    smooth := by sorry }'''

content = content.replace(old_zero, new_zero)

# 2. 给 addTestFunction 补上 smooth 字段
old_add = '''/-- TestFunction 加法。 -/
noncomputable def addTestFunction (f1 f2 : TestFunction) : TestFunction :=
  { toFun := fun x => f1.eval x + f2.eval x'''

new_add = '''/-- TestFunction 加法。 -/
noncomputable def addTestFunction (f1 f2 : TestFunction) : TestFunction :=
  { toFun := fun x => f1.eval x + f2.eval x'''

# 我们需要找到 addTestFunction 的定义，然后在最后加上 smooth 字段
# 先找到 addTestFunction 的结束位置
add_start = content.find(old_add)
if add_start != -1:
    # 找到 addTestFunction 的 measurable 字段，然后在它后面加上 smooth 字段
    add_measurable = content.find('measurable :=', add_start)
    if add_measurable != -1:
        # 找到这一行的结束
        add_line_end = content.find('\n', add_measurable)
        # 在这一行后面加上 smooth 字段
        new_add_line = content[add_measurable:add_line_end] + '\n    smooth := by sorry'
        content = content[:add_measurable] + new_add_line + content[add_line_end:]

# 3. 给 smulTestFunction 补上 smooth 字段
# 我们先找到 smulTestFunction 的定义
old_smul = 'noncomputable instance : SMul ℂ TestFunction where'
smul_start = content.find(old_smul)
if smul_start != -1:
    # 找到 smulTestFunction 的 measurable 字段，然后在它后面加上 smooth 字段
    smul_measurable = content.find('measurable :=', smul_start)
    if smul_measurable != -1:
        # 找到这一行的结束
        smul_line_end = content.find('\n', smul_measurable)
        # 在这一行后面加上 smooth 字段
        new_smul_line = content[smul_measurable:smul_line_end] + '\n    smooth := by sorry'
        content = content[:smul_measurable] + new_smul_line + content[smul_line_end:]

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
