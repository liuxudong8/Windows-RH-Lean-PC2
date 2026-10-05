# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修正证明
old_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  -- 用线性性拆成两个 Mellin 变换的和
  have h1 : melinTransform (differentialOperatorTestFunction f + t • f) s =
      melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s := by
    exact melinTransform_linear (differentialOperatorTestFunction f) f 1 t s
  rw [h1]
  -- 用微分算子的公式
  have h2 : melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h2]
  <;> ring'''

new_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  -- 用线性性拆成两个 Mellin 变换的和
  have h_eq1 : (differentialOperatorTestFunction f + t • f) = (1 : ℂ) • differentialOperatorTestFunction f + t • f := by
    simp
  rw [h_eq1]
  have h1 := melinTransform_linear (differentialOperatorTestFunction f) f (1 : ℂ) t s
  rw [h1]
  <;> simp
  -- 用微分算子的公式
  have h2 : melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h2]
  <;> ring'''

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
