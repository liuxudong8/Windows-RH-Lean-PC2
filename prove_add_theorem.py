# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到 melinTransform_differentialOperator_add 的证明，把 sorry 换成真正的证明
old_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  sorry'''

new_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
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

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
