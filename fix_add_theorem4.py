# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修正证明
old_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  -- 用线性性拆成两个 Mellin 变换的和
  have h1 := melinTransform_linear (differentialOperatorTestFunction f) f (1 : ℂ) t s
  -- 我们需要的是 melinTransform (differentialOperatorTestFunction f + t • f) s
  -- 而 h1 是 melinTransform (1 • differentialOperatorTestFunction f + t • f) s
  -- 我们需要证明 1 • differentialOperatorTestFunction f = differentialOperatorTestFunction f
  have h_one_smul : (1 : ℂ) • differentialOperatorTestFunction f = differentialOperatorTestFunction f := by
    apply TestFunction.toFun_injective
    funext x
    rfl
  rw [←h_one_smul] at *
  rw [h1]
  have h2 : (1 : ℂ) * melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s =
      melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s := by
    ring
  rw [h2]
  -- 用微分算子的公式
  have h3 : melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h3]
  <;> ring'''

new_proof = '''theorem melinTransform_differentialOperator_add (f : TestFunction) (t : ℂ) (s : ℂ) :
    melinTransform (differentialOperatorTestFunction f + t • f) s = -(s - t) * melinTransform f s := by
  -- 用线性性拆成两个 Mellin 变换的和
  have h1 := melinTransform_linear (differentialOperatorTestFunction f) f (1 : ℂ) t s
  -- 我们需要证明 1 • differentialOperatorTestFunction f = differentialOperatorTestFunction f
  have h_one_smul : (1 : ℂ) • differentialOperatorTestFunction f = differentialOperatorTestFunction f := by
    apply TestFunction.toFun_injective
    funext x
    simp [SMul.smul]
    <;> ring
  -- 现在，我们有 h1 : melinTransform (1 • f1 + t • f2) s = 1 * Mf1 + t * Mf2
  -- 我们需要的是 melinTransform (f1 + t • f2) s = ...
  -- 我们可以把 h1 里的 1 • f1 替换成 f1
  have h_main : melinTransform ((1 : ℂ) • differentialOperatorTestFunction f + t • f) s =
      melinTransform (differentialOperatorTestFunction f + t • f) s := by
    rw [h_one_smul]
  rw [←h_main]
  rw [h1]
  have h2 : (1 : ℂ) * melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s =
      melinTransform (differentialOperatorTestFunction f) s + t * melinTransform f s := by
    ring
  rw [h2]
  -- 用微分算子的公式
  have h3 : melinTransform (differentialOperatorTestFunction f) s = -s * melinTransform f s :=
    melinTransform_differentialOperator f s
  rw [h3]
  <;> ring'''

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
