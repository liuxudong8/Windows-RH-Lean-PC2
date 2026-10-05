# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修正证明
old_proof = '''  have h_one_smul : (1 : ℂ) • differentialOperatorTestFunction f = differentialOperatorTestFunction f := by
    apply TestFunction.toFun_injective
    funext x
    simp [SMul.smul]
    <;> ring'''

new_proof = '''  have h_one_smul : (1 : ℂ) • differentialOperatorTestFunction f = differentialOperatorTestFunction f := by
    apply TestFunction.toFun_injective
    funext x
    change (1 : ℂ) * (differentialOperatorTestFunction f).eval x = (differentialOperatorTestFunction f).eval x
    <;> ring'''

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
