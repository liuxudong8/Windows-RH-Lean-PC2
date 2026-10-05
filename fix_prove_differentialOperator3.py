# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修正证明
old_proof = '''    have h21 : Real.exp (Real.log x) = x := Real.exp_log hx
    have h2 : (x : ℂ) = Complex.exp ((Real.log x : ℂ)) := by
      exact_mod_cast h21'''

new_proof = '''    have h21 : Real.exp (Real.log x) = x := Real.exp_log hx
    have h22 : x = Real.exp (Real.log x) := Eq.symm h21
    have h2 : (x : ℂ) = Complex.exp ((Real.log x : ℂ)) := by
      exact_mod_cast h22'''

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\MellinInfrastructure.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
