f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. jlLParameterMap 需要 noncomputable
content = content.replace(
    'def jlLParameterMap (n : ℕ) : ℂ :=',
    'noncomputable def jlLParameterMap (n : ℕ) : ℂ :=',
    1
)

# 2. 删除重复的 maassSpecParam_nonneg 公理
old_maass = '''/-- Maass 谱参数非负（公理）：0 ≤ maassSpecParam(k)。
    这是 Maass 形式的标准性质：谱参数 t_k 取非负实数值。 -/
axiom maassSpecParam_nonneg :
    ∀ (k : ℕ), 0 ≤ maassSpecParam k

'''
content = content.replace(old_maass, '', 1)

# 3. 删除重复的 l_parameter_eigenvalue_formula 公理（用更简单的匹配）
lines = content.split('\n')
new_lines = []
skip = False
for i, line in enumerate(lines):
    if 'axiom l_parameter_eigenvalue_formula :' in line:
        # 跳过这一行和下一行（∀ ...）
        skip = True
        continue
    if skip:
        skip = False
        continue
    new_lines.append(line)
content = '\n'.join(new_lines)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed duplicates and noncomputable')
