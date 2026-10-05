f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. jlLParameterMap -> def
old_lparam = '''/-- JL L-参数映射（opaque）：
    ψ: ℕ → ℂ 将三维谱指标 n 映射到对应自守表示的 L-参数。 -/
opaque jlLParameterMap : ℕ → ℂ'''
new_lparam = '''/-- JL L-参数映射（def，由 JL 对应直接给出）：
    jlLParameterMap(n) = 1/2 + i*maassSpecParam(jlSpectrumMap(n))。
    三维表示 pi_n 的 L-参数等于对应 Maass 表示的 L-参数。 -/
def jlLParameterMap (n : ℕ) : ℂ :=
    (1 / 2 : ℂ) + Complex.I * (maassSpecParam (jlSpectrumMap n) : ℂ)'''
content = content.replace(old_lparam, new_lparam, 1)

# 2. 删除 l_parameter_standard_form 公理
old_std = '''/-- L-参数标准形式（公理）：jlLParameterMap(n).re = 1/2。 -/
axiom l_parameter_standard_form :
    ∀ (n : ℕ), (jlLParameterMap n).re = 1 / 2

'''
content = content.replace(old_std, '', 1)

# 3. l_parameter_im_nonneg -> maassSpecParam_nonneg
old_im = '''/-- L-参数虚部非负（公理）：0 ≤ jlLParameterMap(n).im。 -/
axiom l_parameter_im_nonneg :
    ∀ (n : ℕ), 0 ≤ (jlLParameterMap n).im'''
new_im = '''/-- Maass 谱参数非负（公理）：0 ≤ maassSpecParam(k)。
    这是 Maass 形式的标准性质：谱参数 t_k 取非负实数值。 -/
axiom maassSpecParam_nonneg :
    ∀ (k : ℕ), 0 ≤ maassSpecParam k'''
content = content.replace(old_im, new_im, 1)

# 4. l_parameter_eigenvalue_formula -> 用 maassSpecParam 表达
old_eig = '''axiom l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (jlLParameterMap n).im^2'''
new_eig = '''axiom l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2'''
content = content.replace(old_eig, new_eig, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: jlLParameterMap -> def')
