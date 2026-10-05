with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_axiom = '''/-- 正向谱-零点对应（公理，暂留，稍后在 distributionSupport 定义后降为 theorem）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。 -/
axiom maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ)

'''

if old_axiom in content:
    content = content.replace(old_axiom, '')
    print("删除 axiom 成功")
else:
    print("未找到 axiom")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
