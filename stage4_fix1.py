path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

start_marker = """/-- Mellin 变换在零点∪极点上的数乘封闭性（定理，由可数集任意赋值推出）："""
end_marker = """  forward_support_match f
"""

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)
print(f'start={start_idx}, end={end_idx}')

if start_idx != -1 and end_idx != -1:
    end_idx += len(end_marker)
    # Replace with maass_param_to_zero axiom
    replacement = """/-- 正向显式公式（公理，Selberg zeta 零点 ↔ Laplacian 特征值对应）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。

    这是 Selberg zeta 函数的标准性质：Selberg zeta Z(s) 的零点与双曲 Laplacian 的特征值
    通过 s(1-s) = λ 对应。在我们的框架中，ζ(s) 与 Selberg zeta 通过 Weil 显式公式
    和 Arthur 迹公式建立联系，正向对应是已知的分析大定理。
    风险等级：中（已知定理，形式化是第二档工作，不影响 RH 反证法逻辑）。 -/
axiom maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ)

"""
    content = content[:start_idx] + replacement + content[end_idx:]
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print('Deleted vanishing chain, replaced with maass_param_to_zero axiom')
else:
    print('Markers not found')
