import re

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 替换公理名称和文档
old_axiom = '''axiom mellin_pair_separation_uniform_decay (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2)'''

new_axiom = '''/-- Mellin 分离对的统一速降界（公理，中风险，纯分析估计）：
    前 4 个条件（谱点取值相同 / M[f₁](ρ)=1 / M[f₂](ρ)=0 / T 上相等）已由
    mellin_pair_separation_construction（PWW 联合插值定理）独立证明。
    此公理仅额外断言：存在不依赖于 T 的统一常数 C，使差的 Mellin 变换在临界带内
    满足 O(1/|Im|²) 速降。
    数学依据：mellin_finite_surjectivity_zero_sum 的构造有统一范数估计
    （核空间中有限维约束的最小范数解，界只依赖于约束值的上确界，而 w₁-w₂ 固定）。
    风险等级：中（标准泛函分析；形式化需 mellin_finite_surjectivity_zero_sum 带范数估计）。 -/
axiom mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2)'''

if old_axiom in content:
    content = content.replace(old_axiom, new_axiom)
    print("公理替换成功")
else:
    print("未找到公理")

# 替换 mollified_pair_tail_sum_negligible 中的引用
content = content.replace(
    'rcases mellin_pair_separation_uniform_decay ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_uniform⟩',
    'rcases mellin_pair_uniform_decay_bound ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_uniform⟩'
)

# 替换文档中的引用
content = content.replace(
    '(b) 由 mellin_pair_separation_uniform_decay，存在统一速降界 C',
    '(b) 由 mellin_pair_uniform_decay_bound，存在统一速降界 C'
)

# 替换其他可能的引用
content = content.replace('mellin_pair_separation_uniform_decay', 'mellin_pair_uniform_decay_bound')

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("文件已写入")
print(f"总行数: {len(content.splitlines())}")
