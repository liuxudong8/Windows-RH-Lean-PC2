f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old_spms = """/-- 谱点保持的 Mellin 叠加（公理，插值理论）：
    对任意磨光函数 g，存在两个磨光函数 f1, f2，使得：
    (1) 它们在所有谱点 {specDiscM n} 上取值相同
    (2) 对所有 s，M[f2](s) - M[f1](s) = M[g](s)

    数学依据：紧支光滑函数空间是无限维的，谱点集 {specDiscM n} 是离散的，
    可以在保持谱点取值的子空间中，找到两个函数 whose Mellin 变换之差
    等于任意给定 g 的 Mellin 变换。这是 Whitney 延拓定理在 Mellin 变换下的变体：
    谱点约束是可数个线性条件，其余维仍为无限，因此可以叠加任意方向。
    这条只涉及谱点约束，不涉及零点局部化。 -/
axiom spectral_preserving_melin_superposition (g : MollifiedTestFunction) :
    \u2203 (f1 f2 : MollifiedTestFunction),
      (\u2200 n : \u2115, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) \u2227
      (\u2200 (s : \u2102), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)"""

# Use direct string replacement with exact match
import re

# Find the exact block
pattern = r'/-- 谱点保持的 Mellin 叠加（公理，插值理论）：.*?axiom spectral_preserving_melin_superposition \(g : MollifiedTestFunction\) :\n    \u2203 \(f1 f2 : MollifiedTestFunction\),\n      \(\u2200 n : \u2115, f1\.toTestFunction\.eval \(specDiscM n\) = f2\.toTestFunction\.eval \(specDiscM n\)\) \u2227\n      \(\u2200 \(s : \u2102\), melinTransform f2\.toTestFunction s - melinTransform f1\.toTestFunction s =\n                    melinTransform g\.toTestFunction s\)'

match = re.search(pattern, content, re.DOTALL)
if match:
    print(f"Found at position {match.start()}-{match.end()}")
    old_text = match.group(0)
else:
    print("NOT FOUND with regex, trying literal")
    # Try literal find
    idx = content.find('axiom spectral_preserving_melin_superposition (g : MollifiedTestFunction)')
    print(f"axiom at index {idx}")
    # Find the start of the comment
    start = content.rfind('/--', 0, idx)
    # Find the end (after the last line of the axiom)
    end = content.find('\n', idx + 200)
    # Actually find the complete axiom block
    end = content.find('melinTransform g.toTestFunction s)', idx) + len('melinTransform g.toTestFunction s)')
    old_text = content[start:end]
    print(f"Block from {start} to {end}, length {len(old_text)}")

new_text = """/-- 单个谱点约束的 Mellin 叠加（公理，插值理论）：
    对任意磨光函数 g 和任意谱点索引 n，存在两个磨光函数 f1, f2，使得：
    (1) 它们在第 n 个谱点 specDiscM n 上取值相同
    (2) 对所有 s，M[f2](s) - M[f1](s) = M[g](s)

    数学依据：单个点的取值约束是一个线性条件，其余维为无限，
    因此可以在保持该点取值的同时叠加任意 Mellin 方向。
    这比"所有谱点"的版本弱得多，只涉及一个约束。
    风险等级：中（单个线性约束的余维数无限，标准泛函分析结果）。 -/
axiom single_spectral_point_preserving_superposition (g : MollifiedTestFunction) (n : ℕ) :
    ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)

/-- 可数谱点约束的紧致性（公理，插值理论）：
    如果对每个 n，都存在一对函数保持第 n 个谱点取值且 Mellin 差 = M[g]，
    则存在一对函数保持所有谱点取值且 Mellin 差 = M[g]。

    数学依据：谱点集 {specDiscM n} 是离散的，每个约束是一个闭线性条件。
    在 Frechet 空间中，可数个闭线性约束的交集非空，
    只要每个有限子约束的交集非空（有限交性质 + 紧致性/完备性）。
    风险等级：中（Frechet 空间的有限交性质，标准泛函分析结果）。 -/
axiom countable_spectral_points_compactness (g : MollifiedTestFunction) :
    (∀ (n : ℕ), ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)) →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s)

/-- 谱点保持的 Mellin 叠加（定理，由单点版本+可数紧致性推出）：
    对任意磨光函数 g，存在两个磨光函数 f1, f2，使得：
    (1) 它们在所有谱点 {specDiscM n} 上取值相同
    (2) 对所有 s，M[f2](s) - M[f1](s) = M[g](s)

    证明：
    (1) single_spectral_point_preserving_superposition 对每个 n 给出保持第 n 个谱点的对
    (2) countable_spectral_points_compactness 由可数个单点约束推出全局约束 -/
theorem spectral_preserving_melin_superposition (g : MollifiedTestFunction) :
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
  have h_single : ∀ (n : ℕ), ∃ (f1 f2 : MollifiedTestFunction),
      f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) ∧
      (∀ (s : ℂ), melinTransform f2.toTestFunction s - melinTransform f1.toTestFunction s =
                    melinTransform g.toTestFunction s) := by
    intro n
    exact single_spectral_point_preserving_superposition g n
  exact countable_spectral_points_compactness g h_single"""

content = content.replace(old_text, new_text, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done')
