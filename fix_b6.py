f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除旧注释（第1442-1451行附近）
old_comment = """/-- 磨光函数的谱点插值能力（公理）：
    对任意谱指标 n，存在磨光测试函数 δ_n，使得它在谱点上取 Kronecker delta：
      δ_n.eval(specDiscM k) = 1  if k = n
      δ_n.eval(specDiscM k) = 0  if k ≠ n
    数学内容：紧支集光滑函数族 C_c^∞(ℝ) 具有足够的自由度，
    可以在可数个离散点集 {specDiscM k} 上任意指定取值。
    这是 Whitney 延拓定理在离散点集上的推论：
    离散点集（无聚点，因 specDiscM 严格递增且趋向无穷）上的任意函数
    都可以延拓为紧支集光滑函数。
    这是正向显式公式局部化论证的基础。 -/
/-- Mellin 差方向"""

new_comment = """/-- Mellin 差方向"""

content = content.replace(old_comment, new_comment, 1)

# 2. 在 specDiscM_strict_mono 之后添加 specDiscM_injective
old_inj = """/-- 三维离散谱无界（由 specDiscM_properties 推出） -/
theorem specDiscM_unbounded (M : ℝ) : ∃ n : ℕ, specDiscM n > M :=
  specDiscM_properties.2.2 M"""

new_inj = """/-- specDiscM 单射（由严格递增推出） -/
theorem specDiscM_injective : Function.Injective specDiscM := by
  intro m n h
  by_cases hmn : m < n
  · have h_lt : specDiscM m < specDiscM n := by
      induction' hmn with n hmn ih
      · exact specDiscM_strict_mono m
      · exact lt_trans ih (specDiscM_strict_mono n)
    linarith
  · by_cases hnm : n < m
    · have h_lt : specDiscM n < specDiscM m := by
        induction' hnm with m hnm ih
        · exact specDiscM_strict_mono n
        · exact lt_trans ih (specDiscM_strict_mono m)
      linarith
    · have h_eq : m = n := by omega
      exact h_eq

/-- 三维离散谱无界（由 specDiscM_properties 推出） -/
theorem specDiscM_unbounded (M : ℝ) : ∃ n : ℕ, specDiscM n > M :=
  specDiscM_properties.2.2 M"""

content = content.replace(old_inj, new_inj, 1)

# 3. 修复 mollified_spectral_delta 中的 specDiscM_strict_mono_axiom.injective
old_inj2 = "      have h_inj : k = n := specDiscM_strict_mono_axiom.injective h"
new_inj2 = "      have h_inj : k = n := specDiscM_injective h"
content = content.replace(old_inj2, new_inj2, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: removed old comment, added specDiscM_injective, fixed proof')
