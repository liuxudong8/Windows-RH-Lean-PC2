import re

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到 jl_weighted_rearrangement 合并公理的位置，替换为新的结构
old_block = '''/-- JL 加权谱重排（合并公理）：
    (1) spectralSum f = Σ_k localJLWeight(k) · f(1/4 + t_k²)
    (2) jlFiberSize(k) = localJLWeight(k)
    合并了 jl_spectrum_rearrangement 和 jl_fiber_size_eq_weight 两条公理。 -/
axiom jl_weighted_rearrangement :
    (∀ (f : TestFunction), spectralSum f = ∑' k : ℕ, (localJLWeight k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2)) ∧
    (∀ (k : ℕ), (jlFiberSize k : ℝ) = localJLWeight k)

/-- JL 谱重排（定理，由合并公理推出）：
    spectralSum f = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。 -/
theorem jl_spectrum_rearrangement (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  have h1 := jl_weighted_rearrangement.1 f
  have h2 : ∀ k, (jlFiberSize k : ℝ) = localJLWeight k := jl_weighted_rearrangement.2
  rw [h1]
  <;> congr with k
  <;> rw [← h2 k] <;> norm_cast

/-- JL 纤维大小 = 局部权重（定理，由合并公理推出）：jlFiberSize(k) = localJLWeight(k)。 -/
theorem jl_fiber_size_eq_weight :
    ∀ (k : ℕ), (jlFiberSize k : ℝ) = localJLWeight k :=
  jl_weighted_rearrangement.2'''

new_block = '''/-- JL 谱映射的纤维有限性（公理，JL 对应的标准性质）：
    对每个 Maass 谱指标 k，三维谱指标中映射到 k 的纤维 {n | jlSpectrumMap n = k} 是有限集。
    数学依据：JL 对应是有限对一的，局部多重性有界（分裂素处最多 2，其他处为 1）。 -/
axiom jlSpectrumMap_finite_fibers :
    ∀ (k : ℕ), Set.Finite {n : ℕ | jlSpectrumMap n = k}

/-- 谱和的纤维分解（公理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    数学依据：specDiscM n = 1/4 + t_{jlSpectrumMap(n)}²（jl_spectrum_preserving），
    按 jlSpectrumMap 的纤维重排求和。纤维有限性由 jlSpectrumMap_finite_fibers 保证。
    后续可降级为 theorem（需 tsum_fiberwise + Summable 条件）。 -/
axiom spectral_sum_fiberwise :
    ∀ (f : TestFunction), spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2)

/-- JL 纤维大小 = 局部权重（公理，JL 数论内容）：
    jlFiberSize(k) = localJLWeight(k)（分裂素处为 1/2，分歧/惯性素处为 1）。
    这是 JL 对应的局部多重性理论，不是纯求和重排。 -/
axiom jl_fiber_size_eq_weight :
    ∀ (k : ℕ), (jlFiberSize k : ℝ) = localJLWeight k

/-- JL 谱重排（定理，由纤维分解公理直接推出）：
    spectralSum f = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。 -/
theorem jl_spectrum_rearrangement (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) :=
  spectral_sum_fiberwise f

/-- JL 加权谱重排（定理，由纤维分解 + 纤维大小公式推出）：
    spectralSum f = Σ_k localJLWeight(k) · f(1/4 + t_k²)。 -/
theorem jl_weighted_spectrum_sum (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (localJLWeight k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  rw [jl_spectrum_rearrangement f]
  <;> congr with k
  <;> rw [← jl_fiber_size_eq_weight k] <;> norm_cast'''

content = content.replace(old_block, new_block, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
