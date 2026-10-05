f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 恢复 jlSpectrumMap 为 opaque
old_jl = """/-- JL 谱映射的存在性（公理，第二档）：
    存在映射 φ : ℕ → ℕ，使得 Shimura 提升把第 φ(n) 个 Maass 本征函数
    映射到第 n 个三维本征函数。这是 Jacquet-Langlands 对应的谱层面表述。 -/
axiom jlSpectrumMap_exists :
    ∃ (φ : ℕ → ℕ), ∀ (n : ℕ),
      shimuraLift (maassEigenfunction (φ n)) = threeManifoldEigenfunction n

/-- JL 谱映射（定义，由存在性公理通过 Classical.choose 给出）。
    φ : ℕ → ℕ 将三维双曲流形 M 的离散谱索引
    映射到四元数代数曲面 X 的 Maass 谱索引。 -/
noncomputable def jlSpectrumMap : ℕ → ℕ :=
    Classical.choose jlSpectrumMap_exists"""

new_jl = """/-- JL 谱映射（抽象不透明常量）。
    φ : ℕ → ℕ 将三维双曲流形 M 的离散谱索引
    映射到四元数代数曲面 X 的 Maass 谱索引。 -/
opaque jlSpectrumMap : ℕ → ℕ"""

content = content.replace(old_jl, new_jl, 1)

# 恢复 shimuraLift_eigenfunction_correspondence 为公理
old_corr = """/-- Shimura 提升的特征函数对应（定理，由 jlSpectrumMap_exists + Classical.choose_spec 推出）：
    U(φ_{jlSpectrumMap(n)}) = ψ_n。 -/
theorem shimuraLift_eigenfunction_correspondence :
    ∀ (n : ℕ),
      shimuraLift (maassEigenfunction (jlSpectrumMap n)) = threeManifoldEigenfunction n :=
    Classical.choose_spec jlSpectrumMap_exists"""

new_corr = """/-- Shimura 提升的特征函数对应（公理）：U(φ_{jlSpectrumMap(n)}) = ψ_n。 -/
axiom shimuraLift_eigenfunction_correspondence :
    ∀ (n : ℕ),
      shimuraLift (maassEigenfunction (jlSpectrumMap n)) = threeManifoldEigenfunction n"""

content = content.replace(old_corr, new_corr, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: restored jlSpectrumMap as opaque')
