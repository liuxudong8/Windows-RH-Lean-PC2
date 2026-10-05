f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """noncomputable def specDiscM : ℕ → ℝ := fun _ => 0
noncomputable def maassSpecParam : ℕ → ℝ := fun _ => 0

/-- 三维离散谱非负（公理）：
    Laplace-Beltrami 算子 Δ_M 是自伴椭圆算子，本征值 ≥ 0。 -/
axiom specDiscM_nonneg_axiom : ∀ n : ℕ, 0 ≤ specDiscM n

/-- 三维离散谱严格递增（公理）：
    按本征值从小到大排列（计重数）。 -/
axiom specDiscM_strict_mono_axiom : ∀ n : ℕ, specDiscM n < specDiscM (n + 1)

/-- 三维离散谱无界（公理）：
    离散谱趋向 +∞（Weyl 定律）。 -/
axiom specDiscM_unbounded_axiom : ∀ M : ℝ, ∃ n : ℕ, specDiscM n > M

/-- 三维离散谱 SpecDisc(M) 的性质束（定理，由三个原子公理合取）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem specDiscM_properties :
    (∀ n : ℕ, 0 ≤ specDiscM n) ∧
    (∀ n : ℕ, specDiscM n < specDiscM (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, specDiscM n > M) :=
  ⟨specDiscM_nonneg_axiom, specDiscM_strict_mono_axiom, specDiscM_unbounded_axiom⟩

/-- Maass 谱参数非负（公理）：
    取 t ≥ 0 分支（t 与 -t 对应同一本征值 λ=1/4+t²）。 -/
axiom maassSpecParam_nonneg_axiom : ∀ n : ℕ, 0 ≤ maassSpecParam n

/-- Maass 谱参数严格递增（公理）：
    按 |t| 从小到大排列。 -/
axiom maassSpecParam_strict_mono_axiom : ∀ n : ℕ, maassSpecParam n < maassSpecParam (n + 1)

/-- Maass 谱参数无界（公理）：
    Maass 谱参数趋向 +∞（Weyl 定律）。 -/
axiom maassSpecParam_unbounded_axiom : ∀ M : ℝ, ∃ n : ℕ, maassSpecParam n > M

/-- Maass 谱参数 SpecMaass(X) 的性质束（定理，由三个原子公理合取）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem maassSpecParam_properties :
    (∀ n : ℕ, 0 ≤ maassSpecParam n) ∧
    (∀ n : ℕ, maassSpecParam n < maassSpecParam (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, maassSpecParam n > M) :=
  ⟨maassSpecParam_nonneg_axiom, maassSpecParam_strict_mono_axiom, maassSpecParam_unbounded_axiom⟩"""

new = """/-- 三维离散谱序列的存在性（公理，第一档）：
    存在序列 s : ℕ → ℝ，满足：(1) 非负 (2) 严格递增 (3) 无界。
    这是自伴椭圆算子离散谱的标准性质（Weyl 定律）。 -/
axiom specDiscM_exists :
    ∃ (s : ℕ → ℝ),
      (∀ n : ℕ, 0 ≤ s n) ∧
      (∀ n : ℕ, s n < s (n + 1)) ∧
      (∀ M : ℝ, ∃ n : ℕ, s n > M)

/-- 三维离散谱（定义，由存在性公理通过 Classical.choose 给出）。 -/
noncomputable def specDiscM : ℕ → ℝ := Classical.choose specDiscM_exists

/-- 三维离散谱 SpecDisc(M) 的性质束（定理，由 Classical.choose_spec 推出）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem specDiscM_properties :
    (∀ n : ℕ, 0 ≤ specDiscM n) ∧
    (∀ n : ℕ, specDiscM n < specDiscM (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, specDiscM n > M) :=
  Classical.choose_spec specDiscM_exists

/-- Maass 谱参数序列的存在性（公理，第一档）：
    存在序列 t : ℕ → ℝ，满足：(1) 非负 (2) 严格递增 (3) 无界。
    这是 Maass 形式谱参数的标准性质（Weyl 定律）。 -/
axiom maassSpecParam_exists :
    ∃ (t : ℕ → ℝ),
      (∀ n : ℕ, 0 ≤ t n) ∧
      (∀ n : ℕ, t n < t (n + 1)) ∧
      (∀ M : ℝ, ∃ n : ℕ, t n > M)

/-- Maass 谱参数（定义，由存在性公理通过 Classical.choose 给出）。 -/
noncomputable def maassSpecParam : ℕ → ℝ := Classical.choose maassSpecParam_exists

/-- Maass 谱参数 SpecMaass(X) 的性质束（定理，由 Classical.choose_spec 推出）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem maassSpecParam_properties :
    (∀ n : ℕ, 0 ≤ maassSpecParam n) ∧
    (∀ n : ℕ, maassSpecParam n < maassSpecParam (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, maassSpecParam n > M) :=
  Classical.choose_spec maassSpecParam_exists"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: specDiscM/maassSpecParam -> Classical.choose, 6 axioms -> 2 exists axioms')
