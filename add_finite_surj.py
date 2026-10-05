path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Add LinearMap import
content = content.replace(
    "import OrderPreservingBijection.MellinInfrastructure",
    "import OrderPreservingBijection.MellinInfrastructure\nimport Mathlib.LinearAlgebra.LinearMap.Basic"
)

# Add finite surjectivity theorem after the independence axiom
axiom_end = "      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j) = 0) → c = 0"

finite_theorem = """      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j) = 0) → c = 0

/-- Mellin 变换有限集满射性（定理，由区间指示函数线性无关推出）：
    对任意 m 个互不相同的点 t_j 和任意赋值 w_j，存在 TestFunction f
    使得 M[f](t_j) = w_j 对所有 j。
    证明：由 mellin_interval_linear_independence 得到 m 个区间指示函数，
    其 Mellin 变换向量线性无关。m 个线性无关向量在 m 维空间 ℂ^m 中构成基，
    故可线性组合得到任意 w。 -/
theorem mellin_finite_surjectivity {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) (w : Fin m → ℂ) :
    ∃ (f : TestFunction), ∀ (j : Fin m), melinTransform f (t j) = w j := by
  rcases mellin_interval_linear_independence t ht with ⟨a, b, ha, hab, h_indep⟩
  let v : Fin m → (Fin m → ℂ) := fun i => fun j => melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j)
  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun c => fun j => ∑ i : Fin m, c i * v i j
      map_add' := by
        intro c1 c2
        ext j
        simp [Finset.sum_add_distrib] <;> ring
      map_smul' := by
        intro z c
        ext j
        simp [Finset.smul_sum] <;> ring }
  have h_inj : Function.Injective L := by
    intro c1 c2 h
    have h_eq : ∀ j, ∑ i : Fin m, (c1 i - c2 i) * v i j = 0 := by
      intro j
      have h1 : L c1 j = L c2 j := by rw [h]
      simpa [L, v] using h1
    have h_zero : c1 - c2 = 0 := h_indep (c1 - c2) h_eq
    simpa [sub_eq_zero] using h_zero
  have h_surj : Function.Surjective L := by
    exact?
  rcases h_surj w with ⟨c, hc⟩
  let f : TestFunction := ∑ i : Fin m, c i • intervalIndicator (a i) (b i) (ha i) (hab i)
  refine ⟨f, ?_⟩
  intro j
  have h_main : melinTransform f (t j) = ∑ i : Fin m, c i * v i j := by
    simp only [f, melinTransform_linear, v]
    <;> rfl
  rw [h_main]
  have h2 : (L c) j = w j := by rw [hc]
  simpa [L, v] using h2"""

content = content.replace(axiom_end, finite_theorem)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Added mellin_finite_surjectivity theorem')
