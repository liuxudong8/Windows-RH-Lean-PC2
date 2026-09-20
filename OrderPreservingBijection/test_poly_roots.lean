import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助：如果次数 < n 的多项式在 n 个不同点为零，则多项式为零。 -/
lemma polynomial_roots_implies_zero (n : ℕ) (v : Fin n → ℂ) (hv_distinct : ∀ i j, i ≠ j → v i ≠ v j)
    (c : Fin n → ℂ) (h : ∀ j, ∑ i : Fin n, c i * (v j) ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  -- 这个引理需要 Polynomial 基础设施，暂时用公理代替
  sorry

end RHSpectralDuality
end OrderPreservingBijection
