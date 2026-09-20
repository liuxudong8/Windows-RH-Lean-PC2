import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 固定 z 的 Mellin 变换作为 AddMonoidHom。 -/
noncomputable def melinTransformAt (z : ℂ) : TestFunction →+ ℂ where
  toFun f := melinTransform f z
  map_zero' := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) z
    simpa using h
  map_add' := by
    intro f1 f2
    have h_eq1 : (f1 + f2 : TestFunction) = (1 : ℂ) • f1 + (1 : ℂ) • f2 := by simp
    calc
      melinTransform (f1 + f2) z
        = melinTransform ((1 : ℂ) • f1 + (1 : ℂ) • f2) z := by rw [h_eq1]
      _ = (1 : ℂ) * melinTransform f1 z + (1 : ℂ) * melinTransform f2 z :=
        melinTransform_linear f1 f2 (1 : ℂ) (1 : ℂ) z
      _ = melinTransform f1 z + melinTransform f2 z := by ring

/-- melinTransform 保持有限和。 -/
lemma melinTransform_finset_sum {α : Type*} (s : Finset α) (f : α → TestFunction) (c : α → ℂ) (z : ℂ) :
    melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, c i * melinTransform (f i) z := by
  have h1 : melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, melinTransform (c i • f i) z := by
    exact map_sum (melinTransformAt z) (fun i => c i • f i) s
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : melinTransform (c i • f i) z = c i * melinTransform (f i) z := by
    have h3 := melinTransform_linear (f i) (0 : TestFunction) (c i) (0 : ℂ) z
    simpa using h3
  exact h2

end RHSpectralDuality
end OrderPreservingBijection
