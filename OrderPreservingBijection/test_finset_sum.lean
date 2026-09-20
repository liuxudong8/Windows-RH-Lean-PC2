import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- melinTransform 保持有限和。 -/
lemma melinTransform_finset_sum {α : Type*} (s : Finset α) (f : α → TestFunction) (c : α → ℂ) (z : ℂ) :
    melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, c i * melinTransform (f i) z := by
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert a s ha ih =>
    have h1 : (∑ i ∈ insert a s, c i • f i) = (c a • f a) + (∑ i ∈ s, c i • f i) := by
      rw [Finset.sum_insert ha] <;> rfl
    rw [h1]
    have h2 : melinTransform ((c a • f a) + (∑ i ∈ s, c i • f i)) z =
        c a * melinTransform (f a) z + melinTransform (∑ i ∈ s, c i • f i) z := by
      have h_lin := melinTransform_linear (f a) (∑ i ∈ s, c i • f i) (c a) (1 : ℂ) z
      simpa using h_lin
    rw [h2, ih]
    rw [Finset.sum_insert ha] <;> ring

end RHSpectralDuality
end OrderPreservingBijection
