import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 1 • f = f 对 TestFunction。 -/
lemma one_smul_testfunction (f : TestFunction) : (1 : ℂ) • f = f := by
  apply TestFunction.toFun_injective
  funext x
  change (1 : ℂ) * f.eval x = f.eval x
  ring

/-- melinTransform 保持有限和。 -/
lemma melinTransform_finset_sum {α : Type*} (s : Finset α) (f : α → TestFunction) (c : α → ℂ) (z : ℂ) :
    melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, c i * melinTransform (f i) z := by
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert a s ha ih =>
    have h1 : (∑ i ∈ insert a s, c i • f i) = (c a • f a) + (∑ i ∈ s, c i • f i : TestFunction) := by
      rw [Finset.sum_insert ha] <;> rfl
    rw [h1]
    set g : TestFunction := (∑ i ∈ s, c i • f i : TestFunction) with hg_def
    have h_one_smul : (1 : ℂ) • g = g := one_smul_testfunction g
    have h_lin : melinTransform ((c a • f a) + g) z = c a * melinTransform (f a) z + melinTransform g z := by
      have h := melinTransform_linear (f a) g (c a) (1 : ℂ) z
      rw [h_one_smul] at h
      simpa using h
    rw [h_lin, ih]
    rw [Finset.sum_insert ha] <;> ring

end RHSpectralDuality
end OrderPreservingBijection
