import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

-- 测试 melinTransform_linear 的基本应用
lemma test_linear_basic (f1 f2 : TestFunction) (c1 c2 : ℂ) (z : ℂ) :
    melinTransform (c1 • f1 + c2 • f2) z = c1 * melinTransform f1 z + c2 * melinTransform f2 z :=
  melinTransform_linear f1 f2 c1 c2 z

-- 测试 TestFunction 的 AddCommMonoid
lemma test_sum (f : ℕ → TestFunction) : TestFunction := ∑ i ∈ Finset.range 3, f i

end RHSpectralDuality
end OrderPreservingBijection
