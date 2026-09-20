import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

variable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0)

#check Matrix.nonsing_inv_mul A
#check (Matrix.nonsing_inv_mul A) h

end RHSpectralDuality
end OrderPreservingBijection
