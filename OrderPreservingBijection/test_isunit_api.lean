import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

variable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0)

#check IsUnit
#check (Units.mk0 (A.det) h)
#check (Units.mk0 (A.det) h).isUnit

end RHSpectralDuality
end OrderPreservingBijection
