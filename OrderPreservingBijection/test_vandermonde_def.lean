import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

variable (n : ℕ) (v : Fin n → ℂ) (i j : Fin n)

#check Matrix.vandermonde v
#reduce (Matrix.vandermonde v) i j
#check Matrix.vandermonde_apply

end RHSpectralDuality
end OrderPreservingBijection
