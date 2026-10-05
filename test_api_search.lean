import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 搜索 pow 相关定理
#check pow_lt_pow_right₀
#check pow_le_pow_right₀
#check pow_strictMono
#check pow_monotone

-- 搜索 Finset.sum_le_tsum
#check Finset.sum_le_tsum_of_nonneg
#check sum_le_tsum

-- 搜索 Set.Finite.of_injective_image
#check Set.Finite.of_injective
#check Set.injOn_image

-- 搜索 nontrivialZeroEnum_are_zeros
#check nontrivialZeroEnum_are_zeros

end RHSpectralDuality
