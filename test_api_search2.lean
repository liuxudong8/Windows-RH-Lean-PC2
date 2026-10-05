import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 搜索 tsum 相关
#check tsum_le_tsum
#check Finset.sum_le_tsum?
#check Summable.tsum_eq_sum

-- 搜索 Set.Finite 相关
#check Set.Finite.image
#check Set.Finite.of_finite_image
#check Set.injOn_iff_injective

-- 搜索 Set.Finite.subset
#check Set.Finite.subset

end RHSpectralDuality
