import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 搜索 summable_of_sum_range_le 签名
#check summable_of_sum_range_le

-- 搜索非负函数有界和等价于 Summable
#check Summable.of_nonneg_of_bounded
#check summable_iff_bounded

-- 搜索 Finset.fold max
#check Finset.fold

end RHSpectralDuality
