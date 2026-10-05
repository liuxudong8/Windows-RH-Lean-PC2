import OrderPreservingBijection.stage_4

open scoped BigOperators
open Finset

-- P0.2 探针 2：单点 tsum/HasSum、tsum 线性、norm 界 API
#check hasSum_single
#check summable_of_finite_support
#check Summable.of_norm_bounded
#check Summable.of_norm
#check tsum_sub
#check Summable.tsum_sub
#check HasSum.sub
#check HasSum.add
#check HasSum.tsum_eq
#check hasSum_zero
#check summable_zero
#check tsum_eq_sum
#check tsum_zero
#check hasSum_ite_eq
#check summable_iff_vanishing_norm
#check tendsto_tsum_compl_atTop_zero
#check Summable.mul_left
#check Summable.of_nonneg_of_le
#check norm_mul_le
#check norm_natCast
