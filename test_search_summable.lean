import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 搜索比值判别法
#check Summable.of_ratio_bounded
#check summable_of_ratio_test

-- 用更简单的方法：(k+1)^2 ≤ 4^k 对所有 k（显然），然后 (k+1)^2/2^k ≤ 2^k... 不收敛
-- 用 (k+1)^2 ≤ (3/2)^k * C，需要找 C

-- 直接证明：∀ k ≥ 6, (k+1)^2 ≤ (4/3)^k * 某个常数
-- 验证 k=6: 49 ≤ (4/3)^6 ≈ 5.6 — 不成立
-- k=20: 441 ≤ (4/3)^20 ≈ 315 — 不成立
-- k=30: 961 ≤ (4/3)^30 ≈ 2560 — 成立

-- 换思路：用已知定理 summable_nat_pow_mul_geometric 或类似
-- 搜索：
#check Real.summable_pow_mul_geometric
#check summable_nat_mul_geometric

end RHSpectralDuality
