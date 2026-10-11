import BSD.LPrime43
import BSD.LSeries5_43

/-!
# _check_43a1 —— 43a1 (1,0) 型排除层对象级非零闭证

组装：秩 1 侧 `BSD.LPrime43.lprime1_43_pos`（L′(43a1,1) > 0，真定理，18 轮迭代闭合）
× 秩 0 侧 `BSD.LSeries5_43.L_E5_43_one_ne_zero`（L(E⁵,1) ≠ 0，真定理，级数区间算术闭合）。

与 `ExclusionReduction.exclusion_layer_nonzero`（37a1 版 `BSD.LK_prime ≠ 0`）同构：
43 版以 `BSD.L_prime_43 ≠ 0` 显式闭证排除层。
-/

namespace BSD

/-- 43a1 排除层对象：L′(43a1,1) · L(E⁵,1)（Artin 分解 + 乘积求导 + L(E,1)=0 的形态）。 -/
noncomputable def L_prime_43 : ℝ := BSD.LPrime43.lprime1_43 * BSD.LSeries5_43.L_E5_43 1

/-- 43a1 排除层非零（对象级）：两个 ℚ 侧非零性相乘。 -/
theorem L_prime_43_ne_zero : L_prime_43 ≠ 0 := by
  unfold L_prime_43
  exact mul_ne_zero (ne_of_gt BSD.LPrime43.lprime1_43_pos)
    BSD.LSeries5_43.L_E5_43_one_ne_zero

end BSD
