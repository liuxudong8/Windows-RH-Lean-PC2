import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

#check Summable.comp_injective
#check Nat.add_left_cancel
#check add_right_injective
#check summable_nat_add_iff

-- 拆分验证（修正版）
example {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, f n) = (∑ i ∈ Finset.range 3, f i) + ∑' n, f (n + 3) := by
  have htail : Summable (fun n => f (n + 3)) := by
    exact hf.comp_injective (fun n m h => by omega)
  have hs : HasSum (fun n => f (n + 3)) (∑' n, f (n + 3)) := htail.hasSum
  have hfull : HasSum f ((∑' n, f (n + 3)) + ∑ i ∈ Finset.range 3, f i) :=
    (hasSum_nat_add_iff 3).mpr hs
  rw [← hfull.tsum_eq]
  ring

-- 尾项显式拆分：Σ' f(n+3) 的绝对值上界拆（验证 Summable.abs + tsum_le_tsum）
example {f g : ℕ → ℝ} (hfg : ∀ n, |f n| ≤ g n) (hg : Summable g) (hf : Summable f) :
    |∑' n, f (n + 3)| ≤ ∑' n, g (n + 3) := by
  have htail : Summable (fun n => f (n + 3)) := hf.comp_injective (fun n m h => by omega)
  have htail_g : Summable (fun n => g (n + 3)) := hg.comp_injective (fun n m h => by omega)
  have habs : Summable (fun n => |f (n + 3)|) := htail.abs
  have hle1 : |∑' n, f (n + 3)| ≤ ∑' n, |f (n + 3)| := by
    -- tsum 三角不等式：mathlib 里是 abs_tsum 系列？
    sorry
  have hle2 : ∑' n, |f (n + 3)| ≤ ∑' n, g (n + 3) := by
    exact Summable.tsum_le_tsum (fun n => hfg (n + 3)) habs htail_g
  exact le_trans hle1 hle2

-- 几何移位：Σ' q^(n+4) = q^4/(1-q)
example (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : (∑' n : ℕ, q ^ (n + 4)) = q ^ 4 * (1 - q)⁻¹ := by
  rw [← tsum_mul_left (a := q ^ 4)]
  congr 1
  funext n
  rw [pow_add]
  ring
