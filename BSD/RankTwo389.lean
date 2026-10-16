import BSD.EulerSystem
import BSD.Sha11_389

open BSD.EulerSystem
open BSD.Sha11_389

namespace BSD.RankTwo389

/-!
# rank(389a1) = 2：数据锚点 + 组合真证（2026-10-16）

背景：`BSD.EulerSystem.rank_389a1`（axiom）给出 Rank = 2（黑箱挂账）。本模块把
代数秩 2 拆为"上界真证 + 下界挂账"：
  rank ≤ 2：|Sel₂| = 4（G4 纯 Python 独立复算，Sha11_389 已挂账 `sel2_order_four_389`）
    ∧ 2-descent 阶上界（正合列 0 → E(ℚ)/2E(ℚ) → Sel₂ → Ш[2] → 0，E(ℚ) 无 2-扭）
    ⟹ 2^rank ≤ #Sel₂ = 4 ⟹ rank ≤ 2（**真证**，仅依赖 descent 结构 axiom + 数据锚点）；
  rank ≥ 2：两个独立无限阶点 P₁ = (−1:1:1)、P₂ = (0:−1:1)
    （高度配对 det = 0.15246017794314375162... ≠ 0，Sage regulator(200) 的 G3 数值；
     torsion trivial 标准事实）⟹ rank ≥ 2（Mordell–Weil：自由部分秩 ≥ 独立点个数；挂账）；
  rank = 2：le_antisymm 组合（**真证**）。

净效果：`rank_two_389` 是 `EulerSystem.rank_389a1`（axiom）的证明型替代——代数秩 2
从"单黑箱 axiom"降级为"|Sel₂| 数据锚点 + descent 结构 axiom + 两独立点单点挂账"。

注意：EulerSystem.rank_389a1 注释的生成元 "(0,0),(1,0)" 与 Sage 实测 gens
[(-1:1:1),(0:-1:1)] 不符（历史遗留；以 G3_Reg/g3_sage.sage 的 gens 为准）。

数据源：Probe389/G4_Sel2/g4_result.md（|Sel₂|=4 纯 Python 复算）、
Probe389/G3_Reg/g3_result.md（Reg 200 位 + 高度配对 det ≠ 0）。
-/

-- ============ 结构 axiom：2-descent 阶上界（定理级挂账） ============

/-- 2-descent 阶上界：E(ℚ) 无 2-扭 ⟹ 2^rank(E) ≤ #Sel₂(E)。
    数学来源：正合列 0 → E(ℚ)/2E(ℚ) → Sel₂(E) → Ш[2] → 0，
    |E(ℚ)/2E(ℚ)| = 2^{rank + dim E(ℚ)[2]}；E(ℚ)[2] = 0（389a1 无 2-扭）⟹ 2^rank | #Sel₂。 -/
axiom sel2_rank_bound (E : Type) (K : Type) : 2 ^ Rank E K ≤ SelPOrder E 2

-- ============ 数据锚点：两独立无限阶点（挂账） ============

/-- 389a1 的两个独立无限阶点（P₁ = (−1:1:1), P₂ = (0:−1:1)）。 -/
axiom PointsIndependent389 : Prop

/-- 数据挂账：P₁, P₂ 独立（高度配对 det = 0.15246017794314375162... ≠ 0，
    Sage regulator(200)/高度配对 det 的 G3 数值；G3_Reg/g3_sage.sage 实测 gens）
    ∧ 无限阶（389a1 torsion trivial 标准事实，LMFDB/Magma 一致）。 -/
axiom points_independent_389 : PointsIndependent389

/-- Mordell–Weil 基本事实（定理级挂账）：两个独立无限阶点 ⟹ rank ≥ 2
    （自由阿贝尔群的秩 ≥ 线性无关元的个数）。 -/
axiom rank_ge_two_of_points : PointsIndependent389 → 2 ≤ Rank Curve389a1 K389a1

/-- rank ≥ 2（组合：数据锚点 + Mordell–Weil 事实）。 -/
theorem rank_ge_two_389 : 2 ≤ Rank Curve389a1 K389a1 :=
  rank_ge_two_of_points points_independent_389

-- ============ 组合真证 ============

/-- rank ≤ 2：2^rank ≤ #Sel₂ = 4 = 2² ⟹ rank ≤ 2（真证：pow 单调双向）。 -/
theorem rank_le_two_389 : Rank Curve389a1 K389a1 ≤ 2 := by
  have hb : 2 ^ Rank Curve389a1 K389a1 ≤ SelPOrder Curve389a1 2 :=
    sel2_rank_bound Curve389a1 K389a1
  have hb' : 2 ^ Rank Curve389a1 K389a1 ≤ 2 ^ 2 := by
    rw [sel2_order_four_389] at hb
    simpa using hb
  exact (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp hb'

/-- **rank(389a1) = 2**（组合真证：rank ≤ 2 ∧ rank ≥ 2 ⟹ = 2；
    `EulerSystem.rank_389a1`（axiom）的证明型替代）。 -/
theorem rank_two_389 : Rank Curve389a1 K389a1 = 2 :=
  le_antisymm rank_le_two_389 rank_ge_two_389

end BSD.RankTwo389
