# -*- coding: utf-8 -*-
"""把 Dbg_Khat.lean 的 khat_second_order_bound 真证（含前置引理链）迁入 S7_1_Stage3.lean 替换 axiom。"""
import io

DBG = r"C:\proj2\QRH\Dbg_Khat.lean"
STAGE3 = r"C:\proj2\QRH\S7_1_Stage3.lean"

with io.open(DBG, "r", encoding="utf-8") as f:
    dbg = f.read()

start = dbg.index("private lemma abs_add_ineq")
end_marker = "simpa using hfin"
end = dbg.index(end_marker) + len(end_marker)
block = dbg[start:end]
# 改名：_dbg -> 正式名
block = block.replace("khat_second_order_bound_dbg", "khat_second_order_bound")

# 给主定理加迁入说明头
new_block = """/-! ### 件 1b：K̂ 二阶一致界真证（K̂ 导数闭式 + 区间界；替代原 axiom）

迁入自 Dbg_Khat.lean（2026-10-26 编译 exit=0）。数学链：
  K̂(u) = [cos(πu) − √2·πu·cotR(√2/2)·sin(πu)] / (1 − 2π²u²)（Khat_closed_form 乘形式）；
  |u| ≤ 1/24 ⟹ |m| = |πu| ≤ 2/15（π < 16/5），m² ≤ 4/225 ⟹ 分母 1−2m² ≥ 217/225 > 0；
  N = cos m − 1 + 2m² − √2·m·cotR·sin m = m²(3/2 − √2·cotR) + rc − √2·m·cotR·rs，
  其中 cos 二阶余项 |rc| ≤ m⁴·5/96（cos_bound）、sin 一阶余项 |rs| ≤ |m|⁵/100 + |m|³/6（sin_bound）；
  |3/2 − √2·cotR(√2/2)| ≤ 9/50（c0_bound，cotR ∈ [1, 237/200] 数值区间）；
  拼接得 |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴（194/1000·π² ≤ 2 由 π ≤ 16/5）。
  数值核对：½|K̂″(0)|≈1.53<2（2u² 系数）、π²≈9.87、√2·cotR≈3/2。 -/

""" + block

with io.open(STAGE3, "r", encoding="utf-8") as f:
    s3 = f.read()

old = """/-- 二阶一致界（statement，清单 §4，BoundBall 显式界化）：|K̂(x) − 1| ≤ 2x² + x⁴ 对 |x| ≤ δ0。
    K̂(0)=1（Core Khat_zero）；K̂″(0)≈−3.06（数值件 F）⟹ ½|K̂″(0)|≈1.53<2；
    O((au)⁴) 具体化为 (au)⁴。Taylor 数值分析件（K̂ 的 C² 界）——挂 axiom 待击破。
    注：原 ∀ a u 全局式 ⟺ ∀ x（取 a=1, u=x 覆盖 ℝ）；δ0 球域是核宽 x=a·u 的支撑带用法。 -/
axiom khat_second_order_bound (δ0 : ℝ) (hδ0 : 0 < δ0) :
  BoundBall 1 δ0 (fun x => |Khat x - 1|) (fun x => (2 : ℝ) * x ^ 2 + x ^ 4)"""

assert old in s3, "axiom 块未找到"
s3 = s3.replace(old, new_block)

with io.open(STAGE3, "w", encoding="utf-8", newline="\n") as f:
    f.write(s3)

print("migrated ok; new block chars =", len(new_block))
