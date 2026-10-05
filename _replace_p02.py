# -*- coding: utf-8 -*-
"""P0.2 第一步：退役 tsum 精确层（stage_4.lean :1803-:1984）。

替换 :1803-:1984 为退役说明注释块。:1801-:1802、:1985 空行保留。
"""
import io

SRC = r"C:\proj2\OrderPreservingBijection\stage_4.lean"
RETIRE = (
    "/--\n"
    "## P0.2 退役：tsum 精确层（2026-10-02）\n\n"
    "原 :1803-:1984 的六个定理（nontrivial_zero_sum_summable、\n"
    "nontrivialZeroSum_eq_tsum_all、nontrivialZeroSum_tsum_linear、\n"
    "tsum_two_point_isolation、nontrivialZeroSum_pair_localization、\n"
    "zero_side_melin_localization）已退役：\n\n"
    "- 它们是旧全枚举 ℕ 层（nontrivialZeroEnum 时代）的 tsum 精确化，\n"
    "  依赖 :49 枚举基础设施（S 无限/单射两缺口，mathlib 无）；\n"
    "- nontrivialZeroSum 已于 2026-10-01 重构为围道内 Finset + farZeroSubtype tsum，\n"
    "  本层在主链上零调用者（zero_side_melin_localization 无人消费）；\n"
    "- 两个 admit（nontrivial_zero_sum_summable、nontrivialZeroSum_eq_tsum_all）\n"
    "  随退役消除，不再进入 #print axioms。\n\n"
    "主链当前 summable 依赖是 farContribution_pair_diff_split（P0.2 待改造：\n"
    "加显式可和性前提 + M1(ρ)-M2(ρ)=1 前提后真证）。\n"
    "-/\n"
)

with io.open(SRC, "r", encoding="utf-8") as f:
    lines = f.readlines()

n = len(lines)
assert n > 1985, f"file too short: {n}"
# :1 对应索引 0；:1803 对应索引 1802；:1984 对应索引 1983
head = lines[:1802]   # 行 1..1802（含 spectral_sum_determined_by_points 及空行）
tail = lines[1984:]   # 行 1985..（空行 + melin_pair_sum_nondegenerate 起）

out = "".join(head) + RETIRE + "".join(tail)
with io.open(SRC, "w", encoding="utf-8", newline="") as f:
    f.write(out)

print("done: retired lines 1803-1984 ->", len(out.splitlines()), "lines total")
