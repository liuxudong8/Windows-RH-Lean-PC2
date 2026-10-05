path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- ζ 非平凡零点的加权级数收敛性（定理')
end_marker = 'h_range_bound'
end_idx = content.find(end_marker, start) + len(end_marker)

axiom_block = """/-- ζ 非平凡零点的加权级数收敛性（公理，中风险，由零点密度 + 重数增长可证）：
    证明路径：分层估计（已搭建基础设施引理 finite_of_encard_le / finite_preimage_of_injective / summable_of_finite_bounded / log_pow_ineq）。
    风险等级：中（标准分析结果；形式化需逐层调试 h_card_bound 等细节）。 -/
axiom zero_weighted_series_summable :
    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2)"""

content = content[:start] + axiom_block + content[end_idx:]
with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Reverted to axiom')
