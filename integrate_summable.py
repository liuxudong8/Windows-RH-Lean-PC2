import re

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 读取测试文件中的引理和定理
with open(r'C:\proj2\test_full_summable9.lean', 'r', encoding='utf-8') as f:
    test_content = f.read()

# 提取 small_finite 引理
small_finite_start = test_content.find('lemma small_finite')
small_finite_end = test_content.find('lemma exists_layer_index')
small_finite_code = test_content[small_finite_start:small_finite_end].strip()

# 提取 exists_layer_index 引理
exists_start = test_content.find('lemma exists_layer_index')
exists_end = test_content.find('theorem zero_weighted_series_summable\'')
exists_code = test_content[exists_start:exists_end].strip()

# 提取 theorem 证明（从 theorem 到 #check）
theorem_start = test_content.find('theorem zero_weighted_series_summable\'')
theorem_end = test_content.find('#check zero_weighted_series_summable\'')
theorem_code = test_content[theorem_start:theorem_end].strip()
# 把 theorem 名称改回 zero_weighted_series_summable（去掉撇号）
theorem_code = theorem_code.replace("zero_weighted_series_summable'", "zero_weighted_series_summable")

# 构建要插入的内容（在 axiom 之前）
insert_code = f"""
-- === zero_weighted_series_summable 降级证明基础设施 ===

{small_finite_code}

{exists_code}

"""

# 找到 axiom 的位置并替换
old_axiom = """/-- ζ 非平凡零点的加权级数收敛性（公理，中风险）：
    已搭建基础设施（riemannZeta_conj / card_le_of_encard_le / lower_conj_eq_upper / finite_of_encard_le / finite_preimage_of_injective / summable_of_finite_bounded / log_pow_ineq）。
    剩余障碍：h_card_bound 显式证明 + h_point_bound 代数估计调试。 -/
axiom zero_weighted_series_summable :
    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2)"""

new_theorem = f"""{insert_code}
/-- ζ 非平凡零点的加权级数收敛性（定理，已降级）：
    分层估计 A_k = {{n : 2^k ≤ |Im(ρₙ)| < 2^(k+1)}}，每层贡献 O(k²/2^k)，∑ k²/2^k < ∞。
    依赖 zero_counting_estimate + zero_multiplicity_log_growth + layer_sum_bound + summable_quadratic_over_geometric。 -/
{theorem_code}"""

if old_axiom in content:
    content = content.replace(old_axiom, new_theorem)
    print("替换成功")
else:
    print("未找到 axiom，尝试模糊匹配")
    # 尝试只匹配 axiom 行
    old_axiom2 = "axiom zero_weighted_series_summable :\n    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2)"
    if old_axiom2 in content:
        content = content.replace(old_axiom2, new_theorem)
        print("替换成功（模糊匹配）")
    else:
        print("仍然未找到")

# 写入文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("文件已写入")
print(f"文件总行数: {len(content.splitlines())}")
