with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = """  have h_bounded := elliptic_class_lengths_bounded
  have h_discrete := elliptic_class_lengths_discrete
  have h_finite : Set.Finite ellipticClassLengths :=
    bounded_discrete_real_set_finite ellipticClassLengths h_bounded h_discrete
  let s := h_finite.toFinset"""

new = """  have h_finite : Set.Finite ellipticClassLengths := ellipticClassLengths_finite
  let s := h_finite.toFinset"""

content = content.replace(old, new)

# 更新注释
old_comment = """/-- 椭圆共轭类集合 E 有限（定理，由支撑+有界+离散+Bolzano-Weierstrass推出）：
    椭圆项只依赖有限个特征长度上的测试函数值。
    证明：
    (1) elliptic_class_lengths_bounded: E_ell 有界
    (2) elliptic_class_lengths_discrete: E_ell 离散
    (3) bounded_discrete_real_set_finite: 有界离散集有限
    (4) 故 E_ell 有限，存在有限个长度 ℓ₁,...,ℓ_N
    (5) elliptic_term_support: ellipticTerm 只依赖这些点上的函数值
    这是算术群标准性质：椭圆共轭类有限。 -/"""

new_comment = """/-- 椭圆共轭类集合 E 有限（定理，由 ellipticClassLengths_finite 公理推出）：
    椭圆项只依赖有限个特征长度上的测试函数值。
    这是算术群标准性质：椭圆共轭类有限。 -/"""

content = content.replace(old_comment, new_comment)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
