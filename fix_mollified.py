import re

with open(r'C:\proj2\OrderPreservingBijection\MollifiedFunction.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 删除 elliptic_class_lengths_bounded 公理
content = re.sub(
    r'/-- 椭圆类特征长度有界（公理）.*?axiom elliptic_class_lengths_bounded.*?\n\n',
    '',
    content,
    flags=re.DOTALL
)

# 2. 删除 elliptic_class_lengths_discrete 公理
content = re.sub(
    r'/-- 椭圆类特征长度离散（公理）.*?axiom elliptic_class_lengths_discrete.*?\n\n',
    '',
    content,
    flags=re.DOTALL
)

# 3. 删除 bounded_discrete_real_set_finite 公理
content = re.sub(
    r'/-- 实数中有界离散子集有限.*?axiom bounded_discrete_real_set_finite.*?\n\n',
    '',
    content,
    flags=re.DOTALL
)

# 4. 把 ellipticClassLengths_finite 从 lemma 改为 axiom
old_lemma = """lemma ellipticClassLengths_finite : Set.Finite ellipticClassLengths :=
    bounded_discrete_real_set_finite ellipticClassLengths elliptic_class_lengths_bounded elliptic_class_lengths_discrete"""

new_axiom = """axiom ellipticClassLengths_finite : Set.Finite ellipticClassLengths"""

content = content.replace(old_lemma, new_axiom)

# 更新注释
old_comment = """/-- 椭圆类特征长度集合有限（引理，由有界+离散+Bolzano-Weierstrass推出）：
    ellipticClassLengths 是有限集。 -/"""

new_comment = """/-- 椭圆类特征长度集合有限（公理，数论事实）：
    ellipticClassLengths 是有限集。
    数学原因：算术群 Γ 中椭圆元素的阶有界，故旋转角只能取有限个值。
    注意：不能通过"有界+离散→有限"推出，反例 {1/n}。 -/"""

content = content.replace(old_comment, new_comment)

with open(r'C:\proj2\OrderPreservingBijection\MollifiedFunction.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
