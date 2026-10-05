f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 找到旧注释开始和 melinTransform 行
# 删除行1080-1085（旧注释），保留 melinTransform
new_lines = []
skip_old_comment = False
for i, line in enumerate(lines):
    if '/-- ζ 零点侧求和（抽象不透明常量）' in line:
        skip_old_comment = True
        continue
    if skip_old_comment:
        if 'opaque melinTransform' in line:
            skip_old_comment = False
            new_lines.append(line)
        continue
    new_lines.append(line)

# 在 nontrivialZeroSum 之后插入 trivialZeroContribution
final_lines = []
for i, line in enumerate(new_lines):
    final_lines.append(line)
    if 'opaque nontrivialZeroSum : TestFunction' in line:
        final_lines.append('\n')
        final_lines.append('/-- 平凡零点与极点贡献（opaque）：\n')
        final_lines.append('    T(f) = Σ_{k≥1} melinTransform f (-2k) + melinTransform f (1) · Res_{s=1}(zetaLogDerivative)。\n')
        final_lines.append('    这是 zetaZeroSide 的另一部分，包含平凡零点 s=-2,-4,... 和极点 s=1 的贡献。 -/\n')
        final_lines.append('opaque trivialZeroContribution : TestFunction → ℂ\n')

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(final_lines)
print('Done')
