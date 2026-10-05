import io

# 1) 从当前 LSeries5 恢复原骨架：行 0..299（1-300 行，含 'end'）+ 行 957（958 行 'end BSD.LSeries5'）
tgt = open(r'c:\proj2\BSD\LSeries5.lean', encoding='utf-8').read()
tlines = tgt.splitlines()
head = tlines[:300]              # 1-300 行
tail = tlines[957:]              # 958 行 'end BSD.LSeries5'（若存在）
assert tail and tail[0].strip() == 'end BSD.LSeries5', f'unexpected tail: {tail[:1]}'

# 2) 生成器产物：从 alpha_lt_2066 起到 part50_ge（含 exp_neg_alpha_gt_8133 / alphaE5 / fE5 / axioms / powE / terms / crude / part）
src = open(r'c:\proj2\BSD\_test_ivd50.lean', encoding='utf-8').read()
slines = src.splitlines()
start = next(i for i, l in enumerate(slines) if l.strip().startswith('theorem alpha_lt_2066'))
body = 'noncomputable section\n' + '\n'.join(slines[start:]) + '\nend\n'

# 3) import 补丁：aE5_table（LSeries5 原 import 无 BSD.aE5_table）
head2 = []
for l in head:
    if l.strip() == 'import OrderPreservingBijection.QuadraticFieldFive':
        head2.append('import BSD.aE5_table')
    head2.append(l)

out = '\n'.join(head2 + [body] + tail)
open(r'c:\proj2\BSD\LSeries5.lean', 'w', encoding='utf-8').write(out)
print('OK rebuilt; head lines:', len(head2), 'body lines:', len(body.splitlines()))
