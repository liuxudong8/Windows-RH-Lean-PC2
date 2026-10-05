# -*- coding: utf-8 -*-
"""修复 gen_skA.py：ASCII 引号→中文引号；tcPr 顺序（shd 在 vAlign 前）"""
import io

P = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\gen_skA.py"
with io.open(P, 'r', encoding='utf-8') as f:
    src = f.read()

pairs = [
    ('因此，"解析秩 ≤ 1 ⟹ 代数秩 = 解析秩"是定理',
     '因此，“解析秩 ≤ 1 ⟹ 代数秩 = 解析秩”是定理'),
    ('"谱点集 = 零点虚部集"',
     '“谱点集 = 零点虚部集”'),
    ('保证"代数秩 ≥ 1"这一未证方向',
     '保证“代数秩 ≥ 1”这一未证方向'),
    ('显式公式的"素数项与轨道项"的接口',
     '显式公式的“素数项与轨道项”的接口'),
    ('显式公式的"形式"上',
     '显式公式的“形式”上'),
    ('"全消条件确实违反 Ramanujan 界与计数"',
     '“全消条件确实违反 Ramanujan 界与计数”'),
    ('"上一个量级"',
     '“上一个量级”'),
    ('表内"?"为待补项',
     '表内“?”为待补项'),
]
for old, new in pairs:
    if old not in src:
        print('MISS:', old)
    src = src.replace(old, new)

# tcPr 顺序：表头行先 append shd 再设置 vertical_alignment
old_block = """    c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'), 'clear'); shd.set(qn('w:fill'), 'D9D9D9')
    c._tc.get_or_add_tcPr().append(shd)"""
new_block = """    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'), 'clear'); shd.set(qn('w:fill'), 'D9D9D9')
    c._tc.get_or_add_tcPr().append(shd)
    c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER"""
if old_block not in src:
    print('MISS: tcPr block')
else:
    src = src.replace(old_block, new_block)

with io.open(P, 'w', encoding='utf-8') as f:
    f.write(src)
print('DONE')
