# -*- coding: utf-8 -*-
"""fix_font.py —— 为新插入段落的 run 显式设置 eastAsia=宋体 ascii=Times New Roman"""
from docx import Document
from docx.oxml.ns import qn
import copy

TGT = r'D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\BSD\_edit_骨架A讨论稿.docx'
doc = Document(TGT)

def fix_run(r):
    rPr = r._r.get_or_add_rPr()
    rFonts = rPr.find(qn('w:rFonts'))
    if rFonts is None:
        rFonts = rPr.makeelement(qn('w:rFonts'), {})
        rPr.insert(0, rFonts)
    for attr, val in (('w:ascii', 'Times New Roman'), ('w:hAnsi', 'Times New Roman'), ('w:eastAsia', '宋体'), ('w:cs', 'Times New Roman')):
        rFonts.set(qn(attr), val)
    # theme 属性清除
    for attr in ('w:asciiTheme', 'w:hAnsiTheme', 'w:eastAsiaTheme', 'w:cstheme'):
        if rFonts.get(qn(attr)) is not None:
            del rFonts.attrib[qn(attr)]

targets = ('代数秩 = 1 的证明', '（iv）代数秩 ≤ 1 的解析侧闭合', '[8] Silverman')
fixed = 0
for p in doc.paragraphs:
    t = p.text.strip()
    if any(t.startswith(x) for x in targets):
        for r in p.runs:
            fix_run(r)
        fixed += 1
print('fixed paragraphs:', fixed)
doc.save(TGT)
print('OK')
