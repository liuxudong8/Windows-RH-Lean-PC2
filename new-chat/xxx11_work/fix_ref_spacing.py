# -*- coding: utf-8 -*-
"""消除孤行页：压缩参考文献段间距（行距 1.05、段后 1pt），使 [8] 并入前页"""
import sys
from docx import Document
from docx.shared import Pt

TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"

doc = Document(TARGET)
changed = 0
for p in doc.paragraphs:
    if p.text.startswith("[") and p.text.strip().endswith("."):
        pf = p.paragraph_format
        pf.line_spacing = 1.05
        pf.space_after = Pt(1)
        changed += 1
print("refs adjusted:", changed)
doc.save(TARGET)
print("SAVED")
