# -*- coding: utf-8 -*-
"""修复图题位置：图题须位于图片段之后（图下方），增量修正 TARGET_DOCX"""
import sys
from docx import Document
from docx.oxml.ns import qn

TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"

doc = Document(TARGET)

cap_par = None
pic_par = None
for p in doc.paragraphs:
    if p.text.startswith("图 1"):
        cap_par = p
    # 图片段：无正文文本但含 drawing 锚点
    if p._p.find(".//" + qn("w:drawing")) is not None:
        pic_par = p

if cap_par is None or pic_par is None:
    print("ERR: 未定位图段/图题段")
    sys.exit(1)

before = pic_par._p.getprevious()
print("pic.prev is cap:", before is cap_par._p)
print("cap text:", cap_par.text[:20])

if before is cap_par._p:
    # 图题在图片之前 → 移到图片之后
    pic_par._p.addnext(cap_par._p)
    print("FIXED: cap moved after pic")
else:
    print("OK: cap already after pic")

doc.save(TARGET)
print("SAVED")
