# -*- coding: utf-8 -*-
"""调试：查找含(iv)标记/数值的段落"""
from docx import Document
import sys

p = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\_edit_bsd1.docx"
doc = Document(p)
print("PARA_COUNT:", len(doc.paragraphs))
for idx, para in enumerate(doc.paragraphs):
    t = para.text
    if "5.354" in t or "E⁵" in t:
        print("---", idx, "LEN", len(t))
        print(repr(t[:120]))
        break
# 也打印所有含'iv'的（宽松）
for idx, para in enumerate(doc.paragraphs):
    t = para.text
    if "代数秩" in t and "扭" in t:
        print("HIT2:", idx, repr(t[:100]))
