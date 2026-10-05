# -*- coding: utf-8 -*-
"""探针：定位 (iv) 段落的 run 结构"""
from docx import Document
import sys

p = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\_edit_bsd1.docx"
doc = Document(p)
for idx, para in enumerate(doc.paragraphs):
    t = para.text
    if "（iv）代数秩 ≤ 1 的解析侧闭合" in t:
        print("PARA_IDX:", idx)
        print("LEN:", len(t))
        print("RUNS:", len(para.runs))
        for i, r in enumerate(para.runs):
            print(i, repr(r.text[:80]))
        break
