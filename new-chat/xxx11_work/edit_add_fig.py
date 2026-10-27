# -*- coding: utf-8 -*-
"""攻防 XLI 增量编辑：备份 SOURCE_DOCX → 表 1 之后插入图 1（图片+图题+正文引用）→ 原地写回 TARGET_DOCX"""
import shutil, sys
from docx import Document
from docx.shared import Pt, Cm
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml.ns import qn

TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"
FIG = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work\fig1_A_scan.png"
BACKUP = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work\SOURCE_DOCX.bak.docx"

# 只读 baseline（禁止操作）
shutil.copy(TARGET, BACKUP)
print("BACKUP OK")

doc = Document(TARGET)

# 定位表 1 读数段（以"读数：(i)"开头）
target_par = None
for p in doc.paragraphs:
    if p.text.startswith("读数：(i)"):
        target_par = p
        break
if target_par is None:
    print("ERR: 读数段未找到")
    sys.exit(1)
print("ANCHOR:", target_par.text[:28])

# 正文引用：段首插入 "如图 1 所示，"
first_run = target_par.runs[0]
first_run.text = "如图 1 所示，" + first_run.text

# 图片段（末尾创建，随后移动到读数段之前）
pic_par = doc.add_paragraph()
pic_par.alignment = WD_ALIGN_PARAGRAPH.CENTER
pic_par.paragraph_format.space_before = Pt(6)
pic_par.paragraph_format.space_after = Pt(0)
pic_par.paragraph_format.line_spacing = 1.15
pic_par.paragraph_format.keep_with_next = True
pic_par.add_run().add_picture(FIG, width=Cm(13.5))

# 图题段（Caption：宋体 9pt 居中，置于图下）
cap = doc.add_paragraph()
cap.alignment = WD_ALIGN_PARAGRAPH.CENTER
cap.paragraph_format.space_before = Pt(2)
cap.paragraph_format.space_after = Pt(6)
cap.paragraph_format.line_spacing = 1.15
cap.paragraph_format.keep_with_next = True
r = cap.add_run("图 1　配对常数 A 的核族 × 尺度扫描（audit6）：单族低于 C_MT 与 7/8 门槛，并集直接论证判负")
r.font.name = "Times New Roman"
r._element.rPr.rFonts.set(qn("w:eastAsia"), "宋体")
r.font.size = Pt(9)

# 移动：cap 紧贴读数段前，pic 在 cap 前（顺序：表 1 → 图 1 → 图题 → 读数段）
target_par._p.addprevious(cap._p)
target_par._p.addprevious(pic_par._p)

doc.save(TARGET)
print("EDITED OK")
