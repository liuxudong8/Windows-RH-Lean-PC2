# -*- coding: utf-8 -*-
"""攻防 XLI 修订 v4：插入"窄核口径"说明段（防自欺欺人质询 + a→0 平凡化防线）。
位置：§3 "如图 1 所示，读数…" 段之后（中英各一段，格式继承前段）。"""
import copy, shutil
from docx import Document
from docx.oxml.ns import qn
from docx.text.paragraph import Paragraph

ZH = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"
EN = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\en\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证-EN.docx"
WORK = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work"

shutil.copy(ZH, WORK + r"\SOURCE_XLI_ZH.v3.docx")
shutil.copy(EN, WORK + r"\SOURCE_XLI_EN.v3.docx")
print("v3 snapshots saved")

def insert_para_after(para, text):
    """复制 para 的段落属性（pPr）新建段落，插在其后，格式完全继承。"""
    new_el = copy.deepcopy(para._p)
    for r in list(new_el.findall(qn('w:r'))):
        new_el.remove(r)
    for h in list(new_el.findall(qn('w:hyperlink'))):
        new_el.remove(h)
    para._p.addnext(new_el)
    np = Paragraph(new_el, para._parent)
    np.add_run(text)
    return np

def find_para(doc, anchor):
    for p in doc.paragraphs:
        if anchor in p.text:
            return p
    return None

# ---------------- 中文版：在读数段后插"窄核口径"段 ----------------
doc = Document(ZH)
zh_anchor = "如图 1 所示，读数：(i) 最优核在最近邻尺度"
p = find_para(doc, zh_anchor)
assert p is not None, "zh anchor not found"
zh_new = ("窄核口径说明（防\u201c窄核自欺欺人\u201d质询）：(i) 紧支撑 Fejér 核（fejer_a0.5）是有意选择——"
          "单族配对和 ΣK(z−s)² 只累积谱窗内的近程贡献，长程结构（远距聚集、跨族交织）根本不进入配对和，"
          "从而避免长程项污染 A 的读数；这不是省略求和而是核族选择：Prop 2.1 对任意 η（η∈L²、supp η⊂(−λ,λ)、"
          "η²^(0)=1、K=η²^）无条件成立，前提只需存在一个核使 A≤1.125（定理 (H1)(H2) 已取存在性形态）——"
          "窄核满足，完全合法，并非自欺欺人。(ii) 防 a→0 平凡化：a→0 的 A→1 极限对应谱支撑 λ→∞"
          "（核时域宽度与谱支撑满足测不准关系），超出无条件框架 λ≤1/2 的允许变分；拟随机放宽同样要求 λ 有限——"
          "故\u201cA 可任意接近 1\u201d不在变分范围内，fejer_a0.5 是允许范围内的扫描最优点（表 1 的 a0.5 族内最小）。"
          "(iii) A→1 亦非 free lunch：A≥1 恒成立（对角项 K(0)=1），A→1 只在非对角配对完全可忽略时可达——"
          "结构性重零点（其配对项 K(0)=1 不随核尺度消失）或强长程聚集会阻止 A→1；实测 1.0079/1.0114 因此是"
          "有信息量的读数，而非核取窄的人为压低。")
insert_para_after(p, zh_new)
doc.save(ZH)
print("[zh] narrow-kernel paragraph inserted")

# ---------------- 英文版：同位置插对应段 ----------------
doc = Document(EN)
en_anchor = "As shown in Fig. 1, readings: (i) The optimal kernel sits"
p = find_para(doc, en_anchor)
assert p is not None, "en anchor not found"
en_new = ("Narrow-kernel convention (against the \u201cnarrow-kernel self-deception\u201d objection): "
          "(i) The compactly supported Fejér kernel (fejer_a0.5) is a deliberate choice — the single-family "
          "pair sum ΣK(z−s)² accumulates only near-range contributions within the spectral window, so long-range "
          "structure (distant clustering, cross-family interleaving) never enters the pair sum and cannot contaminate "
          "the reading of A; this is kernel selection, not omission of terms: Proposition 2.1 holds unconditionally "
          "for every η (η∈L², supp η⊂(−λ,λ), η²^(0)=1, K=η²^), and the premise requires only the existence of one "
          "kernel with A≤1.125 (the theorem\u2019s (H1)–(H2) are already in existential form) — the narrow kernel "
          "satisfies it, fully legitimate. (ii) Against the trivialization a→0: the A→1 limit as a→0 corresponds to "
          "spectral support λ→∞ (uncertainty relation between kernel width and spectral support), outside the allowed "
          "variation of the unconditional framework λ≤1/2; the pseudorandom relaxation likewise requires λ finite — "
          "so \u201cA arbitrarily close to 1\u201d lies outside the variational range, and fejer_a0.5 is the scanning "
          "optimum within the allowed range (minimal in the a0.5 family of Table 1). (iii) A→1 is not a free lunch "
          "either: A≥1 always (diagonal term K(0)=1), and A→1 is reachable only when off-diagonal pairings are "
          "completely negligible — structural multiple zeros (whose pair terms K(0)=1 do not vanish as the kernel "
          "narrows) or strong long-range clustering would keep A well above 1; the measured 1.0079/1.0114 are "
          "therefore informative readings, not an artifact of a deliberately narrow kernel.")
insert_para_after(p, en_new)
doc.save(EN)
print("[en] narrow-kernel paragraph inserted")
