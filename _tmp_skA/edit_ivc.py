# -*- coding: utf-8 -*-
"""补(iv-c)初等不等式链 + (iv-d)粗界口径"""
from docx import Document

SRC = r"D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\BSD\弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿1.docx"
TGT = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\_edit_bsd1b.docx"

import shutil
shutil.copyfile(SRC, TGT)

old1 = ("（iv-c）余项界（封闭几何级数）。L(E⁵,1) = S_N + R_N，S_N = 2·Σ_{n≤N} a_n·n^(−1)·e^(−αn)，"
        "|R_N| ≤ 2·Σ_{n>N} 2e^(−αn) = 4·e^(−α(N+1))/(1 − e^(−α))。N = 800：e^(−α·801) ≤ 1.3×10⁻⁷²，"
        "1 − e^(−α) > 0.18 ⟹ |R_N| ≤ 1.7×10⁻⁷¹；该几何级数求和已形式化闭合（BSD.LSeries5.geom_tail_bound，Lean，"
        "axiom 闭包仅基础公理）。")
new1 = ("（iv-c）余项界（封闭几何级数）。L(E⁵,1) = S_N + R_N，S_N = 2·Σ_{n≤N} a_n·n^(−1)·e^(−αn)，"
        "|R_N| ≤ 2·Σ_{n>N} 2e^(−αn) = 4·e^(−α(N+1))/(1 − e^(−α))。数值界为初等不等式链（全部可核验）："
        "α = 2π/√925 > 2·3.1415/30.414 > 0.2065（π > 3.1415；√925 < 30.414 ⟸ 30.414² = 925.011… > 925）；"
        "e^(−α) ≤ e^(−0.2065) = 1/e^(0.2065) < 1/(1 + 0.2065 + 0.2065²/2 + 0.2065³/6) = 1/1.22929… = 0.813481… < 0.8136"
        "（e^x ≥ 1 + x + x²/2 + x³/6，x ≥ 0），故 1 − e^(−α) > 0.1864 > 0.18；"
        "e^(−α·801) ≤ e^(−165.4065) < 1.5×10⁻⁷²（同法 e^x ≥ x^N/N! 取 N 充分大）。"
        "综合 |R_N| ≤ 4×1.5×10⁻⁷²/0.1864 < 3.3×10⁻⁷¹（保守粗界；Ramanujan 逐项精细口径 1.674×10⁻⁷¹，"
        "见 verify_E5_iii.py）。该几何级数求和已形式化闭合（BSD.LSeries5.geom_tail_bound，Lean，"
        "axiom 闭包仅基础公理）。")

old2 = "S⁻ ≥ 5.3548616166 − 10⁻⁶⁰ ≫ 1.7×10⁻⁷¹。"
new2 = "S⁻ ≥ 5.3548616166 − 10⁻⁶⁰ ≫ 3.3×10⁻⁷¹（|R_N| 粗界）。"

doc = Document(TGT)
target = None
for idx, para in enumerate(doc.paragraphs):
    if "（iv）代数秩 ≤ 1 的解析侧闭合" in para.text:
        target = para
        break
assert target is not None, "not found"
t = target.text
assert old1 in t, "old1 not found"
assert old2 in t, "old2 not found"
new_text = t.replace(old1, new1).replace(old2, new2)
target.runs[0].text = new_text
doc.save(TGT)
print("OK runs:", len(target.runs), "len:", len(new_text))
