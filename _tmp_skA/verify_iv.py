# -*- coding: utf-8 -*-
"""回读验证(iv)段"""
from docx import Document

P = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\_edit_bsd1.docx"
doc = Document(P)
for idx, para in enumerate(doc.paragraphs):
    t = para.text
    if "（iv）代数秩 ≤ 1 的解析侧闭合" in t:
        print("IDX:", idx)
        print(t)
        print("---CHECK---")
        for probe in ["（iv-a）", "Γ(1, b) = ∫_b^∞ e^(−t) dt = e^(−b)",
                      "L(E⁵,1) = 2·Σ_{n≥1} a_n(E⁵)·n^(−1)·e^(−2πn/√925)",
                      "τ(n) ≤ 2√n", "|a_n| ≤ 2n",
                      "4·e^(−α(N+1))/(1 − e^(−α))", "geom_tail_bound",
                      "S⁻ ≥ 5.3548616166 − 10⁻⁶⁰",
                      "（iv-d）", "rank E⁵(ℚ) = 0。由 2.1 节二次扭分解"]:
            print("HAS", probe, ":", probe in t)
        break
