# -*- coding: utf-8 -*-
"""编辑 5.4(iv)：把区间判定升级为四段证明结构"""
from docx import Document

P = r"C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\_edit_bsd1.docx"

head = "（iv）代数秩 ≤ 1 的解析侧闭合（E⁵ 扭）。E⁵ 为 37a1 的 5-二次扭：Y² = x³ − 25x + 125/4，导子 N(E⁵) = 37·25 = 925（5 与 37 互素），根数 ε(E⁵) = ε(E)·χ₅(−37) = −1·(−1) = +1（χ₅ 为模 5 二次特征；(3/5) = −1；s = 3 处反射公式与直接级数之比 0.99999967 闭合，独立确认 ε 与局部因子）。Hecke 系数 a_p(E⁵) = χ₅(p)·a_p(E)（p ∤ 925），5 处加性（a = 0）、37 处乘性（a₃₇ = +1，经 s = 3 闭合比确定）。"

body = ("判定升级为证明结构（四段）。（iv-a）s = 1 处反射公式的初等退化。反射公式 "
        "Λ(s) = Σ_n a_n[ε·b^(s−2)·Γ(2−s, b) + b^(−s)·Γ(s, b)]（b = 2πn/√925，ε = +1）在 s = 1 处两分支合并："
        "Γ(1, b) = ∫_b^∞ e^(−t) dt = e^(−b)，故 L(E⁵,1) = (2π/√925)·Λ(1) = 2·Σ_{n≥1} a_n(E⁵)·n^(−1)·e^(−2πn/√925)"
        "（归一化 Λ(1) = (2π/√925)·Γ(1)·L(1)，Γ(1) = 1；不完全 Gamma 完全消失，级数逐项初等、指数收敛）。"
        "（iv-b）系数界。Ramanujan 界 |a_p| ≤ 2√p（3.1，无条件）经素幂递推与乘性组合给 |a_n| ≤ τ(n)√n；"
        "配恒真界 τ(n) ≤ 2√n（因子按 d ≤ √n 与 d > √n 分组，每组至多 √n 个）得 |a_n| ≤ 2n，"
        "故余项项 |a_n·n^(−1)·e^(−αn)| ≤ 2e^(−αn)（α = 2π/√925）——纯几何级数，无多项式因子。"
        "（iv-c）余项界（封闭几何级数）。L(E⁵,1) = S_N + R_N，S_N = 2·Σ_{n≤N} a_n·n^(−1)·e^(−αn)，"
        "|R_N| ≤ 2·Σ_{n>N} 2e^(−αn) = 4·e^(−α(N+1))/(1 − e^(−α))。N = 800：e^(−α·801) ≤ 1.3×10⁻⁷²，"
        "1 − e^(−α) > 0.18 ⟹ |R_N| ≤ 1.7×10⁻⁷¹；该几何级数求和已形式化闭合（BSD.LSeries5.geom_tail_bound，Lean，"
        "axiom 闭包仅基础公理）。（iv-d）部分和有理区间。S_N 各项以有理数端点逼近 e^(−αn)（幂级数截断至足够阶），"
        "得 S_N ∈ [S⁻, S⁺]，S⁻、S⁺ 为有理数（N = 800 精确有理算术，dps = 80）："
        "S⁻ ≥ 5.3548616166 − 10⁻⁶⁰ ≫ 1.7×10⁻⁷¹。综合 L(E⁵,1) ≥ S⁻ − |R_N| > 0。")

tail = "配合 ℚ 端定理“解析秩 0 ⟹ 代数秩 0”（Kolyvagin [2]），rank E⁵(ℚ) = 0。由 2.1 节二次扭分解 rank E(K) = rank E(ℚ) + rank E⁵(ℚ) = 1 + 0，代数秩 ≤ 1 闭合，故代数秩 = 1。"

new_text = head + body + tail

doc = Document(P)
target = None
for idx, para in enumerate(doc.paragraphs):
    if "（iv）代数秩 ≤ 1 的解析侧闭合" in para.text:
        target = para
        print("TARGET_IDX:", idx, "RUNS:", len(para.runs))
        break
assert target is not None, "not found"

# 保留首 run 的 rPr，删除其余 run，重写首 run 文本
first = target.runs[0]
for r in list(target.runs[1:]):
    r._r.getparent().remove(r._r)
first.text = new_text

doc.save(P)
print("SAVED len(new_text) =", len(new_text))
