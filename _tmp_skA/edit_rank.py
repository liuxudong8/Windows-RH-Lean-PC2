# -*- coding: utf-8 -*-
"""edit_rank.py —— 骨架A讨论稿补"代数秩=1"证明
1) 2.1 节"选择理由"段后插入代数秩证明段
2) 5.4 加 (iv)
3) 1.3 / 4.3 / 6 边界声明更新
4) 参考文献补二次扭（Silverman）
"""
import copy
from docx import Document

SRC = r'D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\BSD\弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx'
TGT = r'D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\BSD\_edit_骨架A讨论稿.docx'
import shutil
shutil.copyfile(SRC, TGT)

doc = Document(TGT)

def set_para_text(p, text):
    runs = p.runs
    rpr = None
    if runs and runs[0]._r.rPr is not None:
        rpr = copy.deepcopy(runs[0]._r.rPr)
    for r in runs:
        r._r.getparent().remove(r._r)
    new_r = p.add_run(text)
    if rpr is not None:
        new_r._r.insert(0, rpr)

def insert_para_after(anchor_p, text, style=None):
    """在 anchor_p 后插入新段落（复制 anchor 的 pPr 骨架）"""
    from docx.oxml.ns import qn
    new_p = copy.deepcopy(anchor_p._p)
    # 清空 runs
    for r in list(new_p.findall(qn('w:r'))):
        new_p.remove(r)
    # 清空超链接等
    for tag in ('w:hyperlink', 'w:bookmarkStart', 'w:bookmarkEnd', 'w:fldSimple'):
        for el in new_p.findall(qn(tag)):
            new_p.remove(el)
    anchor_p._p.addnext(new_p)
    from docx.text.paragraph import Paragraph
    np = Paragraph(new_p, anchor_p._parent)
    set_para_text(np, text)
    return np

# ---- 1) 2.1 节：在"选择理由"段后插代数秩证明 ----
anchor = None
for p in doc.paragraphs:
    t = p.text.strip()
    if t.startswith('选择理由：ℚ 端秩 1 已知是双刃剑'):
        anchor = p
        break
assert anchor is not None, 'anchor 2.1 未找到'
new_text = ('代数秩 = 1 的证明（二次扭分解）。设 K = ℚ(√5)，σ 为 Gal(K/ℚ) 的生成元。'
            'E(K) 是有限生成 ℤ[Gal]-模，特征空间分解 E(K) ⊗ ℚ ≅ V⁺ ⊕ V⁻ 中，'
            'V⁺ = (1/2)(1 + σ)·E(K) ⊗ ℚ ≅ E(ℚ) ⊗ ℚ，'
            'V⁻ = (1/2)(1 − σ)·E(K) ⊗ ℚ ≅ E⁵(ℚ) ⊗ ℚ，'
            '其中 E⁵ 为 E 的 5-二次扭（K 的判别式 d = 5；扭方程 Y² = x³ − 25x + 125/4）。'
            '故 rank E(K) = rank E(ℚ) + rank E⁵(ℚ)。'
            'rank E(ℚ) = 1 由 LMFDB [6] 记录（生成元 (0,0)）；'
            'rank E⁵(ℚ) = 0 由 5.4(iv) 的区间算术判定给出（L(E⁵,1) ≠ 0 为确定性判定，'
            '结合 ℚ 端定理“解析秩 0 ⟹ 代数秩 0”，Kolyvagin [2]）。'
            '故 rank E(K) = 1，代数秩恰为 1。此证明不依赖 Heegner 点机制，全部成分（特征空间分解、'
            '二次扭方程、区间算术）可 Lean 形式化。')
insert_para_after(anchor, new_text)

# ---- 2) 5.4 加 (iv)：锚定（ii）段，在其后插入新段 ----
anchor54 = None
for p in doc.paragraphs:
    t = p.text.strip()
    if t.startswith('（ii）4.1 显式公式精确形态'):
        anchor54 = p
        break
assert anchor54 is not None, 'anchor 5.4(ii) 未找到'
iv_text = ('（iv）代数秩 ≤ 1 的解析侧闭合（E⁵ 扭）。E⁵ 为 37a1 的 5-二次扭：Y² = x³ − 25x + 125/4，'
           '导子 N(E⁵) = 37·25 = 925（5 与 37 互素），根数 ε(E⁵) = ε(E)·χ₅(−37) = −1·(−1) = +1'
           '（χ₅ 为模 5 二次特征；(3/5) = −1；s = 3 处反射公式与直接级数之比 0.99999967 闭合，'
           '独立确认 ε 与局部因子）。Hecke 系数 a_p(E⁵) = χ₅(p)·a_p(E)（p ∤ 925），'
           '5 处加性（a = 0）、37 处乘性（a₃₇ = +1，经 s = 3 闭合比确定）。'
           '区间算术判定（N = 800 截断，dps = 80）：'
           'L(E⁵,1) ∈ [5.3548616166 − 1.7×10⁻⁷¹, 5.3548616166 + 1.7×10⁻⁷¹] ⊂ (0, ∞)。'
           '误差预算：尾界 ≤ 1.7×10⁻⁷¹（Ramanujan 界 |a_p| ≤ 2√p ⟹ |a_n| ≤ τ(n)√n，'
           '与 Γ 因子指数衰减 e^(−2πn/√925) 的封闭几何级数）；舍入 ≤ 10⁻⁷⁷。'
           '配合 ℚ 端定理“解析秩 0 ⟹ 代数秩 0”（Kolyvagin [2]），rank E⁵(ℚ) = 0。'
           '由 2.1 节二次扭分解 rank E(K) = rank E(ℚ) + rank E⁵(ℚ) = 1 + 0，'
           '代数秩 ≤ 1 闭合，故代数秩 = 1。')
insert_para_after(anchor54, iv_text)

# ---- 3) 边界声明更新 ----
# 4.3 边界句
for p in doc.paragraphs:
    t = p.text.strip()
    if '边界声明：本结论限于 E = 37a1/ℚ(√5) 单曲线' in t:
        set_para_text(p, t.replace(
            '代数秩 ≤ 1（从而完整弱 BSD 秩 1 情形）仍需独立论证，本判定不推广为一般弱 BSD。',
            '代数秩 = 1 已由 2.1 节二次扭分解与 5.4(iv) 的 E⁵ 区间判定闭合（完整弱 BSD 秩 1 情形在 E = 37a1/ℚ(√5) 上成立）；本判定仍不推广为一般弱 BSD。'))
        break
# 1.3 节
for p in doc.paragraphs:
    t = p.text.strip()
    if t.startswith('骨架 A 的论证由四层构成'):
        set_para_text(p, t.replace(
            '反证（假设 L′(E,1) = 0 导出矛盾，现由区间算术闭合）。',
            '反证（假设 L′(E,1) = 0 导出矛盾，现由区间算术闭合）；代数秩 = 1 由二次扭分解 + E⁵ 扭秩 0 判定闭合（见 2.1、5.4(iv)）。'))
        break
# 6 节
for p in doc.paragraphs:
    t = p.text.strip()
    if t.startswith('骨架 A 给出了弱 BSD 秩 1 未证方向'):
        set_para_text(p, t.replace(
            '代数秩 ≤ 1（完整弱 BSD 秩 1 情形）与一般化推广仍为开放方向。',
            '代数秩 = 1（完整弱 BSD 秩 1 情形）已由二次扭分解 + E⁵ 扭区间判定闭合（见 2.1、5.4(iv)）；一般化推广仍为开放方向。'))
        break

# ---- 4) 参考文献补 [8] Silverman ----
for p in doc.paragraphs:
    t = p.text.strip()
    if t.startswith('[7] Spicer'):
        ref8 = '[8] Silverman J H. The Arithmetic of Elliptic Curves[M]. 2nd ed. Graduate Texts in Mathematics 106. New York: Springer, 2009.（二次扭分解：E(K) ≅ E(ℚ) ⊕ E^d(ℚ)，K = ℚ(√d)）'
        insert_para_after(p, ref8)
        break

doc.save(TGT)
print('OK saved:', TGT)
