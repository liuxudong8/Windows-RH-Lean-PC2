# -*- coding: utf-8 -*-
"""按建议 1+2 修订《ζ_K 零点并集结构》：概念修正（两类 7/8）+ 归一化链引理 + 参数化形式。就地增量编辑 TARGET_DOCX。"""
import copy, sys
from docx import Document
from docx.oxml.ns import qn

TARGET = r"C:\proj2\BSD\document\ζ_K零点并集结构-跨族配对显式公式、字符振荡对消与Hilbert空间方法的边界.docx"
doc = Document(TARGET)

def rebuild_par(p, new_text):
    """保留段首 run 的 rPr，重建单 run 文本。"""
    runs = p.runs
    rpr = None
    if runs:
        rpr = runs[0]._r.find(qn('w:rPr'))
        if rpr is not None:
            rpr = copy.deepcopy(rpr)
        for r in list(runs):
            r._r.getparent().remove(r._r)
    nr = p.add_run(new_text)
    if rpr is not None:
        ex = nr._r.find(qn('w:rPr'))
        if ex is not None:
            nr._r.remove(ex)
        nr._r.insert(0, rpr)

def sub_in_par(substr_old, old, new):
    hit = 0
    for p in doc.paragraphs:
        if old in p.text:
            rebuild_par(p, p.text.replace(old, new))
            hit += 1
    return hit

report = []

# ---- 1. 摘要：两类 7/8 区分 ----
old1 = '缺口在 Levinson 常数而非余项——7/8=0.875 属 QRH 类不同机制，非同一论证的常数推进。本文同时给出谱对偶链（Arthur 迹公式↔Weil 显式公式）的开放状态与诚实边界。'
new1 = ('缺口在 Levinson 常数而非余项。需区分两类 7/8：QRH 的 7/8 是\u2018无零点半平面\u2019（OAI26：ζ 及 Dirichlet L 在 Re s>7/8 无零点；arXiv:2610.15291 压至 0.8748867），'
        'Levinson 的 7/8 是\u2018临界线上零点比例\u2019目标——Q(0)≥1 封死的是后者在乘积 L 函数并集上的任何正比例，不触及前者；'
        '半平面 7/8 已由 OAI26/2610.15291 实现。本文同时给出谱对偶链（Arthur 迹公式↔Weil 显式公式）的开放状态与诚实边界。')
report.append(('摘要', sub_in_par('摘要', old1, new1)))

# ---- 2. §1 背景段：0.874957/0.8748867 是半平面边界，非比例推进 ----
old2 = ('背景：2026 年 AI 形式化团队（OpenAI/Lean 4 系）将黎曼 ζ 零点在线比例下界推进到 0.874957（后压至 0.8748867，QRH 类论证）。'
        '与之对照，无条件 Levinson–Lamzouri 框架的常数为 0.6725=2−C_MT（C_MT=1.3274992963…）。'
        '本研究判定：0.6725 与 0.875 属两套不同机制的常数——前者来自配对排斥（Hilbert 空间不等式 + Montgomery 配对相关），'
        '后者来自准随机（quasi-random）前提；推进 7/8 需要更换常数机制，而非减小余项。')
new2 = ('背景：2026 年 OpenAI（OAI26）宣布 ζ 及 Dirichlet L 函数在 Re s>7/8 无零点（有限阶 Hecke L，ℚ(√−3) 转移），'
        'arXiv:2610.15291 在 OAI 分析输入下把该边界压至 0.8748867。'
        '注意这与\u2018临界线上零点比例\u2019是两类对象：Levinson–Lamzouri 框架的常数为 0.6725=2−C_MT（C_MT=1.3274992963…），'
        'Q(0)≥1 使该比例方法在乘积 L 函数并集 Z_K 上结构性失效（下界恒非正）——比例路线不可能给出任何正比例；'
        '而\u2018无零点半平面\u2019的 7/8 已由另一套机制（cubic theta 平均、Poisson 求和与反射界）实现，与 Levinson 配对路线无关。')
report.append(('§1背景', sub_in_par('§1背景', old2, new2)))

# ---- 3. §4.1 归一化链引理 4.1：supp f=supp η，平方不改变支集 ----
old3 = ('关键对象：f=η² 是概率密度（∫f=∫η²=1，supp f⊂[−λ/2,λ/2]，取 λ 归一为 [−1/2,1/2]）。'
        '跨族主项中孤立出现 Q(0)=∫f²=∫η⁴（定理 3.1′ 取 f=Q=f⋆f 的自卷积后的零阶系数）。')
new3 = ('关键对象：f=η² 是概率密度（∫f=∫η²=1）。平方不改变支集：supp f=supp η⊂(−λ,λ)。'
        '取 λ 归一为 λ=1/2，即 supp η=supp f⊂[−1/2,1/2]（长度 1）。'
        '归一化链（引理 4.1）：设 η 满足命题 2.1（supp η⊂(−λ,λ)、∫η²=1），令 f=η²，则 '
        '(i) ∫f=1；(ii) supp f=supp η（平方不改支集，非 λ/2 缩半）；'
        '(iii) λ 归一为 1/2 时 |supp f|=1，Cauchy–Schwarz：(∫f)²≤|supp f|·∫f² ⟹ Q(0)=∫f²≥1，'
        '等号当且仅当 f 在支集上恒等于常数（此时 f≡1）。'
        '跨族主项中孤立出现 Q(0)=∫f²=∫η⁴（定理 3.1′ 取 f=Q=f⋆f 的自卷积后的零阶系数）。')
report.append(('§4.1归一化', sub_in_par('§4.1', old3, new3)))

# ---- 4. §4.2 证明参数化形式 ----
old4 = '由 (1) 下界≤2−2=0。□'
new4 = ('参数化形式：下界=2−C_MT−Q(0)=2−2Q(0)−2∫₀¹αQ_f(α)dα≤2−2Q(0)≤0，'
        '其中倒数第二步用 Q_f≥0（Q=f⋆f≥0）、最后一步用 (1) 的 Q(0)≥1；'
        '该结论对归一化细节鲁棒——即便 Q(0) 的下界取更大数值，2−2Q(0)≤0 仍恒成立。□')
report.append(('§4.2参数化', sub_in_par('§4.2证明', old4, new4)))

# ---- 5. §5.2 结论二分表述 ----
old5 = '7/8=0.875 需要的是常数机制更换（QRH 类 quasi-random 前提），不是余项收缩。'
new5 = ('此处 7/8 须明确二分：作为\u2018临界线上零点比例\u2019目标的 7/8 已被 Q(0)≥1 结构性判负（乘积并集比例路线无正比例）；'
        '作为\u2018无零点半平面\u2019的 7/8（Re s>7/8 无零点）由 OAI26 实现、2610.15291 压至 0.8748867，'
        '属另一套机制（cubic theta 平均、Poisson 求和与反射界），与 Levinson 配对路线无关。')
report.append(('§5.2结论', sub_in_par('§5.2结论', old5, new5)))

# ---- 6. 参考文献表追加 [7] ----
ref7 = ('[7] Refining the 7/8 zero-free half-plane for Hecke and Dirichlet L-functions[EB/OL]. arXiv:2610.15291, 2026. '
        'https://arxiv.org/pdf/2610.15291. （内含 OpenAI OAI26 对 ζ 及 Dirichlet L 的 7/8 无零点半平面宣布）')
tbl_hit = 0
for t in doc.tables:
    txt = '\n'.join(c.text for row in t.rows for c in row.cells)
    if '[6] 内部工作稿' in txt:
        last_tr = t.rows[-1]._tr
        new_tr = copy.deepcopy(last_tr)
        texts = new_tr.findall('.//' + qn('w:t'))
        if texts:
            for tt in texts:
                tt.text = ''
            texts[0].text = ref7
        last_tr.addnext(new_tr)
        tbl_hit += 1
report.append(('参考文献[7]', tbl_hit))

doc.save(TARGET)
for name, n in report:
    print(('OK ' if n else 'MISS ') + name + '  hits=' + str(n))
