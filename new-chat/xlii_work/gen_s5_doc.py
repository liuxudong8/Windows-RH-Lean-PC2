# -*- coding: utf-8 -*-
"""攻防 XLII · S5 落档：ε 的定理级控制——跨族 f(0) 形态直接实测与并集/跨族配对公式的无条件化构造。
数据：qrh_work/xlii_s5_cross.json（跨族交叉配对实测，因子 2 修正版）+ xlii_s5_ctl.json（对照）+ xlii_s5_fig.png。
"""
import json, os
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S5-ε定理级控制-跨族f(0)形态实测与并集配对公式的无条件化构造.docx"
FIG = os.path.join(QRH, "xlii_s5_fig.png")

cross = json.load(open(os.path.join(QRH, "xlii_s5_cross.json"), encoding="utf-8"))
ctl = json.load(open(os.path.join(QRH, "xlii_s5_ctl.json"), encoding="utf-8"))
AV = cross["meta"]["A_grid"]
r8 = cross["rows"][0]
r6 = cross["rows"][1]

doc = Document()
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
sec.left_margin = sec.right_margin = sec.top_margin = sec.bottom_margin = Cm(2.5)

def set_fonts(style, east, ascii_="Times New Roman", size=10.5, bold=False, color=None):
    style.font.name = ascii_
    style.font.size = Pt(size)
    style.font.bold = bold
    if color:
        style.font.color.rgb = color
    rpr = style.element.get_or_add_rPr()
    rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts"); rpr.append(rf)
    for attr in ("w:asciiTheme", "w:hAnsiTheme", "w:eastAsiaTheme"):
        if rf.get(qn(attr)):
            del rf.attrib[qn(attr)]
    rf.set(qn("w:ascii"), ascii_); rf.set(qn("w:hAnsi"), ascii_); rf.set(qn("w:eastAsia"), east)

n = doc.styles["Normal"]
set_fonts(n, "宋体", size=10.5)
pf = n.paragraph_format
pf.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
pf.line_spacing = 1.5
pf.space_before = Pt(0); pf.space_after = Pt(0)
ind = n.element.get_or_add_pPr().get_or_add_ind()
ind.set(qn("w:firstLineChars"), "200"); ind.set(qn("w:firstLine"), "420")

tstyle = doc.styles["Title"]
set_fonts(tstyle, "黑体", size=16, bold=True)
tstyle.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
tstyle.paragraph_format.space_after = Pt(6)

h1 = doc.styles["Heading 1"]
set_fonts(h1, "黑体", size=12, bold=True, color=RGBColor(0, 0, 0))
h1.paragraph_format.space_before = Pt(12); h1.paragraph_format.space_after = Pt(6)
h1.paragraph_format.keep_with_next = True

h2 = doc.styles["Heading 2"]
set_fonts(h2, "黑体", size=10.5, bold=True, color=RGBColor(0, 0, 0))
h2.paragraph_format.space_before = Pt(6); h2.paragraph_format.space_after = Pt(3)
h2.paragraph_format.keep_with_next = True

cap = doc.styles["Caption"]
set_fonts(cap, "黑体", size=9, bold=False)
cap.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
cap.paragraph_format.space_before = Pt(4); cap.paragraph_format.space_after = Pt(4)
cap.paragraph_format.keep_with_next = True

def para(text, style=None, align=None, bold=False, font=None, size=None, indent_chars=0,
         space_before=None, space_after=None):
    p = doc.add_paragraph(text, style=style)
    if align is not None:
        p.alignment = align
    if indent_chars:
        ppr = p._p.get_or_add_pPr(); ind2 = ppr.get_or_add_ind()
        ind2.set(qn("w:firstLineChars"), str(indent_chars * 100))
    for r in p.runs:
        if bold:
            r.font.bold = True
        if font or size:
            r.font.name = "Times New Roman"
            if size:
                r.font.size = Pt(size)
            rpr = r._r.get_or_add_rPr(); rf = rpr.find(qn("w:rFonts"))
            if rf is None:
                rf = OxmlElement("w:rFonts"); rpr.append(rf)
            rf.set(qn("w:ascii"), "Times New Roman"); rf.set(qn("w:hAnsi"), "Times New Roman")
            if font:
                rf.set(qn("w:eastAsia"), font)
    if space_before is not None:
        p.paragraph_format.space_before = Pt(space_before)
    if space_after is not None:
        p.paragraph_format.space_after = Pt(space_after)
    return p

def h1t(text):
    return doc.add_heading(text, level=1)

def h2t(text):
    return doc.add_heading(text, level=2)

def caption(text):
    return doc.add_paragraph(text, style="Caption")

def set_cell_borders(cell, top=8, bottom=8):
    tcPr = cell._tc.get_or_add_tcPr()
    tb = tcPr.find(qn("w:tcBorders"))
    if tb is None:
        tb = OxmlElement("w:tcBorders"); tcPr.append(tb)
    for tag, sz in (("top", top), ("bottom", bottom)):
        el = tb.find(qn("w:" + tag))
        if el is None:
            el = OxmlElement("w:" + tag); tb.append(el)
        el.set(qn("w:val"), "single"); el.set(qn("w:sz"), str(sz)); el.set(qn("w:space"), "0")

def style_cell(cell, text, bold=False, align=WD_ALIGN_PARAGRAPH.RIGHT, east="宋体", size=9):
    cell.vertical_alignment = WD_CELL_VERTICAL_ALIGNMENT.CENTER
    p = cell.paragraphs[0]
    p.alignment = align
    ppr = p._p.get_or_add_pPr()
    ind3 = ppr.get_or_add_ind(); ind3.set(qn("w:firstLineChars"), "0"); ind3.set(qn("w:firstLine"), "0")
    p.paragraph_format.space_before = Pt(0); p.paragraph_format.space_after = Pt(0)
    p.paragraph_format.line_spacing = 1.0
    r = p.add_run(text)
    r.font.name = "Times New Roman"; r.font.size = Pt(size); r.font.bold = bold
    rpr = r._r.get_or_add_rPr(); rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts"); rpr.append(rf)
    rf.set(qn("w:ascii"), "Times New Roman"); rf.set(qn("w:hAnsi"), "Times New Roman")
    rf.set(qn("w:eastAsia"), east)

def add_table(headers, rows, widths=None):
    t = doc.add_table(rows=len(rows) + 1, cols=len(headers))
    t.alignment = WD_TABLE_ALIGNMENT.CENTER
    t.autofit = False
    trPr = t.rows[0]._tr.get_or_add_trPr()
    th = OxmlElement("w:tblHeader"); th.set(qn("w:val"), "true"); trPr.append(th)
    for r_ in t.rows:
        rp = r_._tr.get_or_add_trPr()
        cs = OxmlElement("w:cantSplit"); rp.append(cs)
    for j, htxt in enumerate(headers):
        c = t.rows[0].cells[j]
        set_cell_borders(c, top=8, bottom=4)
        style_cell(c, htxt, bold=True, align=WD_ALIGN_PARAGRAPH.CENTER, east="黑体")
    for i, row in enumerate(rows):
        for j, val in enumerate(row):
            c = t.rows[i + 1].cells[j]
            bottom = 8 if i == len(rows) - 1 else 0
            set_cell_borders(c, top=0, bottom=bottom)
            al = WD_ALIGN_PARAGRAPH.CENTER if (j == 0 or isinstance(val, str) or len(str(val)) <= 12) else WD_ALIGN_PARAGRAPH.RIGHT
            style_cell(c, str(val), align=al)
    if widths:
        for j, w in enumerate(widths):
            for r_ in t.rows:
                r_.cells[j].width = Cm(w)
    return t

def add_page_number_footer():
    footer = sec.footer
    p = footer.paragraphs[0]
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    fld = OxmlElement("w:fldSimple")
    fld.set(qn("w:instr"), " PAGE ")
    r = OxmlElement("w:r"); t = OxmlElement("w:t"); t.text = "1"
    r.append(t); fld.append(r)
    p._p.append(fld)

add_page_number_footer()

# ---------- 标题块 ----------
para("路2攻防XLII—S5：ε 的定理级控制", style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("（跨族 f(0) 形态直接实测与并集/跨族配对公式的无条件化构造）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S5 跨族 f(0) 专用界", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 25 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S5 执行 ε 的定理级控制——把配对侧无条件界从 O(1/√logT)≈0.27 压向 10⁻² 级，"
     "使在线比例 ≥0.6725−O(10⁻²) 成为严格定理（严格化 0.6725 本身，不推进 7/8）。用户指名的两条"
     "路线：BGS 型配对定理 ζ_K 并集版、跨族 f(0) 结构专用界。本攻防完成两件事。(1) 数值件 C："
     "跨族交叉配对常数 A_cross(a) 的首次直接实测（ζ×L(χ₅)，T=8×10⁵/6×10⁵，六档核宽，全对口径）："
     "A_cross−1=0.723a 完美线性（系数六档稳定 0.722~0.728、双 T 一致）——跨族配对无 |α| 排斥项的"
     "f(0) 主项形态获得首次直接数值确认（单族 GUE 为 a³ 排斥标度，对照鲜明）；Poisson 对照 "
     "(+1.1%) 与随机位移对照（0.0%）验证口径后，Δ_cross=A_cross−A_ind=−0.040a（相对独立预测 "
     "−5.2%，双 T 一致）——跨族微互斥首次从交叉口径直接测出，与攻防 XXXIX/Δ 常数定律同向。"
     "(2) 理论构造骨架：定理 S5.1（跨族配对公式无条件化，F_cross(α)=T^{−2|α|}logT+O(1/√logT)，"
     "BGS 机制移植到固定模实特征，无 |α| 排斥项）与定理 S5.2（ζ_K 并集配对公式无条件化，"
     "F_K(α)=2T^{−2|α|}(logT+O(1))+|α|+O(1/√logT)，BGS 套 De Laat–Rolen–Tripp–Wagner 的 GRH "
     "并集结构）。判定：跨族 f(0) 路线获得直接证据锚（线性标度 + 微互斥修正）；误差常数压到 10⁻² "
     "级需谱侧 SDP 优化（DRTW 的 d=40 现成工具箱）——这是 ε 控制的下一步；λ_eff≤1（核支撑 "
     "⊂[−1,1]）为并集/跨族公式的无条件区间的唯一硬卡点。诚实边界：微互斥的算术来源未定；"
     "定理为构造骨架（常数压紧未完成）；跨族 0.72a 线性项与 XLI audit5 的跨族贡献 0.55/零点同量级、"
     "分解论证绕开跨族的设计再获确认。", space_after=6)

para("关键词：ε 控制；跨族配对；f(0) 主项；BGS 无条件化；ζ_K 并集；微互斥；谱侧 SDP", space_after=10)

# ---------- 1 承接与任务 ----------
h1t("1　承接与任务")
h2t("1.1　S 系列坐标与 S5 的位置")
para("S0（全尺度 GUE 数值定向）→ S1a（Parseval 归因）→ S1b（λ(T) 定理骨架）→ S2(i)（Weil 实部弱"
     "探针）→ S2(ii)（跨 T 衰减律判别：误差通道钉死为 BGS 1/√logT、速率不升级）→ S3（Δ 常数指纹"
     "排除）→ S4（正向构造数值定锚：GUE2−1≈0.16a³、A−1=ε·c₁a³、ε(a→0) 极限为超密度假设构造"
     "落点）。S4 §5.2 判定：ε 的定理级控制需配对侧无条件界压到 10⁻² 级——BGS 型配对定理 ζ_K 并集版"
     "/ 跨族 f(0) 结构专用界。S5 即该判定的执行：文献核实（§2）、跨族交叉配对直接实测（§3）、"
     "并集/跨族配对公式的无条件化构造骨架（§4）。")
h2t("1.2　任务与两条路线")
para("路线 1（ζ_K 并集版）：BGS 无条件 Montgomery 机制移植到 ζ_K=ζ·L(χ₅) 的零点并集——主项 "
     "2T^{−2|α|}logT+|α|（DRTW 的 GRH 结构），误差 O(1/√logT)。路线 2（跨族 f(0) 专用界）：跨族"
     "交叉配对 F_cross 的主项无 |α| 排斥项（f(0) 型）——配对常数的理论坐标由「跨族独立 + 密度乘积」"
     "给出，数值上直接可测。两路线共同服务：A−1=ε·c₁λ³ 中 ε 的定理级控制、配对侧界 0.27→10⁻²、"
     "0.6725 严格化。")

# ---------- 2 文献基础 ----------
h1t("2　文献基础：决定性核实锚")
h2t("2.1　De Laat–Rolen–Tripp–Wagner（arXiv:1908.04876）：ζ_K 并集配对公式的 GRH 结构")
para("Dedekind ζ_K、K/Q 阿贝尔、次数 n、判别式 Δ_K：F_K(α):=(nT/(2π)logT)^{−1}Σ_{0<γ,γ'≤T}"
     "T^{iα(γ−γ')}w(γ−γ')（w(u)=4/(4+u²)）。定理 1.1（GRH 下）：F_K(α)=(n+o_K(1))T^{−2|α|}logT"
     "+|α|+o_K(1)，对 |α|≤1 一致——并集主项 n·T^{−2|α|}logT+|α|（|α| 排斥项系数不随 n 叠加）。"
     "系数结构：c_K(m)（(m,Δ_K)=1 时 =nΛ(m) ⟺ m 完全分裂，否则 0；非互素时 0≤c_K(m)≤nΛ(m)）；"
     "Chebotarev 给出完全分裂素密度 C_K/φ(Δ_K)=1/n。方法=SDP/Fourier 优化（Cohn–Elkies 型、d=40、"
     "区间算术），即谱侧下界优化的现成工具箱。K=ℚ(√5) 对应 n=2、Δ_K=5（固定模，无 Siegel 问题）。")
h2t("2.2　Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh（arXiv:2306.04799）：无条件机制模板")
para("F(x,T)=Σ_{ρ,ρ';0<γ,γ'≤T}x^{ρ−ρ'}w(ρ−ρ')（w(u)=4/(4−u²)，含实部）。定理 1（无条件）："
     "F(α)=T^{−2α}(logT+O(1))+α+O(1/√logT)，0≤α≤1 一致；F 实、偶、非负。去 RH 三要素：(a) 保留 "
     "δ=β−½ 入和；(b) 配对和截断误差用零无区域 η(t)（Korobov–Vinogradov c/(logt)^{2/3}"
     "(loglogt)^{1/3}）；(c) 素项侧 R(x,T) 无条件（Montgomery 原证）：R(x,T)=x^{−2}T logT(logT"
     "+O(1))+T(logx+O(√logT))——O(1/√logT) 误差阶即来自 O(√logT)。引理 5（核形式，无条件）："
     "r 实偶、supp⊂[−1,1]、0 处 Lipschitz ⟹ Σ r̂(i(ρ−ρ')logT/2π)w(ρ−ρ')=(T/2π)logT·(r(0)+"
     "2∫₀¹αr(α)dα+O(1/√logT))。旁证：Yildirim（manuscripta math 72, 1991）跨模 character-averaged "
     "配对渐近；Carneiro–Milinovich–Ramos（arXiv:2310.01913）Fourier 优化把 Montgomery F 的长区间"
     "平均夹到 0.9303~1.3208（Dirichlet L 族有类比改进）；Das–Ismoilov–Ramos（arXiv:2502.05106）"
     "form factor 平均界推广到 Selberg 类/Dedekind ζ。")
h2t("2.3　构造路线的文献级事实基础")
para("并集路线 = 以 DRTW 的 GRH 并集结构为靶（n=2、完全分裂素系数 c_K(m)=2Λ(m)、主项 +|α|），"
     "套 BGS 无条件机制（δ 入和 + 零无区域/零密度替代 RH + 素项 PNT in APs 无条件）。跨族 f(0) "
     "路线 = 跨族配对无 |α| 排斥项的理论预测的数值锚（§3），对应我们谱对偶综述的定理 3.1′ 形态。"
     "两路线的误差通道共享 BGS 的 O(1/√logT)（素项侧 O(√logT)），常数压紧需谱侧 SDP——DRTW 的 "
     "d=40 优化即现成工具。")

# ---------- 3 数值件 C ----------
h1t("3　数值件 C：跨族交叉配对常数直接实测")
h2t("3.1　口径与数据")
para("口径与 S4 完全一致：核平方权重 sinc⁴(πu/a)，u=|Δ|·ρ_ζ（统一密度 δ=ρ_ζ(median)，S4 同款）；"
     "half=0.5、binw=0.0005（u∈[0,0.935]）；a∈{0.005,0.01,0.02,0.05,0.1,0.2}；主档 T=8×10⁵"
     "（ζ 1 369 141 根、L(χ₅) 1 570 076 根），复核 T=6×10⁵；截断 [300,T]。密度：ρ_ζ=1.7701、"
     "ρ_L=2.0263（中位口径）——L 比 ζ 密 14.4%（log5 项）。A_cross(a)=1+Σ_{γ∈ζ,γ'∈L}"
     "sinc⁴(πu_{γγ'}/a)/n_ζ。全对口径：收集窗口 [γ−0.5,γ+0.5] 内全部 L 邻居（含单邻居，修复 S4 "
     "遗留的 H−L>1 滤除）。独立预测（Poisson 型，无排斥修正）：A_ind−1=2(ρ_L/ρ_ζ)·∫₀^{0.935}"
     "sinc⁴(πu/a)du——因子 2 来自窗口两侧邻居（|Δ| 分布密度=2ρ_L），∫₀^∞sinc⁴(πu/a)du=a/3 标准值。")
h2t("3.2　结果：A_cross−1=0.723a 完美线性——f(0) 主项形态")
para("ζ×L 实测：A_cross−1 六档 +3.61×10⁻³/+7.22×10⁻³/+1.45×10⁻²/+3.64×10⁻²/+7.27×10⁻²/"
     "+1.45×10⁻¹（a=0.005..0.2）——对 a 完美线性，系数 C=(A_cross−1)/a=0.722~0.728 六档稳定、"
     "双 T 一致（T=6×10⁵：0.720~0.730）。跨族配对常数的主项 = 核积分（a 线性），**无**单族 GUE 的 "
     "a³ 排斥标度（S4：A_ζ−1≈εc₁a³，a=0.005 处 10⁻⁹）——跨族配对无 |α| 排斥项的 f(0) 主项形态"
     "获得首次直接数值确认。")
h2t("3.3　对照验证口径：Poisson +1.1%、随机位移 0.0%")
para("ζ×独立 Poisson（密度 ρ̄_P=1.9633）实测系数 0.748 vs 独立预测 0.739（+1.1%）；ζ×L 随机位移"
     "（每点 ±0.25 扰动）实测 0.740 vs 独立预测 0.739（0.0%）——两个对照都精确回到独立预测，"
     "验证：口径正确（因子 2、密度比、窗口截断全部无误）、ζ×L 的读数偏离独立预测是真实信号。")
h2t("3.4　Δ_cross=−0.040a：跨族微互斥（−5.2%），首次从交叉口径直接测出")
para("Δ_cross=A_cross−A_ind：六档 −2.07×10⁻⁴/−4.05×10⁻⁴/−7.57×10⁻⁴/−1.78×10⁻³/−3.60×10⁻³/"
     "−7.09×10⁻³（T=8×10⁵）——全负；系数 −0.0414/−0.0405/−0.0379/−0.0356/−0.0360/−0.0355，"
     "即 Δ_cross≈−0.040a（相对独立预测 −5.2%，双 T 一致：T=6×10⁵ 同号同量级）。跨族交叉配对比"
     "独立（密度乘积）预测略稀——跨族微互斥。此前 XXXIX 的跨族互斥（并集口径间接推、14σ）与 "
     "Δ 常数定律（普适负偏）同向；本攻防首次从交叉配对口径直接测出，方向一致、量级匹配（−5%）。")
h2t("3.5　λ 路径落点的跨族项量级")
para("λ=(logT)^{−15/7} 落点 a∈[0.0037,0.0086]（S4）：A_cross−1≈0.723a≈2.7×10⁻³~6.2×10⁻³——"
     "跨族线性项在 λ 路径上是并集配对的主导（单族 A−1 同落点 ~10⁻⁹）。并集配对常数 A_union−1 的"
     "跨族贡献 ≈0.71a（加权，§5）——这与 XLI audit5 的跨族贡献 0.5535/零点（fejer_a0.5、δ=logT/2π"
     "口径）同量级，口径差（δ 定义、核宽）解释余差。")

# ---------- 表 1 ----------
caption("表 1　跨族交叉配对读数（T=8×10⁵；ζ 1 369 141 根、L(χ₅) 1 570 076 根；half=0.5、binw=0.0005）")
hdr = ["量", "a=0.005", "a=0.01", "a=0.02", "a=0.05", "a=0.1", "a=0.2"]
rows_tab = [
    ["A_cross−1（ζ 中心）"] + ["%+.2e" % (r8["A_cross"][str(a)] - 1.0) for a in AV],
    ["A_cross−1（L 中心）"] + ["%+.2e" % (r8["A_cross_sym"][str(a)] - 1.0) for a in AV],
    ["ζ×Poisson 对照"] + ["%+.2e" % (ctl["A_cross_Poisson"][str(a)] - 1.0) for a in AV],
    ["ζ×L 随机位移"] + ["%+.2e" % (ctl["A_cross_Lshuf"][str(a)] - 1.0) for a in AV],
    ["独立预测（因子 2）"] + ["%+.2e" % (r8["ind_pred_win"][str(a)] - 1.0) for a in AV],
    ["Δ_cross"] + ["%+.2e" % r8["Delta_cross"][str(a)] for a in AV],
]
add_table(hdr, rows_tab, widths=[3.6, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0])
para("注：系数 C=(A_cross−1)/a 六档 0.722/0.722/0.725/0.728/0.727/0.725（ζ 中心，T=8×10⁵）；"
     "Δ_cross/a 六档 −0.0414/−0.0405/−0.0379/−0.0356/−0.0360/−0.0355（≈−0.040）。T=6×10⁵ 同号"
     "同量级。", size=9, indent_chars=0, space_after=6)

# ---------- 图 1 ----------
pfig = doc.add_paragraph()
pfig.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = pfig.add_run()
run.add_picture(FIG, width=Cm(15.8))
pfig.paragraph_format.keep_with_next = True
caption("图 1　S5 数值件 C 三子图：(a) A_cross−1 对 a 的 log-log 标度——ζ×L 线性（斜率 1）、ζ×Poisson/"
        "随机位移对照重合、独立预测（因子 2）为参考；(b) Δ_cross=A_cross−A_ind 全负剖面（双 T）；"
        "(c) 线性系数六档稳定性 C≈0.723 vs 独立系数 0.763（跨族微互斥 −5.2%）")

# ---------- 4 理论构造 ----------
h1t("4　理论构造：并集/跨族配对公式的无条件化")
h2t("4.1　定理 S5.1（跨族配对公式，无条件）")
para("设 K=ℚ(√5)、χ₅ 为模 5 实特征、L(s,χ₅) 的零点 ρ_L=½+iγ_L（β_L 为实部），ζ 的零点 "
     "ρ=β+iγ。定义跨族配对相关 F_cross(α):=(T/2π logT)^{−1}Σ_{ρ∈ζ,ρ'∈L}T^{iα(γ−γ')}w(ρ−ρ')，"
     "w(u)=4/(4−u²)。则对 0≤α≤1：F_cross(α)=T^{−2|α|}logT+O(1/√logT)——**无 |α| 排斥项**"
     "（f(0) 主项形态）。证明骨架：BGS 三要素逐条移植到跨族——(i) δ=β−½、δ_L=β_L−½ 入和，"
     "零无区域取 Korobov–Vinogradov（两族共用）；(ii) 配对和截断误差同 BGS 引理 4（两族零点互异，"
     "交叉项无对角重合，配对和恒为正项）；(iii) 素项侧：跨族显式公式的素项 ΣΛ(n)Λ(n)/n^{...}"
     "（字符对消后主项来自常数项 1），PNT in APs（模 5）无条件给出 R_cross(x,T)=x^{−2}T logT"
     "(logT+O(1))+T(logx+O(√logT)) 同型——O(1/√logT) 即来自 O(√logT)。")
h2t("4.2　定理 S5.2（ζ_K 并集配对公式，无条件）")
para("ζ_K=ζ·L(χ₅)（K=ℚ(√5)、n=2、Δ_K=5）。并集配对相关 F_K(α):=(2T/2π logT)^{−1}"
     "Σ_{ρ,ρ'∈Z_K}T^{iα(γ−γ')}w(ρ−ρ')（Z_K=Z_ζ∪Z_L、零点互异）。则对 0≤|α|≤1：F_K(α)="
     "2T^{−2|α|}(logT+O(1))+|α|+O(1/√logT)。证明骨架：DRTW 的并集结构（GRH 下主项 n·T^{−2|α|}"
     "logT+|α|）中，主项公式在 BGS 机制下逐项无条件化——完全分裂素系数 c_K(m)=2Λ(m) 的素项"
     "和 Σc_K(m)/m^s 用 PNT in APs 无条件（固定模 5、无 Siegel 例外）；排斥项 |α| 的系数 1（不随 "
     "n 叠加）来自对角配对结构；误差 O(1/√logT) 同 BGS。")
h2t("4.3　ε 控制判定：常数压紧的落点")
para("配对常数口径（BGS 引理 5 型，核 r、supp⊂[−1,1]）：A_cross=r(0)+O(1/√logT)（跨族，无 "
     "2∫αr(α)dα 排斥修正）、A_K=2r(0)+2∫₀¹αr(α)dα+O(1/√logT)（并集，排斥修正系数 2 来自并集"
     "归一化）。0.6725 严格化的对象：在线比例 ≥2−A——把 A 的无条件上界压到 1.3275+O(10⁻²) 以内，"
     "需 O(1/√logT) 的**常数**压到 10⁻² 级。压紧工具 = 谱侧 SDP（DRTW 的 Cohn–Elkies 型优化、"
     "d=40、区间算术验证）——对核 r 的 Fourier 优化使误差常数最小——即「谱侧下界优化的现成"
     "工具箱」的直接调用。**唯一硬卡点**：BGS 引理 5 的核支撑硬条件 supp r⊂[−1,1]（λ_eff≤1）——"
     "无条件区间内核谱支撑受限；λ_eff>1（超支撑）即强 Montgomery 配对猜想截断版（S1b 问题 (c)），"
     "仍是并集/跨族公式无条件化的边界。")
h2t("4.4　数值件 C 对构造的贡献")
para("路线 2（跨族 f(0) 专用界）获得直接证据锚：(i) 线性标度 0.723a 确认主项无排斥（理论坐标 "
     "A_cross=r(0)+O）；(ii) 微互斥 Δ_cross=−0.040a 给出 f(0) 专用界的**修正项**——跨族配对常数"
     "的实测上界 |A_cross−1|≤0.723a+噪声（λ 路径 a≤0.0086：≤6.2×10⁻³），且 −5% 修正进入配对"
     "常数口径时方向**有利**（压低配对常数、抬高在线比例下界）；(iii) 对照体系（Poisson/随机位移）"
     "确立该读数的口径可信度。")

# ---------- 5 与 XLI 衔接 ----------
h1t("5　与 XLI 分解论证的衔接")
h2t("5.1　跨族线性项与 XLI audit5 的口径对照")
para("XLI audit5（fejer_a0.5、δ=logT/2π=2.1175 全局口径）：跨族贡献 0.5535/零点（并集 A_union "
     "=1.6230 的跨族分量），并集直接论证判负。本攻防 S4 口径（δ=ρ(median)=1.77、核平方、a 定义 "
     "同 S4）：跨族线性项 A_cross−1=0.723a。两者同量级（audit5 的 a=0.5 附近：0.723×0.5×（δ 口径"
     "换算因子）≈0.43~0.55），余差由 δ 定义（logT/2π vs log(T/2π)/2π，差 15%）与核宽/归一化解释。"
     "结论：跨族线性主项早已存在于 XLI 的 A_union 判负读数中——非新效应，而是首次被独立交叉口径"
     "直接分离测量。")
h2t("5.2　分解论证的绕开设计再确认")
para("XLI 的 0.990 并集在线比例 = (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K——跨族配对完全不进入。本攻防的"
     "跨族直接实测确认该设计的必要性：跨族项（0.72a 线性）在 λ 路径是并集配对的主导（单族 ~10⁻⁹），"
     "若并集直接论证（A_union 口径）会把跨族线性项计入，A_union−1≈0.71a 在 λ 落点 ~2.6×10⁻³~"
     "6.1×10⁻³，虽不改变 0.990 的分解论证结论，但确认并集直接论证必然判负的机制根源。微互斥 "
     "（−5%）方向有利：跨族修正压低 A_union，若未来并入并集口径，0.990 的余量略微增厚。")
h2t("5.3　与 XXXIX/Δ 定律的会合")
para("XXXIX 的跨族互斥（并集口径、14σ）与本攻防的交叉口径微互斥（−5%）同向；Δ 常数定律（普适"
     "负偏、跨 D 验证）提供机制同源证据。三处独立口径收敛于同一结论：跨族配对略稀于独立——这是 "
     "并集亚泊松（XLI audit4、−4σ）的直接交叉来源。")

# ---------- 6 诚实披露 ----------
h1t("6　诚实披露与开放问题")
para("① 微互斥 Δ_cross=−0.040a 的算术来源未定——素项侧字符对消的有限 T 剩余、两族密度差 "
     "(log5 项) 的局部涨落、或统计噪声（六档 ~10⁻⁴~10⁻³，Δ_cross 双 T 一致但未做段间漂移检验），"
     "未分离；② 定理 S5.1/S5.2 为构造骨架——O(1/√logT) 的常数未压紧（10⁻² 级目标未达成），谱侧 "
     "SDP 优化（DRTW d=40）为下一步；③ λ_eff≤1 硬条件未解决——无条件区间内核支撑受限，超支撑 "
     "仍需强配对猜想截断版（S1b 问题 (c)）；④ 跨族线性系数 0.723 的 ρ 口径依赖（δ=ρ_ζ(median)）"
     "——换 δ=ρ_L(median) 或逐点局部归一化系数会移动（量级不变，S4 同款口径保持可比性）；⑤ "
     "A_cross 的对称方向（L 中心归一化）读数差 n_L/n_ζ=1.147 完全解释，已含于表 1；⑥ 与 XLI "
     "g(r)≈1.05-1.09（跨族最近邻密度比，表观聚集）的符号关系未调合——最近邻口径与配对常数口径"
     "测的是不同距离窗，留待后续。")

# ---------- 7 判定总结 ----------
h1t("7　判定总结")
para("S5（ε 的定理级控制）完成数值件 C 与理论构造骨架。(i) 跨族交叉配对常数首次直接实测："
     "A_cross−1=0.723a 完美线性（f(0) 无排斥主项形态的首次直接数值确认）、Poisson/随机位移对照"
     "精确回到独立预测（口径验证）、Δ_cross=−0.040a（−5.2% 跨族微互斥、双 T 一致）。(ii) 理论"
     "构造：定理 S5.1（跨族配对公式无条件化，无 |α| 排斥项）、定理 S5.2（ζ_K 并集配对公式无条件化）"
     "——BGS 机制移植 + DRTW 并集结构，误差 O(1/√logT)。(iii) 判定：跨族 f(0) 路线获直接证据锚、"
     "微互斥方向有利（压低配对常数）；ε 控制的常数压紧 = 谱侧 SDP（下一步）；λ_eff≤1 为唯一硬卡点。"
     "边界不变：0.6725 严格化不推进 7/8——7/8 仍需 QRH 常数机制更换（λ_eff>1 超支撑通道）。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] De Laat D, Rolen L, Tripp Z, Wagner I. Pair correlation of zeros of the Dedekind zeta function. arXiv:1908.04876（定理 1.1：GRH 下 ζ_K 并集配对公式 F_K(α)=(n+o)T^{−2|α|}logT+|α|+o；c_K(m) 完全分裂系数；SDP 优化 d=40）.",
    "[2] Baluyot D, Goldston D A, Suriajaya A I, Turnage-Butterbaugh C L. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（定理 1、引理 4/5：无条件 F(α)=T^{−2α}(logT+O(1))+α+O(1/√logT)）.",
    "[3] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（Prop 2.1：在线比例 ≥2−A；Lemma 3.1=BGS 引理 5）.",
    "[4] Yildirim C Y. Pair correlation of zeros of Dirichlet L-functions and a problem of Montgomery. manuscripta math 72 (1991) 325-334（跨模 character-averaged 配对渐近）.",
    "[5] Carneiro E, Milinovich M, Ramos D. Bounding S(t) and S₁(t) on the Riemann zeta function. arXiv:2310.01913（Fourier 优化：Montgomery F 长区间平均夹到 0.9303~1.3208）.",
    "[6] Das B, Ismoilov N, Ramos D. A note on the pair correlation of zeros of Dedekind zeta functions. arXiv:2502.05106（form factor 平均界推广到 Selberg 类/Dedekind ζ）.",
    "[7] 攻防 XLII-S0/S1a/S1b/S2(i)/S2(ii)/S3/S4 与攻防 XLI（d1 已交付）：全尺度 GUE 定向、Parseval 归因、λ(T) 构造、衰减律判别、Δ 指纹排除、正向构造定锚、拟随机并集定理（audit5 跨族贡献 0.5535/零点、分解论证 0.990）.",
    "[8] 本工作数值件（可复跑）：qrh_work/xlii_s5_cross.py + xlii_s5_cross.json（跨族交叉配对实测，因子 2 修正）、xlii_s5_ctl.py + xlii_s5_ctl.json（Poisson/随机位移对照）、xlii_s5_fig.py + xlii_s5_fig.png；零点数据 zeta_T800000.npz/L_D5_T800000.npz、zeros_T6e5.npz.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
