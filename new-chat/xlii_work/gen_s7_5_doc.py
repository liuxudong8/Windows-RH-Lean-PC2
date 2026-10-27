# -*- coding: utf-8 -*-
"""攻防 XLII · S7.5 落档：骨头 3（N3）——离线项一致版本（BGS 余项跨 λ 一致）。
母本：gen_s7_4_doc.py（样式链 + ^{…}/_{…} 解析 para()；标题/题注用 Unicode 形态，禁 ** 星号）。
文献依据：BGS arXiv:2306.04799 定理 1 证明（(2.18)/(2.19)）、引理 4（截断 Z=T log²T）、引理 5（(3.4)）。
数值件：S7 件 E（xlii_s7_prime.json：|S_final|/N_L=4.0e-8@T=8e5）、件 F（xlii_s7f_supersupport：主 A 衰减 + 形态 B ratio=1.000）。
"""
import os, re
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.5-骨头3-离线项一致版本-BGS余项跨λ一致.docx"
FIG = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s7f_fig.png"

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

def _apply_run_font(r, bold=False, font=None, size=None):
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

def para(text, style=None, align=None, bold=False, font=None, size=None, indent_chars=0,
         space_before=None, space_after=None):
    p = doc.add_paragraph(style=style)
    if align is not None:
        p.alignment = align
    if indent_chars:
        ppr = p._p.get_or_add_pPr(); ind2 = ppr.get_or_add_ind()
        ind2.set(qn("w:firstLineChars"), str(indent_chars * 100))
    tokens = re.split(r"(\^\{[^}]*\}|_\{[^}]*\})", text)
    for tk in tokens:
        if not tk:
            continue
        if tk.startswith("^{"):
            r = p.add_run(tk[2:-1]); r.font.superscript = True
        elif tk.startswith("_{"):
            r = p.add_run(tk[2:-1]); r.font.subscript = True
        else:
            r = p.add_run(tk)
        _apply_run_font(r, bold=bold, font=font, size=size)
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
para("路2攻防XLII—S7.5：骨头 3——离线项一致版本", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（N3 击破：BGS 余项跨 λ 一致——离线障碍无核宽依赖）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S7.5 骨头 3", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 26 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("骨头 3（N3）——离线项一致版本。挂清单定义：BGS 定理 1 的离线余项 O(1/√logT) 在核宽 a→0 "
     "（λ→∞，推 1 场景）时须跨 λ 一致——余项常数不随核窄化发散。本档给出核心判定：该一致版本"
     "在 BGS 证明结构内已经成立——余项来源与核无关。定理 1 证明的余项仅两处：(a) 引理 4 的截断"
     "误差 O(x^{1−2η(T log²T)}log³T)+O(x)，截断 Z=T log²T 只依赖 T；(b) 素数项积分 R(x,T)="
     "∫|r(x,t)|²dt 的修正 O(T√logT)（GM87 引理 6/7），Montgomery 引理右端 r(x,t) 不含任何核。"
     "核只出现在零点侧 L(x,T)=∫|l(x,t)|²dt，经 L=R 恒等式与素数项恒等。故引理 5 余项 O(T√logT) "
     "对 supp⊂[−1,1] 的一切核一致；N1（缩放自同构）已证缩放核 r_{a}(α)=a⁻¹r(α/a) 保持该条件，"
     "跨 λ 一致随之成立。定理 N3：(i) 配对公式余项跨 λ 一致（O(T√logT)，常数不依赖 a）；(ii) "
     "素数项 S_final 跨 λ 一致（SW 压制常数只依赖模 5 与 T）——数值件 E：|S_final|/N_{L}="
     "4.0×10^{−8}@T=8×10^{5}，件 F 形态实验 B：δS 与 ½K″(0)(aδ)²T_{2} 比值 1.000（核窄化下离线项"
     "二阶主导、无发散）；(iii) 离线总余项 R_{off}=O(1/√logT)·N_{L} 跨 λ 一致。与 N1/N2 联合："
     "A(K_{λ})−1=0.16a³+O((logT)^{−1/2})(1+O(a²))→0——推 1 三块骨头齐。", space_after=6)

para("关键词：离线项；一致余项；素数项；Siegel–Walfisz；配对公式；跨 λ 一致",
     space_after=10)

# ---------- 1 N3 定义与背景 ----------
h1t("1　N3 的定义与背景")
para("S7.1 §7.1 挂入 Stage 3+ 三块硬骨头：N1 引理 5 超支撑推广（S7.3 击破——缩放自同构）、N2 "
     "ε–λ 联动（S7.4 击破——正则化撑宽与有效核宽标度律）、N3 离线项一致版本。本档执行 N3。")
para("背景：BGS 定理 1 给出配对和的无条件展开 F(α)=T^{−2α}(logT+O(1))+α+O(1/√logT)，对 0≤α≤1 "
     "一致。推 1 场景的核窄化（a→0）要求该 O(1/√logT) 余项的隐式常数不随核宽发散——否则超支撑"
     "推广（N1）在余项层失效。N3 的任务：拆出 BGS 余项的全部来源，逐一验证与核无关，给出跨 λ "
     "一致界。")

# ---------- 2 余项结构拆解 ----------
h1t("2　BGS 余项的结构拆解：两处来源均不含核")
h2t("2.1　引理 4：截断误差")
para("L(x,T)=∫₀ᵀ|l(x,t)|²dt 的零点侧组装先按 |γ|≤Z 截断。引理 4 的估计：")
para("L(x,T) = 4Σ_{|γ|,|γ′|≤Z} x^{δ+δ′+i(γ−γ′)}∫₀ᵀ dt/[(1+((t−γ)+iδ)²)(1+((t−γ′)−iδ′)²)] + O(x)",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("取 Z=T log²T。截断误差 (2.14)/(2.15) 用平凡估计 Σ|γ|≥Z γ^{−2}≪logZ/Z 与零点计数 N(T)——"
     "只依赖 T，不含核。离临界线因子 x^{δ+δ′}≪x^{2Θ(Z)−1}≤x^{1−2η(T log²T)}（Θ 为零点实部上"
     "确界）只在误差主项 O(x^{1−2η}log³T) 出现，与核无关。")
h2t("2.2　引理 1（Montgomery）：素数项")
para("l(x,t)=r(x,t)，右端为 Landau 显式公式（σ=3/2 取法）：")
para("r(x,t) = −Σ_{n≤x}Λ(n)/n^{1/2+it}·min(n/x, x/n) + x^{−1}(log(|t|+2)+O(1)) + O(x^{1/2}/(1+t²)) + O(x^{−5/2}/(|t|+2))",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("素数项 r(x,t) 由 ζ 的显式公式导出，不含任何核函数。核只通过 l(x,t)（零点侧求和）进入。")
h2t("2.3　R(x,T)：素数项积分与 O(1/√logT) 的来源")
para("R(x,T)=∫₀ᵀ|r(x,t)|²dt。GM87 引理 6/7 的无条件改进（(2.19)）：")
para("R(x,T) = x^{−2}T logT·(logT+O(1)) + T(log x+O(√logT))，0≤x≤T",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("F(α) 展开的 α+O(1/√logT) 即由此项经 (1.3) 归一化得到。r 不含核 ⟹ R 不含核 ⟹ 余项 "
     "O(T√logT) 对一切核一致。核只在 L 侧出现，L=R 恒等式（(2.17)）使两边等同——定理 1 的余项"
     "组装无核依赖。")
h2t("2.4　引理 5：通用核配对公式")
para("引理 5（(3.4)）：对 supp r⊂[−1,1]、r Lipschitz@0：")
para("Σ_{0<γ,γ′≤T} r̂(i(ρ−ρ′)logT/2π)w(ρ−ρ′) = (T/2π)logT·[r̂(0)+2∫₀¹αr(α)dα] + O(T√logT)",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("余项 O(T√logT) 与核 r 无关（对 supp⊂[−1,1] 一致）——由 §2.1–§2.3：截断与素数项均不含"
     "核。N1（S7.3 定理 N1）已证缩放核 r_{a}(α)=a⁻¹r(α/a) 逐条保持引理 5 条件（supp、Lipschitz、"
     "L¹），且配对公式形式不变、误差无 a 依赖——跨 λ 一致性在配对公式层成立。")

# ---------- 3 定理 N3 ----------
h1t("3　定理 N3（离线项一致版本）")
h2t("3.1　定理陈述")
para("定理 N3（离线项一致版本）。设 S7.1 的 L 版 BGS 型配对假设成立（实特征 χ₅、模 5、SW 压制）。"
     "对核族 r_{a}(α)=a⁻¹r(α/a)（a→0）：")
para("（i）配对公式余项跨 λ 一致：配对和=(T/2π)logT·[r̂_{a}(0)+2∫₀¹αr_{a}(α)dα]+O(T√logT)，"
     "隐式常数不依赖 a；", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=0)
para("（ii）素数项跨 λ 一致：S_final(a)=O(T√logT)，常数只依赖模 5 与 T，不依赖 a；",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=0)
para("（iii）离线总余项：R_{off}=O(1/√logT)·N_{L}，跨 λ 一致。",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("推论：与 N1（配对公式层）、N2（ε–λ 联动）联合，配对常数")
para("A(K_{λ,ε})−1 = 0.16a³(1+o(1)) + O((logT)^{−1/2})(1+O(a²)) → 0",
     align=WD_ALIGN_PARAGRAPH.CENTER, space_after=4)
para("推 1 的三块骨头全部闭合。")
h2t("3.2　证明骨架（四步）")
para("第一步（配对公式余项跨核一致）：由 §2.1–§2.3——定理 1 余项仅两处来源（引理 4 截断、R(x,T) "
     "素数项积分），均不含核，故引理 5 的 O(T√logT) 对 supp⊂[−1,1] 一致。N1 已证缩放核保持条件，"
     "一致界对 a 均匀。")
para("第二步（素数项层）：S7.1 的 L 版假设下素数项 r_{L} 用 χ₅ 的 SW（模 5）压制；∫|r_{L}|²dt 的 "
     "主项+O(T√logT) 常数只依赖模 5。核窄化只影响零点侧组装，经 L=R 恒等式吸收。")
para("第三步（偏差合成）：A−1=[非对角配对和]/N_{L}+R_{off}/N_{L}=0.16a³(1+o(1))+O((logT)^{−1/2})"
     "(1+O(a²))（首项：N1/S4 的 GUE2 标度律；次项：本定理 (iii)）。")
para("第四步（取法代入）：λ=(logT)^{q} ⟹ R_{off}/N_{L}=O((logT)^{−1/2}) 不随 q 恶化；ε=c·a（N2）"
     "⟹ 总偏差→0。□")

# ---------- 4 数值 ----------
h1t("4　数值支撑：离线项跨尺度、跨核宽一致")
para("已有数值件两处交叉验证离线项一致版本。")
caption("表 1　离线项一致版本的数值证据（件 E 与件 F）")
hdr1 = ["数据件", "量", "参数档", "数值", "含义"]
rows1 = [
    ["件 E（S7）", "|S_final|/N_L", "T=8×10⁵", "4.0×10⁻⁸", "素数项相对主项比值（跨高度一致）"],
    ["件 F 主 A", "|S_a|/N_L", "X=10⁴", "2.04×10⁻⁴", "素数项随截断增长单调衰减"],
    ["件 F 主 A", "|S_a|/N_L", "X=10⁸", "1.0×10⁻⁸", "衰减快于 X^{-1/2}（SW 型压制）"],
    ["件 F 形态 B", "δS/(½K″(0)(aδ)²T₂)", "aδ≤3×10⁻³", "1.000", "核窄化下离线项二阶主导、无发散"],
    ["件 F 形态 B", "|S_a|", "X=10⁸ 扫 a", "≈2.05", "素数项窄带有界（跨 λ 一致）"],
]
add_table(hdr1, rows1, widths=[2.8, 3.6, 2.6, 2.4, 3.2])
para("注：件 E=数值件 E（T=8×10⁵ 素数项实测）；件 F=数值件 F（S7.2，筛素数至 10⁸）。",
     size=9, indent_chars=0, space_after=6)
para("读数有三。其一，件 E：|S_final|/N_{L}=4.0×10^{−8}——素数项比主项小 7–8 个量级，离线项在 "
     "T=8×10^{5} 高度已可忽略；其二，件 F 主实验 A：|S_{a}|/N_{L} 随截断 X 单调衰减 2.04×10^{−4}→"
     "1.0×10^{−8}，快于 X^{−1/2}——SW 型压制在超支撑场景下同样生效（无核宽诱发发散）；其三，件 F "
     "形态实验 B：δS 与 ½K″(0)(aδ)²T_{2} 比值恒为 1.000（aδ≤3×10^{−3}）——核窄化下离线项二阶"
     "主导、一阶恒零，离线项的核宽依赖为收缩型 (aδ)² 而非发散。")

# ---------- 5 图 ----------
h1t("5　实测图形")
p = doc.add_paragraph()
p.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = p.add_run()
run.add_picture(FIG, width=Cm(14.0))
caption("图 1　数值件 F 双子图（S7.2 复用）：左=素数项 |S_a|/N_L 随截断 X 单调衰减；右=形态实验 B："
        "偶核一阶恒零、二阶主导 δS≈½K″(0)(aδ)²T₂——离线项跨尺度、跨核宽一致")
para("图 1 左：|S_{a}|/N_{L} 随 X（10^{4}→10^{8}）单调衰减两个量级以上——素数项在超支撑下的 SW 压制"
     "跨尺度成立；图 1 右：δS 与 ½K″(0)(aδ)²T_{2} 的对数比沿参考线（比值 1.000）——核窄化不引"
     "发离线项发散，标度 (aδ)² 收缩。")

# ---------- 6 结论 ----------
h1t("6　结论与判定")
para("骨头 3（N3）击破完成。")
para("（1）理论：BGS 余项结构拆解——两处来源（引理 4 截断误差、R(x,T) 素数项积分）均不含核；"
     "引理 5 余项 O(T√logT) 对 supp⊂[−1,1] 的一切核一致；N1 缩放保持 ⟹ 配对公式层跨 λ 一致。"
     "定理 N3：(i) 配对公式余项一致；(ii) 素数项 SW 压制常数只依赖模 5 与 T（不依赖 a）；(iii) "
     "离线总余项 R_{off}=O(1/√logT)·N_{L} 跨 λ 一致。")
para("（2）数值：件 E（|S_final|/N_{L}=4.0×10^{−8}）、件 F 主实验 A（|S_{a}|/N_{L} 单调衰减至 "
     "1.0×10^{−8}）、形态实验 B（δS/二阶参考=1.000）——离线项跨尺度、跨核宽一致，无发散迹象。")
para("（3）对推 1：三块骨头齐——N1（配对公式层缩放自同构，S7.3）、N2（ε–λ 联动，S7.4）、N3 "
     "（离线项一致，本档）。A(K_{λ,ε})−1=0.16a³+O((logT)^{−1/2})→0 全程闭合，无速度竞争。")
para("（4）诚实边界：L 版 BGS 型配对公式仍是显式假设（S7.1）；跨 λ 一致性在 BGS 的无条件结构内"
     "成立，但 L 版（χ₅ 模 5）下的 SW 常数尚未显式化——留待 S7.1 Stage 3+ 三引理（Abel 求和、"
     "K̂_{a} 一致界、N_{L} 对数下界）形式化时给出。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] Baluyot D, Goldston D A, Suriajaya A I, Turnage-Butterbaugh C L. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（定理 1 证明 (2.18)/(2.19)、引理 4 截断 Z=T log²T、引理 5 (3.4)）.",
    "[2] 攻防 XLII-S7.1（d1 已交付）：形式化证明 Lean 落地——L 版 BGS 型配对公式假设、§7.1 Stage 3+ 三件套挂清单、数值件 E（|S_final|/N_L=4.0e-8@T=8e5）.",
    "[3] 攻防 XLII-S7.2（d1 已交付）：数值件 F——素数项 |S_a|/N_L 单调衰减、形态实验 B（δS 与 ½K″(0)(aδ)²T₂ 比值 1.000、敏感量 (aδ)² 修正）.",
    "[4] 攻防 XLII-S7.3（d1 已交付）：骨头 1——BGS 引理 5 超支撑推广（缩放自同构 r̂_a(z)=r̂(az)、配对公式层成立）.",
    "[5] 攻防 XLII-S7.4（d1 已交付）：骨头 2——ε–λ 联动（支撑容忍 ε=O(a)、有效核宽标度律 0.16(a+2ε)³）.",
    "[6] 攻防 XLII-S4（d1 已交付）：正向构造数值定锚——GUE2(a)−1≈0.16a³ 恒正律.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
