# -*- coding: utf-8 -*-
"""攻防 XLII · S4 落档：正向构造——窄核实测与配对常数残差结构，λ(T) 构造的数值定锚。
数据：qrh_work/xlii_s4a.json（α 预演）+ xlii_s4b.json（窄核实测）+ xlii_s4b_fig.png。
"""
import json, os
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S4-正向构造-窄核实测与配对常数残差结构-λ(T)构造的数值定锚.docx"
FIG = os.path.join(QRH, "xlii_s4b_fig.png")

s4a = json.load(open(os.path.join(QRH, "xlii_s4a.json"), encoding="utf-8"))
s4b = json.load(open(os.path.join(QRH, "xlii_s4b.json"), encoding="utf-8"))
r8 = s4b["rows"][0]
r6 = s4b["rows"][1]
AV = s4b["meta"]["A_grid"]
lp = s4b["lambda_path"]

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
para("路2攻防XLII—S4：正向构造", style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("（窄核实测与配对常数残差结构——λ(T) 构造的数值定锚）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S4 正向构造", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 25 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S4 完成正向构造的数值定锚：把 S1b 的 (H2′_λ)（λ_eff(T) 截断的 BGS 型配对公式）从"
     "「假设」推进为「构造出满足它的核与 λ(T)」的第一步。数值件 A（α 预演）：λ(T)=c(logT)^{−α}"
     "（α∈{1,15/7,3}）扫描显示 λ 落点 a~0.004~0.009 远在 S2(ii) 网格（a≥0.1）之下，幂律外推的"
     "跨 T 指数 β 混乱且符号翻转——外推不可靠，必须窄核实测。数值件 B（窄核专项，half=0.5、"
     "binw=0.0005，a∈{0.005,0.01,0.02,0.05,0.1,0.2}，T=8×10⁵/6×10⁵）：(1) GUE2(a)−1≈c₁a³，"
     "c₁=0.156~0.166——理论指数 3（换元 u=ax）数值确认，S1b §2.2 的 O(a³) 精确化；(2) "
     "Δ≈−c₁a³(1−ε)，残差比 ε=A−1/GUE2−1 由 0.78（a=0.2）单调降至 0.05（a=0.005）——A−1 是"
     "GUE2 偏差与配对误差两个同阶项的近乎完全抵消；(3) A−1=ε·c₁a³ 恒正（ζ 双 T 一致）。判定："
     "(H2′_λ) 的数值形态成立——窄核端 |A−GUE2|≈0.16a³（C(a)≈0.16a³√logT，随谱支撑增长衰减），"
     "S1b 表 2 的平衡结构（BGS 误差项与 GUE2 项同阶）确认；(logT)^{−15/7} 为保守下界，λ³ 主导给出"
     "可收紧方向（速率指数 ≥3α=45/7≈6.43）；ε(a→0) 极限为剩余自由度——超密度假设的构造落点。"
     "桥接攻防 XXXIX：配对侧余项常数级 10⁻³~10⁻² 的窄核极限即 −c₁a³；在线比例桥（0.6725）与"
     "干到 1（A→1）共用配对侧结构。诚实边界：λ 路径在统计噪声带下缘，速率直接数值验证不可能；"
     "ε(a→0) 极限开放；L 族窄核 Δ 转正未解释。", space_after=6)

para("关键词：正向构造；λ(T)；窄核实测；残差比 ε；配对常数；超密度假设", space_after=10)

# ---------- 1 承接与任务 ----------
h1t("1　承接与任务")
h2t("1.1　S 系列坐标与 S4 的位置")
para("S0（全尺度 GUE 配对数值定向）→ S1a（Parseval 归因，δF 谱全负）→ S1b（λ(T) 定理骨架："
     "(H2′_λ) 下 A=1+o(1)、速率 (logT)^{−15/7}）→ S2(i)（Weil 实部口径弱探针判定 + 左尾威胁闭合）→ "
     "S2(ii)（跨 T 衰减律判别：误差通道钉死为 BGS 1/√logT，速率不升级、与 λ 通道正交）→ S3（Δ 常数"
     "指纹排除交叉验证）。主线下一步按文档判定为转回正向下界构造：S4 正向构造——把 S1b 的 (H2′_λ) "
     "从假设推进为「构造出满足它的核与 λ(T)」，使 A(λ;T)→1 的速率真正达到 (logT)^{−15/7}。")
h2t("1.2　任务与双路径")
para("两条路径：(i) 桥补严——在线比例桥余项精细形态（攻防 XXXIX 余项界 0.27 的松弛定位）与干到 1 "
     "的配对常数结构会合，把「理论余项界 → 正向下界窗口」的桥补严；(ii) λ(T) 显式候选 + 数值预演——"
     "λ(T)=c(logT)^{−α}（α>1/2 才压得过 √logT 误差），在 α∈{1,15/7,3} 验证 A(λ(T);T)→1 的实测轨迹"
     "与 (logT)^{−15/7} 的贴合度。本攻防执行数值预演（数值件 A）与窄核实测（数值件 B），并给出"
     "(H2′_λ) 的数值形态判定。")

# ---------- 2 数值件 A：α 预演 ----------
h1t("2　数值件 A：α 预演与网格缺口暴露")
h2t("2.1　方法")
para("λ(T)=c(logT)^{−α}，α∈{1, 15/7≈2.143, 3}，c∈{0.5,1,2}。A(λ;T) 由 S2(ii) 六核网格"
     "（a∈{0.1,0.2,0.3,0.5,1.0,2.0}，八档 T）的幂律外推重构：GUE2(a)−1 对 a 拟合幂律（全网格指数 "
     "kg≈2.74），Δ(a;T)=A−GUE2 对 a 拟合幂律（指数 q 逐 T 标定），再取 λ(T) 处的值。对每 (α,c) 拟合 "
     "log|A−1| 对 log(logT) 的斜率 β。")
h2t("2.2　结果与判读")
para("ζ 族 Δ 的幂律指数 q 跨 T 漂移 2.22~2.45（L 族 2.26~3.67，波动更大）；α=2.14 与 3 时 A−1 跨 T "
     "衰减指数 β 虚高（−8~−20）且符号翻转（mixed）；α=1 时 β 混乱（−0.5~+4.8）。原因：λ(T) 在 "
     "T∈[10⁴,8×10⁵] 落入 a∈[0.0037,0.0086]，远在网格最小核 0.1 之下——A−1 是两个外推同阶项"
     "（GUE2−1≈c₁λ³ 与 |Δ|≈c₂λ^q）的小差，1e-8~1e-11 量级已远低于实测可测精度（A 的统计涨落 "
     "~1e-4）。β 值系外推模型的数学产物，不承载物理。")
h2t("2.3　判定")
para("外推不可靠——λ 路径的实测需窄核直接采样。数值件 B 的任务：把核宽降到 λ 路径的落点区间"
     "（a~0.005~0.2），直接测 A、GUE2−1、Δ 与 A−1 的真实标度。")

# ---------- 3 数值件 B：窄核实测 ----------
h1t("3　数值件 B：窄核实测（λ 路径直接验证）")
h2t("3.1　口径与数据")
para("窄核配对直方图 half=0.5、binw=0.0005（S2(ii) 全局口径 half=40/binw=0.02 的窄核细化）；"
     "核宽 a∈{0.005,0.01,0.02,0.05,0.1,0.2}；主档 T=8×10⁵（ζ 1 369 141 根、L(χ₅) 1 570 076 根），"
     "复核档 T=6×10⁵（ζ 999 354 根、L 1 149 836 根）；截断 [300,T]，GUE2 基准同款半无穷积分"
     "（R=60）。窄核下 u>0.5 处 K=sinc²(πu/a) 已指数级衰减，half=0.5 截断与 GUE2 全积分等价。")
h2t("3.2　GUE2−1≈c₁a³：理论指数 3 的数值确认")
para("换元 u=ax 给出 GUE2(a)−1=2a∫₀^∞(1−sinc²(πax))sinc⁴(πx)dx，a→0 主项 (2π²a³/3)·∫x²sinc⁴(πx)dx"
     "——指数 3。窄核实测（T=8×10⁵）：c₁=(GUE2−1)/a³ 在 a∈[0.005,0.2] 六档稳定于 "
     "0.156~0.166（a=0.005 处 0.160、a=0.2 处 0.156）。S1b §2.2 的 O(a³)（引用 S0 实测）获得独立"
     "窄核口径的精确标定：GUE2(a)−1≈0.16a³。")
h2t("3.3　Δ≈−c₁a³(1−ε)：A−1 的残差结构")
para("Δ=A−GUE2 在窄核端与 GUE2−1 近乎完全抵消：Δ/a³ 由 −0.152（a=0.005）升至 −0.035（a=0.2）；"
     "残差比 ε=A−1/GUE2−1 由 0.78（a=0.2）单调降至 0.05（a=0.005）——A−1=ε·c₁a³，恒正（ζ 双 T "
     "一致）。两个同阶项（GUE2 偏差项 +c₁a³ 与配对误差项 −c₁a³(1−ε)）的同幅相消是 S4 的核心结构"
     "发现：配对误差在窄核端的极限形态是 −GUE2−1（而非独立幂律）。")
h2t("3.4　L 族窄核 Δ 转正")
para("T=8×10⁵ 处 L(χ₅) 的 Δ 在 a=0.02/0.05/0.1 转正（+3.75×10⁻⁷/+1.87×10⁻⁶/+1.19×10⁻⁵），"
     "a=0.005/0.01/0.2 为负。与 ζ 的恒负不同——L 族窄核窗口配对样本更稀（L 密度低 ~1.15 倍），"
     "且跨族互斥在窄核窗口的表现未独立建模。诚实披露：该转正为统计涨落或结构效应未决，不影响 "
     "ζ 族的残差结构判定，但提醒 ε 的 L 族标定不可靠。")
h2t("3.5　λ 路径落点与可测性")
para("λ(T)=(logT)^{−15/7} 在 T∈[10⁴,8×10⁵] 落入 a∈[0.0037,0.0086]（T=10⁴：8.6×10⁻³；T=8×10⁵："
     "3.7×10⁻³）——恰在可测噪声带下缘：A−1~1×10⁻⁹（a=0.005）低于配对计数的泊松涨落（n~1.4×10⁶，"
     "A 的统计精度 ~10⁻⁷~10⁻⁸）。结论：速率本身无法直接数值验证；但 A−1 的量级上界由 GUE2 偏差项"
     "给出——A(λ;T)−1≤0.16λ³<1.6×10⁻⁷（T≥10⁴），构造的可行性不受噪声限制。")

# ---------- 表 1 ----------
caption("表 1　窄核专项读数（T=8×10⁵；ζ 1 369 141 根、L(χ₅) 1 570 076 根；half=0.5、binw=0.0005）")
hdr = ["量", "a=0.005", "a=0.01", "a=0.02", "a=0.05", "a=0.1", "a=0.2"]
rows_tab = []
for fam in ("zeta", "L"):
    lab = "ζ A−1" if fam == "zeta" else "L A−1"
    rows_tab.append([lab] + ["%+.1e" % r8["A_minus_1"][fam][str(a)] for a in AV])
    rows_tab.append(["ζ Δ" if fam == "zeta" else "L Δ"] + ["%+.1e" % r8["Delta"][fam][str(a)] for a in AV])
add_table(hdr, rows_tab, widths=[2.6, 2.1, 2.1, 2.1, 2.1, 2.1, 2.1])
para("注：GUE2−1 的 c₁=(GUE2−1)/a³ 在六档为 0.160/0.166/0.166/0.165/0.161/0.156（ζ 与 L 共用同一 "
     "GUE2 基准）。ε=A−1/GUE2−1（ζ）：0.05/0.115/0.215/0.63/0.73/0.78。", size=9, indent_chars=0, space_after=6)

# ---------- 图 1 ----------
pfig = doc.add_paragraph()
pfig.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = pfig.add_run()
run.add_picture(FIG, width=Cm(15.5))
pfig.paragraph_format.keep_with_next = True
caption("图 1　S4 窄核实测三子图：左 log-log 标度（GUE2−1、A−1、|Δ|，斜率 3 参考）；中 ε(a)=A−1/"
        "GUE2−1 残差剖面（T=8×10⁵/6×10⁵，ζ 蓝、L 红）；右 λ(T)=(logT)^{−15/7} 路径落点与噪声带")

# ---------- 4 理论桥 ----------
h1t("4　理论桥：配对侧余项结构与 (H2′_λ) 的数值形态")
h2t("4.1　攻防 XXXIX 的余项界松弛定位")
para("攻防 XXXIX（d1 已交付）把在线比例桥的 Levinson 理论余项界 O(1/√logT)≈0.27 分解定位："
     "密度侧 3.4×10⁻⁵（T 无关）、配对侧 ∫C(h)dh≈±10⁻³ 常数级（T 无关）、素项侧 10⁻⁵~10⁻³——"
     "270 倍松弛集中在配对侧（Montgomery 配对相关误差项），且配对侧负偏有确定性结构（跨族互斥 "
     "14σ，与 Δ 常数定律同源）。正向下界窗口：配对侧无条件界压到 10⁻² 级 ⟹ 在线比例 "
     "≥0.6725−O(10⁻²) 成为严格定理。")
h2t("4.2　配对侧余项的窄核极限")
para("本攻防窄核实测给出配对侧余项的窄核极限形态：Δ≈−c₁a³(1−ε)→−0.16a³（a→0）——即配对侧"
     "偏差与 GUE2 偏差项同阶同幅（ε→0 不可排除，A−1 恒正）。这统一了两个视角：XXXIX 的配对侧"
     "常数级 10⁻³~10⁻² 对应中等核（a~0.1~0.2），其窄核极限即 −GUE2−1——跨族互斥的负偏结构在"
     "窄核窗口表现为对 GUE2 偏差的近乎完全补偿。在线比例桥（0.6725 的 Levinson 余项）与干到 1 "
     "（A(λ)→1）共用这一配对侧结构。")
h2t("4.3　(H2′_λ) 的数值形态：平衡结构确认")
para("(H2′_λ) 断言 |A(a;T)−GUE2(a)|≤C(a)(logT)^{−1/2}、C(a)=O(λ_eff^p)。窄核实测给出 "
     "|A−GUE2|≈0.16a³（a∈[0.005,0.2] 六档）——C(a)≈0.16a³√logT，随谱支撑增长衰减（p_eff<0 的"
     "窄核极限），满足任意多项式界。S1b 表 2 的平衡结构（BGS 误差项 (logT)^{pq−1/2} 与 GUE2 偏差项 "
     "(logT)^{−3q} 同阶平衡，q=5/7）获窄核直接支持。")
h2t("4.4　速率判定：(logT)^{−15/7} 为保守下界")
para("A(λ;T)−1=ε·c₁λ³（ζ 实测形态）。取 λ=(logT)^{−15/7}：λ³=(logT)^{−45/7}≈(logT)^{−6.43}——"
     "比 (logT)^{−15/7}≈(logT)^{−2.14} 快 4.3 个对数指数级。S1b 的速率是 (H2′_λ) 平衡推导的保守下界；"
     "S4 的残差结构给出收紧方向：若 ε(a)→ε*>0（常数残差），速率指数=3α（α=15/7 时 6.43）；若 "
     "ε(a)→0（超收敛），速率更快、由更高阶项或误差通道限制。ε 的 a→0 极限即超密度假设 (H2′_λ) 的"
     "构造落点——这是 S4 留给下一阶段的唯一开放自由度。")

# ---------- 5 正向下界窗口判定 ----------
h1t("5　正向下界窗口判定")
h2t("5.1　已钉死的事实")
para("① GUE2(a)−1≈0.16a³（指数 3 理论确认，c₁ 六档稳定 0.156~0.166）；② 窄核端配对误差 "
     "Δ≈−c₁a³(1−ε)，A−1=ε·c₁a³ 恒正（ζ 双 T）；③ (H2′_λ) 数值形态成立（|A−GUE2|≈0.16a³，"
     "平衡结构确认）；④ A−1 速率上界 0.16λ³，λ=(logT)^{−15/7} 时 A−1≤1.6×10⁻⁷（T≥10⁴）。")
h2t("5.2　剩余自由度与下一步")
para("ε(a→0) 极限（→0 超收敛 vs →ε*>0 常数残差）为 (H2′_λ) 的构造落点。实测 ε(0.005)=0.05 仍在降，"
     "但不能确认极限为 0（噪声带限制）。定理级推进需 ε 的显式控制——对应 XXXIX §6 的正向下界窗口："
     "配对侧无条件界压到 10⁻² 级（BGS 型配对定理 ζ_K 并集版 / 跨族 f(0) 结构专用界）。数值上可先做"
     "ε(a) 的多 T 窄核系统标定（更大 T≥2×10⁶ 提升噪声极限 2~3 个量级）。")

# ---------- 6 诚实披露与开放问题 ----------
h1t("6　诚实披露与开放问题")
para("① λ 路径速率直接数值验证不可能——落点 a∈[0.0037,0.0086] 在泊松噪声带下缘（A−1~10⁻⁹ vs "
     "统计 ~10⁻⁷~10⁻⁸），(logT)^{−15/7} 与更快速率的数值区分需 T≥10⁷ 或降噪手段；② ε(a→0) 极限"
     "开放——实测 0.05@a=0.005 仍在降，既不能确认 ε→0 也不能确认 ε→ε*>0；③ L 族窄核 Δ 转正未"
     "解释（统计样本稀 vs 跨族互斥窄核表现，见 3.4）；④ Δ 含 GUE2 有限窗残差与统计噪声未分离成分，"
     "c₁ 与 ε 为上界型标定；⑤ S4 为数值定锚而非定理——(H2′_λ) 仍为显式假设，构造完成度 = 数值形态"
     "+ 速率上界 + 平衡确认，不含定理级 ε 控制；⑥ λ(T) 的常数 c 未定（c∈{0.5,1,2} 对速率指数无影响，"
     "仅改变常数因子）。")

# ---------- 7 判定总结 ----------
h1t("7　判定总结")
para("S4（正向构造）完成数值定锚并落档。窄核实测（T=8×10⁵/6×10⁵，a∈[0.005,0.2]）钉死：(i) "
     "GUE2(a)−1≈0.16a³（理论指数 3 确认）；(ii) 配对误差窄核极限 Δ≈−c₁a³(1−ε)，A−1=ε·c₁a³ 恒正；"
     "(iii) (H2′_λ) 数值形态成立、S1b 平衡结构确认；(logT)^{−15/7} 为保守下界，λ³ 主导给出收紧方向"
     "（速率指数 ≥45/7≈6.43）；ε(a→0) 极限为超密度假设的构造落点。与攻防 XXXIX 会合：配对侧余项"
     "常数级偏差的窄核极限即 −GUE2−1，在线比例桥与干到 1 共用配对侧结构。主线下一步：ε 的定理级"
     "控制——配对侧无条件界理论构造（BGS 型 ζ_K 并集版 / 跨族 f(0) 专用界），或 ε(a) 多 T 系统标定。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（Prop 2.1、Lemma 3.1=BGS Lemma 5）——S1b/XL 期已核实.",
    "[2] Baluyot D, Goldston D A, Suriajaya A I, Turnage-Butterbaugh C L. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（Lemma 5：误差 O(1/√logT)）——S2(ii)/S4 理论锚.",
    "[3] 攻防 XLII-S0/S1a/S1b/S2(i)/S2(ii)/S3（d1 已交付）：全尺度 GUE 数值定向、Parseval 归因、λ(T) 构造与 p 量化、Weil x-口径弱探针、跨 T 衰减律判别、Δ 指纹排除交叉验证.",
    "[4] 攻防 XXXIX（d1 已交付）：在线比例桥余项精细形态——理论余项界 0.27 的松弛定位（配对侧 10⁻³~10⁻² 常数级、跨族互斥 14σ）与正向下界严格化窗口.",
    "[5] 本工作数值件（可复跑）：qrh_work/xlii_s4a.py + xlii_s4a.json（α 预演）、xlii_s4a2.py（幂律标度）、xlii_s4b.py + xlii_s4b.json + xlii_s4b_fig.png（窄核实测）；零点数据 zeta_T800000.npz/L_D5_T800000.npz（T=8×10⁵）、zeros_T6e5.npz（T=6×10⁵）.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
