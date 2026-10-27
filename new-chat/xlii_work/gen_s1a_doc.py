# -*- coding: utf-8 -*-
"""攻防 XLII S1a 落档：Parseval 归因——配对谱超出量 δF/δR 的分解与核依赖。
数据：qrh_work/xlii_s1a.json；图：xlii_s1a_fig1.png / xlii_s1a_fig2.png。
"""
import json
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLII-S1a-Parseval归因-δFδR分解与核依赖.docx"

s1a = json.load(open(QRH + r"\xlii_s1a.json", encoding="utf-8"))

doc = Document()

# ---------- 页面 ----------
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
sec.left_margin = sec.right_margin = sec.top_margin = sec.bottom_margin = Cm(2.5)

# ---------- 样式 ----------
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

def add_picture_centered(path, width_cm):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    run = p.add_run()
    run.add_picture(path, width=Cm(width_cm))
    return p

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
para("路2攻防XLII—S1a：Parseval 归因——配对谱超出量 δF/δR 的分解与核依赖",
     style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("（S0 数值定向的归因补全：A−GUE 内禀化、fejer 选择支撑、衰减律判别挂 S2）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S1a 数值验证", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 24 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S1a 完成配对口径的 Parseval 归因数值实验：把 S0 中配对常数偏差 A−GUE "
     "归因到谱内禀量 δF/δR。口径：配对核 F(α)（u=|δ|ρ(t_mid) 的傅里叶变量）与 R(u)；"
     "δF=F−F_GUE（ζ 999354 根、L(χ₅) 1149836 根，T=6×10⁵）。结果：(i) δF 谱全负（ζ/L 一致，"
     "周期性波动，超 GUE 排斥）；(ii) δR(u)=R_obs−2R_GUE 呈三区结构：近端负、中段正、远端负；"
     "(iii) Parseval 恒等式匹配带成立：D_actual=∫δF·核 与 D_parseval=∫δR·核 在 α≈0.45 处比率 "
     "0.997（ζ），宽 α 端受截断伪影偏离；(iv) 核族修正后三族偏差全负，|sinc|>|gauss|>|fejer|"
     "（ζ/L 一致）——支撑 XLI 选 fejer 窄核；(v) 衰减律未决：5 段斜率 −2~−5、第四段反弹，"
     "单 T 前缀无法分辨 1/logT 对 1/√logT——判别挂 S2(ii)。判定：A<1 系谱内禀排斥而非核伪影，"
     "S0 的 A(λ) 全曲线贴 GUE 获归因支持。", space_after=6)

para("关键词：Parseval 归因；配对谱超出量 δF/δR；超 GUE 排斥；核族偏序；衰减律判别",
     space_after=10)

# ---------- 1 承接与主线 ----------
h1t("1　承接与主线")
h2t("1.1　S0 之后：为何需要归因")
para("攻防 XLII S0（d1 已交付）给出「干到 1」的数值定向：配对常数 A(λ) 全尺度贴双侧 GUE、"
     "窄端单调→1、s<0.01 计数 0。但 A−GUE 的偏差本身是「现象」而非「解释」：它可能来自谱的"
     "内禀排斥（超 GUE），也可能只是核构造/有限 T 的伪影。S1a 的 Parseval 归因把偏差分解到"
     "谱内禀量 δF/δR，回答「A<1 从哪来」。")
h2t("1.2　S1a 在「干到 1」链中的位置")
para("XLI 桥：λ_eff(T)→∞ 全尺度 GUE 配对 ⟹ 配对常数 A→1 ⟹ 在线简单零点比例 ≥1−o(1)。"
     "S0 钉住 A(λ) 数值形态，S1b 给出定理骨架（(H2′_λ) 下 A=1+o(1)）与 p 量化，S2(i) 判定 "
     "x-口径为弱探针、必须走配对口径。S1a 在这两者之间补足归因层：确认配对口径看到的偏差"
     "是谱内禀的，且 fejer 窄核（XLI 的最优核）的选取不是自欺欺人（见 3.4）。")

# ---------- 2 口径与设计 ----------
h1t("2　口径与设计")
h2t("2.1　配对核与 GUE 基准")
para("配对相关：F(α) 为 u=|δ|ρ(t_mid) 的傅里叶变量（δ 为相邻零点间距、ρ 为局部密度）；"
     "R(u) 为规范化配对密度。GUE 基准 F_GUE（正弦核谱）与 2R_GUE（显式公式中的 2 重数）；"
     "实测偏离量 δF=F−F_GUE、δR=R_obs−2R_GUE。数据：T=6×10⁵、LOW=300、ζ 999354 根、"
     "L(χ₅) 1149836 根；配对直方图 half=8.0、binw=0.002；fejer 核可复现 S0 的 A 值"
     "（reproduce_v3_fejer=true）。")
h2t("2.2　Parseval 归因")
para("配对常数对核的依赖写为卷积：A−GUE2 = ∫δF(α)·核(α) dα（谱侧）与 = ∫δR(u)·核(u) du "
     "（距离侧）。Parseval 恒等式要求两式相等（D_actual=∫δF·核，D_parseval=∫δR·核）。"
     "逐 α 扫描 α∈{0.1,...,2.0} 13 点，比较 D_actual 与 D_parseval：匹配带成立处说明"
     "谱侧与距离侧归因一致。")
h2t("2.3　核族与核匹配基准")
para("核族：fejer、sinc、gauss（宽度 α∈{0.3, 0.5, 1.0}）。GUE2_K 为核匹配基准（同核宽下 GUE "
     "谱的 A_K），核族偏差 A_K−GUE2_K 修正了核宽带来的系统差，直接比较三族在相同口径下的"
     "偏离方向与大小。")

# ---------- 3 结果 ----------
h1t("3　结果")
h2t("3.1　δF 谱全负（图 1 左）")
add_picture_centered(QRH + r"\xlii_s1a_fig1.png", 14.5)
caption("图 1　S1a 配对归因主图。左：δF(α)=F−F_GUE（ζ 黑、L(χ₅) 红），全负区间=谱中超 GUE 排斥；"
        "右：δR(u)=R_obs−2R_GUE（ζ 黑、L 红），近端负/中段正/远端负三区结构")
para("左面板：δF 在 α∈[0,3] 全程为负（0 点水平虚线以下），ζ 与 L 形态一致——配对谱超出量"
     "系统性低于 GUE，即「超 GUE 排斥」；周期性波动来自有限高度下配对密度的振荡结构。"
     "全负性排除「部分 α 段存在 GUE 缺失排斥」的混合图像，A<1 是整体谱行为。")
h2t("3.2　δR 三区结构（图 1 右）")
para("右面板：δR(u) 呈三区——近端（小 u）负（短程排斥强于 GUE）、中段正（排斥盈余回流）、"
     "远端负（长程振荡）。ζ 与 L 同构。三区结构与 δF 全负共同刻画谱内禀排斥的完整轮廓；"
     "近端负区是 A<1 的直接来源，中段正是 Parseval 匹配带平衡项（见 3.3）。")
h2t("3.3　Parseval 恒等式匹配带（表 1）")
caption("表 1　Parseval 归因对照：D_actual=∫δF·核 对 D_parseval=∫δR·核（ζ/L，α=0.1~2.0；比率=parseval/actual）")
alphas = ["0.1", "0.15", "0.2", "0.25", "0.3", "0.35", "0.4", "0.45", "0.5", "0.75", "1.0", "1.5", "2.0"]
rows1 = []
for a in alphas:
    da = s1a["D_actual"]["zeta"][a]; dp = s1a["D_parseval"]["zeta"][a]
    daL = s1a["D_actual"]["L"][a]; dpL = s1a["D_parseval"]["L"][a]
    r = [a, "%.1e" % da, "%.1e" % dp, "%.3f" % (dp / da), "%.1e" % daL, "%.1e" % dpL, "%.3f" % (dpL / daL)]
    rows1.append(r)
add_table(["α", "D_actual ζ", "D_parseval ζ", "比率 ζ", "D_actual L", "D_parseval L", "比率 L"], rows1)
para("", indent_chars=0, space_after=2)
para("匹配带：ζ 在 α∈[0.3,0.5] 段 D_actual≈D_parseval（α=0.45 处比率 0.997，最接近 1）；"
     "L 的匹配带略宽、常数水平更高（α=0.45 比率 0.935）。宽 α 端（α≥1）D_actual 与 D_parseval "
     "系统性分离：D_actual 继续增长而 D_parseval 饱和——截断伪影（γ≤T 的有限高度）在宽核下"
     "进入谱侧积分。匹配带的成立是「A−GUE 可归因」的数值保证。")
h2t("3.4　核族修正后偏差全负（表 2、图 2 右）")
caption("表 2　核族偏差 A_K−GUE2_K（核匹配基准，全负；ζ/L 一致）")
rows2 = []
for a in ("0.3", "0.5", "1.0"):
    for fam in ("zeta", "L"):
        v = s1a["kernel_family"][fam][a]
        rows2.append(["ζ" if fam == "zeta" else "L", a,
                      "%.5f" % v["fejer"], "%.5f" % v["sinc"], "%.5f" % v["gauss"]])
add_table(["族", "核宽 a", "fejer", "sinc", "gauss"], rows2)
para("", indent_chars=0, space_after=2)
para("三族偏差全负（ζ/L 一致），且 |sinc|>|gauss|>|fejer| 严格偏序——核越宽、负偏离越深"
     "（sinc 最宽、fejer 最窄）。含义：(i) 超 GUE 排斥是核无关的普适现象（全负）；"
     "(ii) 窄核 fejer 的偏差绝对值最小——XLI 选 fejer_a0.5 不是「自欺欺人」地挑出 A≈1.008："
     "它是偏差最小的合法选择，定理只需一个核满足 A≤1.125；(iii) 核匹配口径下 L 族比 ζ 族"
     "偏离更深（同核宽），与 3.1 中 δF 幅度一致。")
h2t("3.5　衰减律未决（图 2 左）")
add_picture_centered(QRH + r"\xlii_s1a_fig2.png", 14.5)
caption("图 2　S1a 辅助图。左：Decay law——5 段 log|A_seg−GUE2| 对 log(log T_seg)，段太窄、"
        "第四段反弹（unresolved: need cross-T dataset）；右：核族偏差 A_K−GUE2_K（核匹配）全负，"
        "6 曲线随核宽增大下降、L 更陡")
para("左面板：|A_seg−GUE2| 的对数随 log(log T_seg) 下降，5 段斜率 −2~−5（ζ 0.3 段 −4.94、"
     "0.5 段 −3.97、1.0 段 −3.10、2.0 段 −2.11；L 同向），但第四段出现反弹——5 个 T 段过窄、"
     "单 T 前缀无法分辨 1/logT 对 1/√logT 的指数结构。这正是 S2(ii) 跨 T 衰减律判别的任务"
     "（需 T=10⁵/2×10⁵/4×10⁵/8×10⁵ 新零点数据）。")

# ---------- 4 判定 ----------
h1t("4　判定")
h2t("4.1　A<1 内禀化")
para("δF 全负 + 核族全负（核无关）+ Parseval 匹配带：S0 中 A(λ)<1 归因为谱内禀超 GUE 排斥，"
     "非核构造或有限 T 伪影。匹配带之外的宽 α 偏离是截断伪影，方向已知、量级受控。")
h2t("4.2　fejer 选择获支撑")
para("三族偏差 |sinc|>|gauss|>|fejer|：窄核 fejer 的系统偏差最小，是「干到 1」的合法工具；"
     "XLI 定理只要求存在一个核满足 A≤1.125——S1a 把「为什么是 fejer」从经验选择升级为"
     "数值偏序证据。")
h2t("4.3　衰减律判别归 S2(ii)")
para("5 段斜率 −2~−5 与 seg4 反弹：单 T 前缀信息量不足。衰减律（1/√logT 对 1/logT）直接决定 "
     "S1b 的速率结构 (logT)^{−15/7} 是否升级——挂 S2(ii) 跨 T 数据，不在 S1a 内强推。")

# ---------- 5 诚实披露与开放问题 ----------
h1t("5　诚实披露与开放问题")
para("① 衰减律判别未决：5 段过窄、seg4 反弹，单 T 前缀无法分辨 1/logT 对 1/√logT——"
     "判别任务整体移交 S2(ii)；② δR 三区结构为 u 网格上的定性轮廓（网格 0.001~0.5、binw 0.002），"
     "不声明精确区界；③ Parseval 匹配带之外的宽 α 偏离系截断伪影（γ≤T），未做尾部分离；"
     "④ dF 谱的周期性波动为有限高度振荡，其幅相结构未建模；⑤ 核匹配基准 GUE2_K 本身依赖"
     "核宽口径，偏序结论（全负、|sinc|>|gauss|>|fejer|）对口径稳健，但绝对值随口径漂移。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] S1a 数值件（本工作，可复跑）：qrh_work/xlii_s1a.py + xlii_s1a.json + xlii_s1a_fig1.png + xlii_s1a_fig2.png（Parseval 归因：δF 全负、δR 三区、匹配带 α≈0.45 比率 0.997、核族偏序 |sinc|>|gauss|>|fejer|、衰减律 5 段斜率 −2~−5 未决）；零点数据 zeros_T6e5.npz（T=6×10⁵、ζ 999354 根、L(χ₅) 1149836 根）.",
    "[2] 攻防 XLII-S0（d1 已交付）：全尺度 GUE 配对与在线比例 1−o(1)——A(λ) 全曲线、s<0.01 计数 0、S0 数值定向.",
    "[3] 攻防 XLII-S1b（d1 已交付）：λ(T) 构造与核依赖常数 p 的量化——定理 XLII.1 条件式、(H2′_λ)、p 量化两段.",
    "[4] 攻防 XLII-S2(i)（d1 已交付）：Weil 实部口径注入敏感性——x-口径弱探针、左尾威胁闭合链、配对口径为强探针.",
    "[5] 攻防 XLI（d1 已交付）：拟随机并集定理条件形态——7/8 门槛、fejer_a0.5 最优核、分解论证.",
    "[6] 攻防 XL（d1 已交付）：配对侧无条件界的理论构造——0.6725 常数缺口、1/√logT 技术极限、开放方向 (a)(b)(c).",
]
for rtext in refs:
    p = para(rtext, indent_chars=0, space_after=2)
    p.paragraph_format.line_spacing = 1.0

doc.save(TARGET)
print("saved:", TARGET)
