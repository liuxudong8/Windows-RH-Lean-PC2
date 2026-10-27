# -*- coding: utf-8 -*-
"""攻防 XLII S2(i) 落档：Weil 显式公式实部口径注入敏感性（无模板创建）。
数据：qrh_work/xlii_s2i.json；图 xlii_work 的 qrh_work/xlii_s2i_fig.png。
"""
import json
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLII-S2(i)-Weil显式公式实部口径注入敏感性-与S1左尾威胁闭合链.docx"

s2 = json.load(open(QRH + r"\xlii_s2i.json", encoding="utf-8"))

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
para("路2攻防XLII—S2(i)：Weil 显式公式实部口径注入敏感性", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（N_off·δ²·(logx)² 累积可测性与左尾威胁闭合链）", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S2(i) 数值验证", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 24 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S2(i) 完成 Weil 显式公式实部口径的注入敏感性数值实验：量化「N_off 个零点带 "
     "β−1/2=δ 偏移时，实部口径统计量的累积可测性」。口径：归一化实部核 "
     "R(x)=Σ_γ Re(x^{iγ}/ρ)/x^{1/2}（ζ 999492 根、log x∈[4,30] 网格）；注入 N_off 个零点偏移 δ 后 "
     "Δ(x)=Σ_{N_off}(w^δ−w^0)，可测性指标 ρ₂=⟨Δ²⟩_x/⟨R²⟩_x（ρ₂≥1 即注入效应≥基线）。结果："
     "(i) 代表性（随机）形态下 ρ₂=C·δ²·(inv2_off/inv2_all)，C=458（本网格；解析与数值精确吻合，"
     "δ=1/logT、N_off=10⁵ 时 0.26 对 0.258）——1/logT 级偏移需约 20%~40% 零点散布才可测，"
     "Weil x-口径对大量小偏移是弱探针；(ii) 左尾（最小 γ）形态下 δ≥1/logT 时 N_off=10 即可测"
     "（ρ₂≈7），δ=0.3 时 ρ₂~10⁶（x^δ 调制的系统同相贡献）——左尾小 γ 若偏移立即被看见。"
     "判定：x-口径不足以单独支撑「在线性 1−o(1)」，S1b 的检测必须走配对口径（S0/S1a 的 A(λ) "
     "全尺度贴 GUE 为强探针）；与 S1（左尾 224 审计实证无信号）构成两向夹逼的左尾威胁闭合链；"
     "δ≲0.01 级偏移低于探测分辨率，与数值零点 β=1/2 至 10⁻⁹ 的事实相容。", space_after=6)

para("关键词：Weil 显式公式；实部口径注入敏感性；N_off·δ²·(logx)²；可测性边界；左尾威胁闭合链",
     space_after=10)

# ---------- 1 承接与主线 ----------
h1t("1　承接与主线")
h2t("1.1　S1b 之后：S2 数值验证")
para("攻防 XLII S1b（d1 已交付）完成「干到 1」的定理骨架：在 (H2′_λ)（λ_eff(T) 截断的 BGS 型"
     "配对公式）下取 λ_eff(T)=(logT)^q，配对常数 A=1+o(1)，经 XLI 桥得在线简单零点比例 ≥1−o(1)；"
     "p 量化（文献侧 + 数值侧）把条件收敛到单点 (H2′_λ)。S2 数值验证两件：(i) Weil 显式公式实部"
     "口径注入敏感性（本篇）——检验数值环境的检测工具对假设违规（离线零点）的探测能力；"
     "(ii) 跨 T 衰减律判别——1/√logT 对 1/logT 的误差结构判别，需跨 T 零点数据（待后续）。")
h2t("1.2　S1 左尾 224 审计回顾与衔接")
para("攻防 XXXVI（d1 已交付）S1 完成左尾 224 审计（威胁形态实证）：对 224 个最小虚部零点的偏移"
     "迹象做直接检查，未发现异常信号——真实数据左尾干净。S2(i) 补足其方法论侧：若左尾真实存在"
     "偏移（N_off 个、幅度 δ），Weil 实部口径能否看见？两向夹逼后，左尾威胁才能闭合。")

# ---------- 2 口径与设计 ----------
h1t("2　口径与设计")
h2t("2.1　Weil 实部核")
para("ψ 显式公式中零点项的实部（x 口径）：x^ρ/ρ 的实部对 β=1/2 的零点为 "
     "x^{1/2}[cos(γ log x)/2 + γ sin(γ log x)]/(1/4+γ²)。归一化核（去公共 x^{1/2}）")
para("R(x) = Σ_γ [cos(γ log x)/2 + γ sin(γ log x)]/(1/4+γ²)，", indent_chars=0, space_after=4)
para("γ 取正虚部零点（ζ 999492 根，[300,6×10⁵]）；正负成对因子 2 为公共常数，在相对量中消去。"
     "log x 网格取 [4,30]（27 点），截断伪影（γ≤T）与数值噪声并入基线，可测性判定用相对量保证公平。")
h2t("2.2　注入方案")
para("把 N_off 个零点改为 β=1/2+δ（人为构造，不改变真实零点）：核变为 "
     "w^δ(x)=x^δ[cos(γ log x)(1/2+δ)+γ sin(γ log x)]/((1/2+δ)²+γ²)，"
     "Δ(x)=Σ_{γ∈N_off}(w^δ−w^0)。两种注入形态：(a) min——取最小 γ 的 N_off 个（左尾威胁最大形态）；"
     "(b) rand——随机 N_off 个（代表性形态）。扫描 δ∈{0.01, 1/logT≈0.075, 0.1, 0.3}、"
     "N_off∈{10, 10², 10³, 10⁴, 10⁵}。")
h2t("2.3　可测性指标")
para("ρ₂(δ,N_off)=⟨Δ(x)²⟩_x/⟨R(x)²⟩_x。ρ₂≥1 ⟺ 注入效应≥基线（基线含真实零点求和与截断伪影），"
     "即该 (N_off,δ) 组合可被 Weil 实部口径数值检测。基线二矩实测 ⟨R²⟩_x=0.01677。")
h2t("2.4　解析预测")
para("大 γ、δ 小（x^δ≈1）、随机相位：w^δ−w^0≈δ[log x·A+cos]/(γ²)，A=cos/2+γ sin；"
     "⟨(w^δ−w^0)²⟩_x≈δ²·(229γ²+66)/γ⁴≈229δ²/γ²（⟨log x²⟩≈458），基线 ⟨R²⟩≈Σ_all 1/(2γ²)。故")
para("ρ₂ ≈ C·δ²·(inv2_off/inv2_all)，C=458（本网格），inv2_off=Σ_{γ∈N_off}1/γ²。", indent_chars=0,
     space_after=4)
para("数值自检（rand，δ=0.075，N_off=10⁵）：ρ₂=0.2599 对解析 458·0.075²·0.1=0.258——精确吻合，"
     "随机相位机制确认。min 形态大 δ 时 x^δ 线性近似失效（δ=0.3、log x=30 处 x^δ=e⁹），"
     "解析仅适用 δ≲0.1。")

# ---------- 3 结果 ----------
h1t("3　结果")
h2t("3.1　可测性矩阵（表 1）")
caption("表 1　注入可测性矩阵 ρ₂（T=6×10⁵，ζ；基线 ⟨R²⟩=0.0168；判定：ρ₂≥1 可测、0.1~1 边缘、<0.1 不可测）")
N0 = [10, 100, 1000, 10000, 100000]
rows1 = []
for mode, mname in (("min", "左尾 min"), ("rand", "随机 rand")):
    for delta in (0.01, 0.075, 0.1, 0.3):
        vals = s2["matrix_" + mode][str(delta)]
        r = [mname, str(delta)]
        for n in N0:
            v = vals[str(n)]
            r.append("%.4g" % v if v >= 1e-4 else "~0")
        last = vals[str(100000)]
        r.append("可测" if last >= 1 else ("边缘" if last >= 0.1 else "不可测"))
        rows1.append(r)
add_table(["形态", "δ", "N_off=10", "10²", "10³", "10⁴", "10⁵", "判定@10⁵"], rows1)
para("", indent_chars=0, space_after=2)
para("读数：(i) 左尾形态 δ≥0.075 时 N_off=10 即 ρ₂≈7~3×10⁶（可测）——左尾小 γ 若偏移立即被看见；"
     "(ii) 随机形态 δ=0.075 时 N_off=10⁵ 仅 ρ₂=0.26（不可测）——20%~40% 零点带 1/logT 偏移才可测；"
     "(iii) δ=0.01 两种形态均不可测（分辨率下限）；(iv) 左尾 ρ₂ 对 N_off 不单调（x^δ 调制与 γ 相位"
     "相互作用，非随机相位机制）。")
h2t("3.2　图 1 说明（注入可测性热力图）")
add_picture_centered(QRH + r"\xlii_s2i_fig.png", 14.5)
caption("图 1　注入可测性热力图（log-log）：ρ₂=⟨Δ²⟩_x/⟨R²⟩_x 对 (N_off, δ) 的依赖，T=6×10⁵。"
        "左：左尾形态（最小 γ 注入）；右：随机形态（代表性）。横轴 N_off（对数）、纵轴 δ（对数），"
        "色标 log10 ρ₂（蓝=不可测、红=可测），黑线为 ρ₂=1 可测性边界")
para("图 1 读法（逐项）：两面板共享色标与坐标约定。左面板（左尾形态）呈现明显的分层：顶部一行"
     "（δ=0.3）深红（ρ₂~10⁶），中部（δ=0.075、0.1）橙红（ρ₂~7~47），底部（δ=0.01）深蓝"
     "（ρ₂≤0.04）——且三档对 N_off 几乎不敏感（横向颜色无变化）：左尾注入的可测性由 δ 单独决定，"
     "N_off≥10 即饱和。黑色 ρ₂=1 边界位于 δ≈0.03~0.05 之间：δ 高于此即任何 N_off≥10 都进入可测区。"
     "右面板（随机形态）横向渐变明显：δ=0.3 行深红（N_off≥10² 可测），δ=0.1 行从 N_off=10⁴ 起橙色"
     "（N_off=10⁵ 时 ρ₂=1.05，恰跨边界），δ=0.075 行整体浅蓝（N_off=10⁵ 时 ρ₂=0.26，未达 1），"
     "δ=0.01 行全蓝（不可测）——随机形态的可测性强烈依赖 N_off，且 1/logT 级偏移在整个 N_off "
     "扫描范围内都不可测。两面板对照：同一 δ，左尾比随机敏感约 10⁴~10⁵ 倍（γ⁻² 加权的差异），"
     "证明 Weil x-口径的探测能力集中在低 γ 零点。")

# ---------- 4 判定 ----------
h1t("4　判定")
h2t("4.1　弱探针结论")
para("x-口径（ψ 型实部核）对代表性分布的 1/logT 级偏移需要约 20%~40% 零点才可测。数学根源："
     "随机相位下 Δ² 只累积对角项，γ⁻² 加权使高 γ（绝大多数零点所在）贡献可忽略；而偏移量级 "
     "δ~1/logT 又使每个注入零点的相对贡献 ~δ²(log x)² 远小于 1。因此 Weil x-口径不足以单独支撑"
     "「在线性 1−o(1)」——若把它当探针，只能排除「大量大偏移」，对「少量小偏移」失明。")
h2t("4.2　左尾威胁闭合链")
para("两向夹逼成立：(i) S1（攻防 XXXVI）224 个最小虚部零点直接审计无偏移信号；(ii) S2(i) 证明"
     "左尾小 γ 若真实偏移（δ≥1/logT，仅 10 个）会立即被 Weil 口径看见（ρ₂≥7）。左尾威胁在数值"
     "与方法论两侧同时闭合。")
h2t("4.3　分辨率下限与口径分工")
para("δ≲0.01（约 1/8 个 1/logT）任何形态不可测——低于探测分辨率，与数值零点 β=1/2 至 10⁻⁹ "
     "精度的事实相容，不构成矛盾。口径分工明确：x-口径是弱探针，S1b 依赖的在线性检测必须走配对"
     "口径——S0/S1a 的配对常数 A(λ) 全尺度贴 GUE（T=6×10⁵ 全曲线、窄端单调→1）才是强探针。"
     "x-口径弱敏感性不构成对 S1b 的威胁，反而排除「Weil 口径可独立验证前提」的错误预期。")

# ---------- 5 诚实披露与开放问题 ----------
h1t("5　诚实披露与开放问题")
para("① 基线含截断伪影（γ≤T）与数值噪声，未与真实信号分离——判定用相对量（ρ₂），公平但非绝对；"
     "② 解析常数 C=458 依赖本网格（log x∈[4,30]），换网格 C 变化但弱探针结论不变（γ⁻² 加权主导）；"
     "③ 左尾 δ=0.3 的 ρ₂~10⁶ 系 x^δ 大端调制（e^{δ·30}=e⁹）的系统同相贡献，非随机相位机制，"
     "仅作左尾极端敏感性的展示；④ 注入为人为构造、不改变真实零点——属方法论敏感性测试；"
     "⑤ S2(ii) 跨 T 衰减律判别（1/√logT 对 1/logT）未做，需跨 T 零点数据（T=10⁵/2×10⁵/4×10⁵/8×10⁵）"
     "——挂主线后续。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] S2(i) 数值件（本工作，可复跑）：qrh_work/xlii_s2i.py + xlii_s2i.json + xlii_s2i_fig.png（Weil 实部口径注入敏感性：可测性矩阵、ρ₂=C·δ²·(inv2_off/inv2_all)、C=458）；零点数据 zeros_T6e5.npz（T=6×10⁵、ζ 999492 根）.",
    "[2] 攻防 XXXVI（S1，d1 已交付）：左尾 224 审计——威胁形态实证（224 个最小虚部零点无偏移信号）.",
    "[3] 攻防 XLII-S1b（d1 已交付）：λ(T) 构造与核依赖常数 p 的量化——定理 XLII.1 条件式、(H2′_λ)、p 量化两段.",
    "[4] 攻防 XLII-S0（d1 已交付）：全尺度 GUE 配对与在线比例 1−o(1)——S0 数值定向（A(λ) 全曲线、超 GUE 排斥）.",
    "[5] 攻防 XLI（d1 已交付）：拟随机并集定理条件形态——7/8 门槛、fejer_a0.5 最优核、分解论证.",
    "[6] 攻防 XL（d1 已交付）：配对侧无条件界的理论构造——0.6725 常数缺口、1/√logT 技术极限、开放方向 (a)(b)(c).",
]
for rtext in refs:
    p = para(rtext, indent_chars=0, space_after=2)
    p.paragraph_format.line_spacing = 1.0

doc.save(TARGET)
print("saved:", TARGET)
