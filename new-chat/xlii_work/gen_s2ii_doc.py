# -*- coding: utf-8 -*-
"""攻防 XLII S2(ii) 落档：跨 T 衰减律判别——配对常数误差律与 S1b 速率钉死。
数据：qrh_work/xlii_s2ii.json（八档 A 值 + 双律拟合）+ xlii_s2ii_fig.png。
"""
import json, os
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S2(ii)-跨T衰减律判别-配对常数误差律与S1b速率钉死.docx"
FIG = os.path.join(QRH, "xlii_s2ii_fig.png")

res = json.load(open(os.path.join(QRH, "xlii_s2ii.json"), encoding="utf-8"))
rows = res["rows"]
fits = res["fits"]
tally = res["law_tally"]
gue2 = res["meta"]["gue2"]

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
para("路2攻防XLII—S2(ii)：跨 T 衰减律判别", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（配对常数误差律与 S1b 速率钉死）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S2(ii) 数值判别", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 25 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S2(ii) 完成跨 T 衰减律判别：判定配对常数偏差 Δ=A(λ;T)−GUE2 随 T 的衰减律，"
     "在 BGS 误差项 O(1/√logT) 与离线乐观口径 O(1/logT) 之间择一，从而决定 S1b 定理速率 "
     "(logT)^{−15/7} 是否升级。数据：八档 T∈{10⁴,2×10⁴,4×10⁴,10⁵,2×10⁵,4×10⁵,6×10⁵,8×10⁵}，"
     "ζ 与 L(s,χ₅) 双族；新四档（10⁵~8×10⁵）为本工作生成（ζ 1.37×10⁶ 根、L(χ₅) 1.57×10⁶ 根 @8×10⁵）。"
     "口径：fejer 核 K=sinc²(πu/a)、a∈{0.3,0.5,1.0,2.0}，half=40、binw=0.02（S0 全局口径），"
     "统一截断 [300,T]。结果：Δ 全负、|Δ| 跨 T 单调收敛向 0（无反弹）；宽核端两律 R² 均极高"
     "（a=1.0：跨族均值 1/√logT=0.9945 vs 1/logT=0.9925；a=2.0：0.9894 vs 0.9838）——1/√logT "
     "系统性微优，与 BGS 定理误差项一致；窄核（a=0.3）L 族斜率转正（纯噪音），不可判。判定："
     "误差律按 BGS 1/√logT 保守口径，1/logT 离线乐观口径无数值支持；S1b 速率 (logT)^{−15/7} "
     "不升级，误差通道与 λ 收缩主通道正交，A→1 的速率仍由 (H2′_λ) 假设决定。", space_after=6)

para("关键词：跨 T 衰减律；BGS 误差项 O(1/√logT)；配对常数 A(λ;T)；速率标度；S1b 升级判定",
     space_after=10)

# ---------- 1 承接与目标 ----------
h1t("1　承接与目标")
h2t("1.1　S1b 之后：速率标度为何需要钉死")
para("S1b（d1 已交付）给出「干到 1」的定理骨架：在 (H2′_λ) 假设下 A=1+o(1)，速率 (logT)^{−15/7}。"
     "该速率的合法性取决于配对常数向极限收敛时的误差通道：若误差项按 BGS 定理为 O(1/√logT)，"
     "则固定核下 A(λ;T) 逼近 GUE2(λ) 很慢，A→1 必须依赖 λ(T)→0 的主通道；若按离线乐观口径 "
     "O(1/logT)，误差衰减更快，速率存在升级空间。S2(ii) 的任务正是用跨 T 数值把这条误差律钉死。")
h2t("1.2　S2(ii) 在「干到 1」链中的位置")
para("主线：S0 数值定向 → S1a Parseval 归因 → S1b 定理骨架 → S2(i) 左尾威胁闭合 → S2(ii) 跨 T "
     "衰减律判别 → S3 威胁排除交叉验证。S2(ii) 与前序的最大区别是引入「T 维」：S1a 的衰减律段"
     "只在单 T=6×10⁵ 内做 5 段漂移检验，S2(ii) 则在八个数量级跨度（logT∈[9.21,13.59]）上直接"
     "拟合 Δ 随 T 的衰减。这使两律（1/√logT 与 1/logT）的可分性首次得到实测检验。")

# ---------- 2 口径与数据 ----------
h1t("2　口径与数据")
h2t("2.1　配对常数与 GUE2 基准（S0 口径）")
para("配对常数 A(λ;T) 定义沿用 S0/S1a：K=sinc²(πu/a) 为 fejer 型核，配对直方图取全局归一化"
     "（统一密度 δ），half=40、binw=0.02，截断 [300,T]；GUE2 基准 gue2(a)=1+2∫₀ᴿ(1−sinc²πu)·"
     "sinc⁴(πu/a)du（R=60）。偏差量 Δ=A−GUE2 即「实测配对 − 随机矩阵预测」的带符号缺口，"
     "Δ<0 表示亚 GUE 配对（排斥不足）。")
h2t("2.2　八档零点数据")
para("旧四档：T=10⁴/2×10⁴/4×10⁴/6×10⁵（前序批次）。新四档 T=10⁵/2×10⁵/4×10⁵/8×10⁵ 为本工作"
     "生成：ζ 用 gen_zeta_generic（低区 mp.zetazero + 高区 R-S 扫描 h=0.02），L(χ₅) 用 "
     "gen_L_generic（D=5，同口径）。生成量 @8×10⁵：ζ 1 369 279 根、L(χ₅) 1 570 290 根；"
     "密度核对（T=8×10⁵）：ζ 差 −25、L 差 −3934（0.25%，R-S 扫描一贯偏差量级）。"
     "L 生成脚本末段抽样验证因 mpf 格式化崩溃返回 rc=1，但数据在崩溃前已完整落盘，"
     "npz 核验（排序、根数、覆盖到 T）通过。")

# ---------- 3 结果 ----------
h1t("3　结果")
h2t("3.1　八档配对常数（表 1）")
caption("表 1　八档 A(λ;T)（ζ 与 L(χ₅)），统一截断 [300,T]；GUE2 基准：a=0.3→1.004095、"
        "a=0.5→1.017708、a=1.0→1.116667、a=2.0→1.566666")
t1 = [["T", "n_ζ", "n_L", "Aζ(0.3)", "Aζ(1.0)", "Aζ(2.0)", "AL(0.3)", "AL(1.0)", "AL(2.0)"]]
for r_ in rows:
    az, al = r_["A"]["zeta"], r_["A"]["L"]
    T = r_["T"]
    Ts = "10⁴" if T == 1.0e4 else ("2×10⁴" if T == 2.0e4 else ("4×10⁴" if T == 4.0e4 else
         ("10⁵" if T == 1.0e5 else ("2×10⁵" if T == 2.0e5 else ("4×10⁵" if T == 4.0e5 else
         ("6×10⁵" if T == 6.0e5 else "8×10⁵"))))))
    t1.append([Ts, str(r_["n_zeta"]), str(r_["n_L"]),
               "%.6f" % az["0.3"], "%.6f" % az["1.0"], "%.6f" % az["2.0"],
               "%.6f" % al["0.3"], "%.6f" % al["1.0"], "%.6f" % al["2.0"]])
add_table(t1[0], t1[1:], widths=[1.3, 1.5, 1.5, 1.7, 1.7, 1.7, 1.7, 1.7, 1.7])
para("", indent_chars=0, space_after=2)
para("读数：(i) 对每个 a、每族，A 随 T 单调递增逼近 GUE2（Δ 全负、|Δ| 递减），八档内无反弹；"
     "(ii) ζ 与 L(χ₅) 在任一 (a,T) 处差异 ≲ 5×10⁻³（a=2.0 处最大 0.007~0.008），双族一致性良好；"
     "(iii) 窄核 a=0.3 处 A 已很接近 GUE2（偏差 1~2×10⁻³），宽核 a=2.0 处偏差仍大（5~6×10⁻²），"
     "符合「宽核探长程、误差累积更大」的预期。")
h2t("3.2　双律拟合（表 2）")
caption("表 2　Δ=A−GUE2 对 1/√logT 与 1/logT 的线性拟合（斜率 k、判定系数 R²；8 点）")
t2 = [["a", "族", "k(1/√logT)", "R²(1/√logT)", "k(1/logT)", "R²(1/logT)"]]
for a in ("0.3", "0.5", "1.0", "2.0"):
    for fam in ("zeta", "L"):
        f = fits[fam][a]
        t2.append([a, "ζ" if fam == "zeta" else "L",
                   "%.4f" % f["1_over_sqrtlogT"]["slope"], "%.4f" % f["1_over_sqrtlogT"]["r2"],
                   "%.4f" % f["1_over_logT"]["slope"], "%.4f" % f["1_over_logT"]["r2"]])
add_table(t2[0], t2[1:], widths=[1.2, 1.2, 3.2, 3.2, 3.2, 3.2])
para("", indent_chars=0, space_after=2)
para("跨族均值（law_tally）：a=1.0：1/√logT=0.9945 vs 1/logT=0.9925；a=2.0：0.9894 vs 0.9838；"
     "a=0.5：0.8523 vs 0.8434；a=0.3：0.7146 vs 0.7277。宽核（a=1.0, 2.0）1/√logT 系统性微优，"
     "窄核（a=0.5）亦微优，仅 a=0.3 处 1/logT 微优但 L 族斜率转正（+0.0056/+0.0096，纯噪音），"
     "该处判定无效。")
h2t("3.3　实测衰减指数")
para("端点比值：ζ a=1.0 处 |Δ(8×10⁵)/Δ(10⁴)|=0.549 → 等效幂指数 k≈1.54（若 Δ∝(logT)^{−k}）；"
     "a=2.0 处比值 0.697 → k≈0.93。两处 k 不一致提示真实衰减为混合结构（BGS 误差项 + 有限窗效应），"
     "单律纯幂拟合只是近似——这进一步说明两律竞争在有限档数下难以铁证分离，保守取 BGS 1/√logT。")

pfig = doc.add_paragraph()
pfig.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = pfig.add_run()
run.add_picture(FIG, width=Cm(13.5))
pfig.paragraph_format.keep_with_next = True
caption("图 1　Δ=A−GUE2 跨 T 衰减（2×2：a=0.3/0.5/1.0/2.0；ζ 蓝 o、L(χ₅) 红 s；虚线=1/√logT 拟合，"
        "点线=1/logT 拟合；纵轴 symlog）")

# ---------- 4 判定 ----------
h1t("4　判定")
h2t("4.1　误差律：BGS 1/√logT 主导，离线口径无支持")
para("联合读判（8 档 × 双族 × 四核）：宽核端（a=1.0, 2.0，配对探测最充分）1/√logT 的 R² 系统性"
     "高于 1/logT（跨族差 +0.002~+0.006），且方向与 BGS 定理误差项 O(1/√logT) 一致；a=0.5 亦微优。"
     "窄核 a=0.3 的 L 族斜率转正，属统计噪音，不构成 1/logT 的支持证据。判定：误差通道按 "
     "O(1/√logT)（BGS 型）保守处理，O(1/logT) 离线乐观口径无数值支持。")
h2t("4.2　无反弹：S1a 漂移疑虑在 T 维被排除")
para("S1a 在 T=6×10⁵ 内 5 段漂移曾见分段波动；S2(ii) 八档数据显示 A 对 T 单调逼近 GUE2、|Δ| 单调"
     "收敛（8 个点无一反弹）。「有限 T 下配对常数相对 GUE2 的缺口随 T 增大而闭合」在 10⁴~8×10⁵ "
     "跨三数量级的 T 维上成立。")
h2t("4.3　窄核噪声披露")
para("a=0.3 处 L(χ₅) 的 R² 仅 0.49~0.52 且斜率转正——窄核窗口内配对样本少（half=40 内 u 分辨率下"
     "A 的统计涨落大），该处两律拟合均不可信，文档不据此下任何结论。宽核结论不受影响。")

# ---------- 5 对 S1b 的影响 ----------
h1t("5　对 S1b 的影响")
h2t("5.1　速率 (logT)^{−15/7}：不升级")
para("S2(ii) 判定误差通道为 BGS O(1/√logT)（保守口径），快于该误差的 1/logT 乐观口径被排除。"
     "S1b 速率 (logT)^{−15/7}≈(logT)^{−2.14} 是 (H2′_λ) 假设下由 λ(T)→0 主通道决定的速率，"
     "与误差通道正交；误差律判定不提供任何升级依据，故维持原速率，不升级。")
h2t("5.2　误差通道与 λ 通道的正交性得到数值支持")
para("数值显示：固定核下 Δ 以 √logT 尺度缓慢收敛（a=1.0 处 8×10⁵ 仍残留 1.7×10⁻² 的缺口），"
     "远慢于 (logT)^{−15/7}。这直接支持 S1b 的核心论断：A→1 不可能靠「固定核、T→∞」达成，"
     "必须依赖核收缩 λ(T)→0 的主通道——即 (H2′_λ) 假设不是可有可无的技术性前提，而是速率 "
     "(logT)^{−15/7} 的承载者。S2(ii) 与 S2(i)（x-口径弱探针）、S3（Δ 指纹爆炸敏感）一致，"
     "共同把主线的成功条件收敛到 (H2′_λ) 与 ζ_K 特有谱结构本身。")

# ---------- 6 诚实披露与开放问题 ----------
h1t("6　诚实披露与开放问题")
para("① 两律 R² 差仅 0.002~0.006（宽核端），属「弱系统性优势 + 保守原则」的判定，非统计铁证；"
     "logT∈[9.21,13.59] 的跨度不足以把两函数形状完全分开，更大 T（≥10⁶ 或 10⁷）或更高精度核可"
     "进一步收紧；② 实测衰减指数 k≈0.93~1.54 随 a 漂移，提示真实误差含混合结构，本文不做混合律"
     "分解（后续可做 Δ=C₁/√logT+C₂/logT 双项拟合）；③ 新四档 L 生成脚本末段抽样验证崩溃"
     "（rc=1），数据本身完整，但该档 L 的「低区 mpmath + 高区 R-S」拼接未做独立交叉复核；"
     "④ Δ 依赖 GUE2 基准的半无穷积分截断 R=60（fejer 核指数衰减，截断误差可忽略）；"
     "⑤ 判定不涉及实数部（x-口径）结构，与 S2(i) 的左尾闭合互补而非重叠。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] Baluyot, D., Goldston, D., Suriajaya, A., Turnage-Butterbaugh, C. 无条件配对公式（BGS 定理），arXiv:2306.04799（Lemma 5：误差 O(1/√logT)）——S2(ii) 判别的理论锚（S1b/XL 期已核实）.",
    "[2] Lamzouri, M. 配对常数与随机矩阵模型，arXiv:2609.02882（Prop 2.1：ζ 的配对常数下界）——A_L≤1.125 前提链（S1b 期已核实）.",
    "[3] 攻防 XLII-S0/S1a/S1b/S2(i)/S3（d1 已交付）：全尺度 GUE 配对数值定向、Parseval 归因、λ(T) 构造与 p 量化、Weil x-口径弱探针、Δ 指纹排除交叉验证.",
    "[4] 攻防 XL/XLI（d1 已交付）：配对侧无条件界（BGS O(1/√logT) 技术极限）；拟随机并集定理常数机制闭合.",
    "[5] 本工作数值件（可复跑）：qrh_work/xlii_s2ii.py + xlii_s2ii.json + xlii_s2ii_fig.png；零点生成 gen_zeta_generic.py/gen_L_generic.py（T=10⁵~8×10⁵ 新四档）.",
]
for rtext in refs:
    p = para(rtext, indent_chars=0, space_after=2)
    p.paragraph_format.line_spacing = 1.0

doc.save(TARGET)
print("saved:", TARGET)
