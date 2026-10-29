# -*- coding: utf-8 -*-
"""路2攻防XLII-S7.9：(L2) 素数项界假命题修正——支撑截断口径（d1 惯例，OMML 公式）。"""
import os, re
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement, parse_xml
from latex2mathml.converter import convert as _l2m
import mathml2omml as _m2o

OUT_DIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1"
os.makedirs(OUT_DIR, exist_ok=True)
TARGET = os.path.join(OUT_DIR, "路2攻防XLII-S7.9-(L2)素数项界假命题修正-支撑截断口径.docx")

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
set_fonts(cap, "黑体", size=9)
cap.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
cap.paragraph_format.space_before = Pt(4); cap.paragraph_format.space_after = Pt(4)
cap.paragraph_format.keep_with_next = True

M_NS = "http://schemas.openxmlformats.org/officeDocument/2006/math"

def _omml(latex):
    out = _m2o.convert(_l2m(latex))
    if "xmlns:m" not in out[:120]:
        out = out.replace("<m:oMath", '<m:oMath xmlns:m="%s"' % M_NS, 1)
    return out

def math_para(latex, space_before=None, space_after=None):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    xml = ('<m:oMathPara xmlns:m="%s"><m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>%s</m:oMathPara>'
           % (M_NS, _omml(latex)))
    p._p.append(parse_xml(xml))
    if space_before is not None:
        p.paragraph_format.space_before = Pt(space_before)
    if space_after is not None:
        p.paragraph_format.space_after = Pt(space_after)
    return p

def _apply_run_font(r, bold=False, font=None, size=None):
    if bold:
        r.font.bold = True
    r.font.name = "Times New Roman"
    if size:
        r.font.size = Pt(size)
    rpr = r._r.get_or_add_rPr(); rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts"); rpr.append(rf)
    rf.set(qn("w:ascii"), "Times New Roman"); rf.set(qn("w:hAnsi"), "Times New Roman")
    if font:
        rf.set(qn("w:eastAsia"), font)

def para(text, align=None, bold=False, font=None, size=None, indent_chars=0,
         space_before=None, space_after=None, style=None):
    p = doc.add_paragraph(style=style)
    if align is not None:
        p.alignment = align
    if indent_chars:
        ppr = p._p.get_or_add_pPr(); ind2 = ppr.get_or_add_ind()
        ind2.set(qn("w:firstLineChars"), str(indent_chars * 100))
    tokens = re.split(r"(\$[^$]*\$|\^\{[^}]*\}|_\{[^}]*\})", text)
    for tk in tokens:
        if not tk:
            continue
        r = None
        if tk.startswith("$") and tk.endswith("$") and len(tk) > 1:
            p._p.append(parse_xml(_omml(tk[1:-1])))
        elif tk.startswith("^{"):
            r = p.add_run(tk[2:-1]); r.font.superscript = True
        elif tk.startswith("_{"):
            r = p.add_run(tk[2:-1]); r.font.subscript = True
        else:
            r = p.add_run(tk)
        if r is not None:
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

# ================= 正文 =================
para("路2攻防XLII-S7.9：(L2) 素数项界假命题修正——支撑截断口径", style="Title")
para("2026-10-29 · d1 惯例落档 · 数学口径变更记录", align=WD_ALIGN_PARAGRAPH.CENTER, size=10, space_after=10)

h1t("摘要")
para("我们发现 (L2) 半形式化中的两个命名 axiom——$\\texttt{sum\\_weight\\_decay}$ 与 "
     "$\\texttt{sum\\_sqrt\\_decay}$——的数学陈述为**假命题**：$\\sum_{n\\le X} n^{-1/2}\\,e^{-c'\\sqrt{\\log n}}$ 与 "
     "$\\sum_{n\\le X} n^{1/2}\\,e^{-c'\\sqrt{\\log n}}$ 均发散到 $+\\infty$（积分检验：令 $u=\\sqrt{\\log x}$，被积函数 "
     "$e^{u^2/2-c'u}\\to\\infty$；数值抽查 $10^3\\to10^7$ 确认 $\\sqrt{N}$ 律发散）。根因：$e^{-c'\\sqrt{\\log n}}$ 是"
     "**亚多项式衰减**（慢于任何 $n^{-\\varepsilon}$），$n^{\\pm1/2}$ 裸加权压不住；素数项有界性的真实来源是 "
     "$\\hat K$ 频域窄支撑截断（$|\\delta\\log n|\\le 1$ 即 $n\\le e^{1/\\delta}$，有限和）与 $\\chi_5$ 振荡。"
     "本文给出修正口径：两个 axiom 改为支撑截断有限和形式（常数显式依赖 $\\delta$），"
     "$\\texttt{prime\\_sum\\_bound}$ 组装相应调整；SW 指数 $e^{-c'\\sqrt{\\log x}}$ 回归其本来位置——"
     "SW 部分和自身。同轮完成**窗外拆窗**：素数项权重统一为频域核 $\\hat K=\\texttt{fourierCos}\\,K$，"
     "窗外项由支撑条件自动为零，$\\texttt{prime\\_sum\\_bound}$ 去掉窗内前提 $X\\le e^{1/\\delta}$，"
     "对任意 $X\\ge 1$ 成立（§6）。影响面：S7.6、S7.8 与 QRH\\_summary 需同步。", indent_chars=0)

h1t("1　发现与判定")

h2t("1.1　原 axiom 陈述（Main.lean 351–363）")
para("$\\texttt{sum\\_weight\\_decay}$：对 $c'>0$，$\\exists C_2\\ge 0$，$\\forall X\\ge 1$，")
math_para(r"\sum_{n\in[1,\lfloor X\rfloor]_\mathbb{N}} n^{-1/2}\,e^{-c'\sqrt{\log n}}\le C_2,")
para("$\\texttt{sum\\_sqrt\\_decay}$：对 $c'>0$，$\\exists C_3\\ge 0$，$\\forall X\\ge 1$，")
math_para(r"\sum_{n\in[1,\lfloor X\rfloor]_\mathbb{N}} n^{1/2}\,e^{-c'\sqrt{\log n}}\le C_3.")

h2t("1.2　假命题判定")
para("**亚多项式性**。对一切 $\\varepsilon>0$，最终 $n^{\\varepsilon}\\le e^{c'\\sqrt{\\log n}}$："
     "$\\varepsilon\\log n\\le c'\\sqrt{\\log n}$ 当 $\\log n\\ge (c'/\\varepsilon)^2$。故 "
     "$e^{-c'\\sqrt{\\log n}}\\ge n^{-\\varepsilon}$ 最终成立——指数衰减慢于任何幂。")
para("**积分检验**（$u=\\sqrt{\\log x}$，$x=e^{u^2}$，$dx=2u\\,e^{u^2}du$）：")
math_para(r"\int_1^{\infty} x^{-1/2}e^{-c'\sqrt{\log x}}\,dx=\int_0^{\infty} 2u\,e^{u^2/2-c'u}\,du=+\infty,", space_after=4)
para("被积函数 $2u\\,e^{u^2/2-c'u}\\to\\infty$（$u^2/2$ 主导 $c'u$），积分发散；$x^{1/2}$ 版为 "
     "$\\int 2u\\,e^{3u^2/2-c'u}du$，发散更烈。级数对应发散（积分检验）。又 "
     "$\\sqrt{X}\\,e^{-c'\\sqrt{\\log X}}\\to+\\infty$（指数差 $(\\log X)/2-c'\\sqrt{\\log X}\\to+\\infty$），"
     "故 $\\texttt{sum\\_sqrt\\_decay}$ 注释所称「$\\sqrt{N}e^{-c'\\sqrt{\\log N}}$ 为该和之单项」的单项本身即无界。")

h2t("1.3　数值证据（c′ = 1）")
caption("表 1　两个指数衰减部分和随 N 增长（10³ → 10⁷）")
add_table(
    ["N", "Σ n^{−1/2}·e^{−√log n}", "Σ √n·e^{−√log n}", "尾项 √N·e^{−√log N}"],
    [["10³", "7.049", "1 762", "2.28"],
     ["10⁴", "14.818", "36 226", "4.81"],
     ["10⁵", "31.656", "788 763", "10.63"],
     ["10⁶", "69.638", "17 853 604", "24.31"],
     ["10⁷", "157.863", "415 849 691", "57.07"]],
    widths=[2.6, 4.0, 4.6, 4.2])
para("第一列按 $\\sqrt{N}$ 律增长（每十倍 N 约 ×2.27），第二列增长 $\\propto N^{3/2}$ 量级，第三列无界——"
     "三列均不趋于常数，两 axiom 之「∃C，∀X」一致有界陈述不成立。", indent_chars=0)

h1t("2　根因：素数项有界性的真实来源")
para("真实素数项为 $S(X)=\\sum_{p\\le X}\\Lambda(p)\\chi_5(p)\\,p^{-1/2}\\,\\hat K(\\delta\\log p)$。其有界性"
     "**不来自裸指数衰减**，而来自三层结构：")
para("(i) **$\\hat K$ 频域窄支撑截断**：$\\hat K$ 支撑 $\\subset[-1,1]$（$\\lambda\\le 1/2$ 核族），故 "
     "$\\hat K(\\delta\\log p)\\ne 0$ 仅当 $|\\delta\\log p|\\le 1$，即 $p\\le e^{1/\\delta}$——素数项自动成为"
     "**有限和**，且 $\\delta=\\log T/(2\\pi)\\to\\infty$ 时截断更紧（$e^{1/\\delta}\\to 1$）。", indent_chars=0)
para("(ii) **$\\chi_5$ 振荡**：SW 部分和 $|\\sum_{n\\le x}\\Lambda(n)\\chi_5(n)|\\le c\\,x\\,e^{-c'\\sqrt{\\log x}}$ "
     "在支撑窗内的总贡献 $\\le c\\,e^{1/\\delta}\\,e^{-c'\\sqrt{1/\\delta}}$（S7.2 件 F 实测 $|S_a|\\approx 2.05$、"
     "$|S_a|/N_L\\to 10^{-8}$）。", indent_chars=0)
para("(iii) **Abel 差分**：$\\Delta b_n$ 由 $K$ 光滑性压至 $O(n^{-3/2})$，配合 (i) 的有限窗，差分和在窗内"
     "$\\le 2\\sqrt{e^{1/\\delta}}$ 量级。", indent_chars=0)
para("即：SW 指数出现在 SW 部分和自身，而非出现在 $n^{\\pm1/2}$ 裸加权和上。原 axiom 张冠李戴，"
     "把衰减放错了位置。", indent_chars=0)

h1t("3　修正口径（新陈述）")

h2t("3.1　sum_weight_decay 新形式（支撑截断有限和）")
math_para(r"\exists C_2(\delta)\ge 0,\ \forall X\ge 1,\ "
          r"\sum_{n\le\min(X,\,e^{1/\delta})} n^{-1/2}\le C_2(\delta),\qquad "
          r"C_2(\delta)=2\sqrt{e^{1/\delta}}\ \text{(可显式)}", space_after=4)
para("证明为平凡 Finset 计数：$\\sum_{n\\le Y} n^{-1/2}\\le 2\\sqrt Y$（积分比较，$Y=e^{1/\\delta}$）。"
     "SW 指数不再出现于此；若需保留，可并入支撑窗 $e^{1/\\delta}$ 的取值。", indent_chars=0)

h2t("3.2　sum_sqrt_decay 新形式（尾部项重写）")
para("Abel 尾部 $A_N\\cdot b_N$（$A_N=\\sum_{n\\le N}\\Lambda(n)\\chi_5(n)$，$b_N=N^{-1/2}\\hat K(\\delta\\log N)$）"
     "在支撑窗内满足")
math_para(r"|A_N\cdot b_N|\le c\,\sqrt{e^{1/\delta}}\;e^{-c'\sqrt{1/\delta}}\;\|\hat K\|_{\infty},", space_after=4)
para("对 $N\\le e^{1/\\delta}$；窗外 $b_N=0$。常数显式依赖 $\\delta$（即 T），不再声称绝对一致有界。", indent_chars=0)

h2t("3.3　prime_sum_bound 组装调整（窗内版 → 拆窗后无窗内版，见 §6）")
para("$|\\texttt{primeSum}\\,K\\,X\\,\\delta|\\le C$，$C=c\\,M\\,(C_2+C_3)$（组装真证：Abel 分解 + "
     "三角不等式 + SW 部分和界 + 权重件 + 两衰减件）；窗内版要求 $X\\le e^{1/\\delta}$。归一化 "
     "$|\\texttt{prime}|\\le 1$ 依赖 $C/N_L\\le 1$——数值上 $C/N_L\\le 1.70\\times 10^{-3}$（件 G）余量充分。"
     "原「绝对常数 C」改为「依赖 δ 的显式常数」；§6 拆窗后窗内前提移除，$X$ 任意。", indent_chars=0)

h1t("4　影响面与同步")
para("(1) **S7.6**（SW 常数显式化）：$|\\psi(x,\\chi_5)|/x\\le 1.70\\times 10^{-3}$ 件不变；"
     "素数项界组装口径按 §3 修正。(2) **S7.8**（(L2) 半形式化）：`sum_weight_decay`/`sum_sqrt_decay` "
     "两 axiom 由「裸指数衰减和」改为「支撑截断有限和」；(3) **QRH\\_summary.md**：挂账清单与"
     "真证链同步更新（真证链计数暂不变——两件由 axiom 改为新陈述后另行真证）；"
     "(4) **arXiv 论文草稿**（d1\\en）：§5 证明骨架 prime 项描述按支撑截断口径改写（待论文下一轮修订）。", indent_chars=0)

h1t("5　Lean 落位与真证结果（2026-10-29）")
para("(a) 两衰减件由 axiom 降为 theorem：`sum_weight_decay`（$C_2=2\\sqrt{e^{1/\\delta}}$，链 = 逐项望远镜 "
     "`inv_sqrt_telescope_le` + `sum_sqrt_telescope`（Icc 归纳）+ `sum_inv_sqrt_le_two_sqrt`）；"
     "`sum_sqrt_decay`（$C_3=e^{3/(2\\delta)}$，链 = 逐项 $e^{-c'\\sqrt{\\log n}}\\le 1$ + `sum_le_card_nsmul` "
     "（card(Icc 1 N)=N 手写归纳）+ `Real.sqrt_le_iff` 平方单调）。", indent_chars=0)
para("(b) SW 指数 $e^{-c'\\sqrt{\\log x}}$ 仅保留在 `siegel_walfisz_chi5` 部分和陈述中（其位置正确）；"
     "`prime_weight_bounds` 权重统一为频域核 $\\hat K$（§6.1 口径修正）。", indent_chars=0)
para("(c) 窗外拆窗（§6）：`primeSum_window_eq` 真证，`prime_sum_bound` 去掉窗内前提，任意 $X\\ge 1$。"
     "全量 `lake build QRH` exit=0；真证链 +3，挂账 axiom −2。", indent_chars=0)

h1t("6　窗外拆窗（补充落档）")

h2t("6.1　口径修正：权重与支撑件的空间错位")
para("`primeSum` 原权重为时域核 $K(\\delta\\log n)$，而窗外零性（$K(\\delta\\log n)=0$ 当 $|\\delta\\log n|>1$）"
     "只能由频域支撑件 $\\forall u,\\ 1<|u|\\to \\texttt{fourierCos}\\,K\\,u=0$（$\\text{supp}\\,\\hat K\\subset[-1,1]$）"
     "给出——两者空间错位：$\\hat K$ 频域紧支撑只给 $K$ 带限（Paley–Wiener），不给 $K$ 时域为零。"
     "修正：素数项权重全局改为频域核 $\\hat K(\\delta\\log n)=\\texttt{fourierCos}\\,K\\,(\\delta\\log n)$，"
     "与 §2(i)「$\\hat K$ 频域窄支撑截断」口径一致（`primeSum` 定义、`prime_weight_bounds` 本体与注释、"
     "`prime_sum_bound` 证明体 28 处同步）。数学上零额外假设——窗外零性本由 BGS 引理 5 的支撑条件给出。", indent_chars=0)

h2t("6.2　拆窗引理（真证）")
math_para(r"\texttt{primeSumWindowEq}:\quad \texttt{primeSum}\,K\,X\,\delta=\texttt{primeSum}\,K\,(\min(X,\,e^{1/\delta}))\,\delta,\qquad \forall X\ge 1,", space_after=4)
para("证链：`by_cases X ≤ e^{1/δ}` 拆两分支——窗内 `min_eq_left` 直接 `rw`；窗外（$e^{1/\\delta}\\le X$）"
     "用 `Finset.sum_subset`（$\\lfloor e^{1/\\delta}\\rfloor_+\\subseteq\\lfloor X\\rfloor_+$），窗外项为零性："
     "$n\\notin[1,\\lfloor e^{1/\\delta}\\rfloor_+]$ 且 $n\\ge 1$ 推 $\\lfloor e^{1/\\delta}\\rfloor_+<n$（`by_contra`）"
     "，$\\texttt{Nat.floor\\_lt}$ 得 $e^{1/\\delta}<n$，`Real.exp_lt_exp` 得 $1/\\delta<\\log n$，"
     "`mul_lt_mul_of_pos_left`（$\\delta>0$）得 $1<\\delta\\log n$，`abs_of_pos` 后支撑件直接给 "
     "$\\hat K(\\delta\\log n)=0$——和式收缩到 $\\lfloor e^{1/\\delta}\\rfloor_+$。", indent_chars=0)

h2t("6.3　prime_sum_bound 无窗内版")
para("`prime_sum_bound` 签名由 `(hXw : X ≤ e^{1/δ})` 改为 `(hKs : ∀ u, 1<|u| → fourierCos K u = 0)`；"
     "$X'=\\min(X,e^{1/\\delta})$ 由 `min_le_right` 自动满足窗内前提，原窗内证明体套 $X'$ 不变：", indent_chars=0)
math_para(r"|\texttt{primeSum}\,K\,X\,\delta|\le c\,M\,(C_2+C_3),\qquad \forall X\ge 1.", space_after=4)
para("对任意 $X\\ge 1$ 成立（含窗外 $X>e^{1/\\delta}$：和式先拆窗再套窗内界）。"
     "影响：`bgs3_pair_expansion` 的 prime 分量与 `prime_sum_bound` 不互相引用，拆窗主要强化 (L2) "
     "组装件的普适性口径。", indent_chars=0)

h2t("6.4　验证")
para("`lake build QRH` 全量 exit=0（权重口径修正一轮、拆窗 + 去前提一轮；一处 `simp` 未化简 floor 内 "
     "min，改 `rw [hmin]`）；#check 探针（`Nat.floor_lt`、`Real.exp_lt_exp`、`Finset.sum_subset` 等）确认后删除；"
     "QRH\\_summary.md / QRH\\_summary\\_en.md 已同步拆窗条目（真证链 +3，挂账 axiom −2）。", indent_chars=0)

doc.save(TARGET)
print("saved:", TARGET)
