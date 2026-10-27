# -*- coding: utf-8 -*-
"""攻防 XLII · S7.7 落档（OMML 公式版）：击破清单四连——BGS 引理 3-5 移植、N1 真证、L1 不变、L4 切割链。
母本：gen_s7_6_doc.py 样式链；公式升级为 Word 原生 OMML（LaTeX→MathML→OMML，latex2mathml + mathml2omml）。
事实来源：本轮 Lean 工程执行记录（C:\\proj2\\QRH 三文件 + build_qrh_l4b.txt，2604 jobs）。
惯例（2026-10-27 起）：文档公式一律 OMML 原生对象；禁 LaTeX 源码文本；代码标识符保持文本。
"""
import re
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement, parse_xml
from latex2mathml.converter import convert as _l2m
import mathml2omml as _m2o

TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.7-击破清单四连-BGS引理3-5移植与N1-L1-L4真证.docx"

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

M_NS = "http://schemas.openxmlformats.org/officeDocument/2006/math"

_HAT_RE = re.compile(
    r"<m:limUpp><m:e>(.*?)</m:e><m:lim>.*?<m:t>\^</m:t>.*?</m:lim></m:limUpp>", re.S)

def _fix_hat(xml):
    """limUpp(^) → acc(̂)：mathml2omml 把 \\hat 转成上极限符，标准排版应为上方帽子（accent）。"""
    return _HAT_RE.sub(
        lambda m: '<m:acc><m:accPr><m:chr m:val="\u0302"/></m:accPr><m:e>%s</m:e></m:acc>' % m.group(1),
        xml)

def _omml(latex):
    """LaTeX → OMML XML 字符串（mathml2omml 输出 <m:oMath>…；补 xmlns:m 声明 + hat 修正）。"""
    out = _m2o.convert(_l2m(latex))
    out = _fix_hat(out)
    if "xmlns:m" not in out[:120]:
        out = out.replace("<m:oMath", '<m:oMath xmlns:m="%s"' % M_NS, 1)
    return out

def add_math_el(p, latex):
    """把 LaTeX 公式作为内联 OMML 追加到段落 p。"""
    elm = parse_xml(_omml(latex))
    p._p.append(elm)

def math_para(latex, space_before=None, space_after=None):
    """独立居中公式段落（m:oMathPara，display 公式）。"""
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
    tokens = re.split(r"(\$[^$]*\$|\^\{[^}]*\}|_\{[^}]*\})", text)
    for tk in tokens:
        if not tk:
            continue
        if tk.startswith("$") and tk.endswith("$") and len(tk) > 1:
            add_math_el(p, tk[1:-1])
        elif tk.startswith("^{"):
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
para("路2攻防XLII—S7.7：击破清单四连", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（BGS 引理 3–5 移植 + N1 真证 + L1 不变 + L4 切割链）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S7.1 形式化证明推进", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 27 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("S7.1 形式化证明击破清单一次四连推进。(i) BGS 引理 3–5 逐条移植（Main）：核构造引理 5 落位为 "
     "核可容许谓词 KernelAdmissible（$K(0)=1$ 且 $\\mathrm{supp}\\,\\hat K\\subset[-1,1]$，$\\lambda\\le 1/2$ 核族），"
     "Khat_admissible 组装（$K(0)=1$ 真证 + 频域支撑件）；配对和展开引理 3 落位为 bgs3_pair_expansion"
     "（$A_L=\\mathrm{diag}+\\mathrm{prime}+\\mathrm{offcrit}$ 分解与界）；pair_sum_expansion 由大 axiom 降为组装"
     "定理，核可容许条件显式进入主定理链，s71_main 接入。(ii) N1 双件真证（Stage3）：n1_diag_invariant、"
     "n1_offdiag_scale_eq 由 fourierCos_scale 直接推导，n1_offdiag_vanishes 落为结构件真证——并作一处"
     "数学诚实修正（原 $\\forall N$ 陈述过宽，vanishing 归因核因子缩放 + 频域衰减件）。(iii) L1 不变真证："
     "normL1 从 axiom 降为 Bochner 积分真定义 $\\|f\\|_1=\\int |f|$，scaleKernel_L1_invariant 由 "
     "integral_const_mul + integral_comp_inv_mul_left（Haar 变量替换）真证。(iv) BGS 引理 4 移植（Main）："
     "离线误差按 $T^{3/8}$ 切割为低频弱实部件 offcritLow 与高频计数件 offcritHigh，bgs4_offcrit_split/"
     "low/high 落位，offcritical_small 由三角不等式组装真证（$R=R_1+R_2$）。编译证据：lake build QRH "
     "2604 jobs 全绿。Main 清单 (L3)(L4) 落位，仅剩 (L1)(L2) 长线数论真证；Stage3 剩 fourierCos_scale"
     "（频域积分层）。", space_after=6)

para("关键词：BGS 引理；配对和展开；核可容许；Bochner 积分；变量替换；$T^{3/8}$ 切割",
     space_after=10)

# ---------- 1 概览 ----------
h1t("1　概览：四连与编译状态")
para("本轮把 S7.1 形式化证明的击破清单从「命名 axiom 占位」推进到「机制链落位 + 组装真证」：Main 侧 "
     "(L3)(L4) 完成 BGS 引理 3–5 与引理 4 的逐条移植，Stage3 侧 N1 双件与 L1 不变由解析件真证。"
     "为打破 import 环（Stage3⇄Main），fourierCos/normL1 先迁至 Core 4b 节，依赖链 Core→Main→Stage3 "
     "单向。全量编译 2604 jobs 全绿（build_qrh_l4b.txt）。")
caption("表 1　本轮改动与编译状态")
hdr1 = ["模块", "本轮动作", "状态"]
rows1 = [
    ["Core（S7_1_Core.lean）", "4b 节迁入 fourierCos/normL1；normL1 降为 Bochner 积分真定义", "编译绿"],
    ["Main（S7_1_Main.lean）", "(L3) BGS 引理 3–5 移植；(L4) BGS 引理 4 T^{3/8} 切割链", "编译绿"],
    ["Stage3（S7_1_Stage3.lean）", "N1 双件真证；scaleKernel_L1_invariant 真证", "编译绿"],
    ["全量 lake build QRH", "2604 jobs，零错误", "全绿"],
]
add_table(hdr1, rows1, widths=[4.2, 8.2, 3.0])
para("注：编译咒语 = Git/elan PATH 前置 + lake build QRH；证据文件 C:\\proj2\\build_qrh_l4b.txt。",
     size=9, indent_chars=0, space_after=6)

# ---------- 2 架构重构 ----------
h1t("2　架构重构：频域/积分算子迁 Core")
para("依赖环的发现：Stage3 此前 import Main（取 zerosLChi5/pairConstant 真实定义）；Main 做 (L3) 移植"
     "需用 fourierCos（原 Stage3 独有）会成环（Stage3⇄Main）。处置：把 fourierCos 与 normL1 两个抽象"
     "算子迁至 Core 新增 4b 节（紧随 f0_continuous），Stage3 删除本地定义改由 Core 继承——依赖链 "
     "Core→Main→Stage3 恢复单向，改 Core 定义须先重 build Core olean 的既有约定不变。")
para("v4.34 实证（本轮的 import 侦察）：积分变量替换引理系位于 MeasureTheory.Measure 命名空间（"
     "integral_comp_mul_left / integral_comp_inv_mul_left），对 Bochner 积分无条件成立；mathlib 侧 "
     "Haar.NormedSpace.olean 已编译（226 个 MeasureTheory olean），Core 增 import 零增量编译成本。")

# ---------- 3 (L3) BGS 引理 3-5 ----------
h1t("3　(L3)：BGS 引理 3–5 逐条移植（Main）")
h2t("3.1　引理 5：核构造——KernelAdmissible")
para("核可容许谓词（$\\lambda\\le 1/2$ 核族）：KernelAdmissible $K := K(0)=1 \\wedge \\forall u,\\,|u|>1 \\rightarrow "
     "\\hat K(u)=0$——即 $\\hat K$ 频域窄支撑 $\\mathrm{supp}\\,\\hat K\\subset[-1,1]$，是 BGS 引理 5 的硬条件在 "
     "Lean 层的显式化。Khat 的可容许性由 Khat_admissible 组装：$K(0)=1$ 为真证（Khat_zero），频域支撑为 "
     "axiom（bgs5_khat_fourier_supp，积分层件，文档 S7.1 §3）。")
h2t("3.2　引理 3：配对和展开——bgs3_pair_expansion")
para("配对和积分展开（Montgomery–Vaughan 均值口径）：对 KernelAdmissible 核与弱实部假设（WeakRealPart "
     "T zerosLChi5），")
math_para(r"A_L(K)=\mathrm{diag}+\mathrm{prime}+\mathrm{offcrit},\qquad \mathrm{diag}\le C_{MT}+C_1\varepsilon,\qquad |\mathrm{prime}|\le 1,\ |\mathrm{offcrit}|\le 1",
          space_after=4)
para("对角主项界承接 n2_linkage 的 $O(\\varepsilon)$ 联动（文档 S7.4 定理 N2）；素数项界为 SW 压制 + "
     "Montgomery–Vaughan 均值（文档 S7.6）；离线项界为引理 4 的 $|\\mathrm{offcrit}|\\le 1$ 缩放（文档 S7.5 "
     "定理 N3）。")
h2t("3.3　pair_sum_expansion 定理化与 s71_main 接入")
para("pair_sum_expansion 从单一 axiom 降为 bgs3_pair_expansion 的组装包装（定理），核可容许条件显式"
     "进入主定理链；s71_main 的组装调用增加实参 Khat_admissible——定理 S7.1 的陈述与证明骨架不变，"
     "但引理 5 的硬条件从「注释声明」升级为「类型层面进入依赖」。")

# ---------- 4 N1 真证 ----------
h1t("4　N1 真证（Stage3）：fourierCos_scale 推导")
h2t("4.1　n1_diag_invariant")
para("缩放自同构不改变引理 5 对角主项：$\\hat r_a(0)=\\hat r(a\\cdot 0)=\\hat r(0)$——fourierCos_scale 取 $z=0$，"
     "congr 归参数，ring 闭合。真证。")
h2t("4.2　n1_offdiag_scale_eq 与 n1_offdiag_vanishes")
para("非对角核因子缩放（真证）：$\\hat K_a(2\\delta)^2=\\hat r(2a\\delta)^2$——fourierCos_scale 取 $z=2\\delta$，两层 "
     "congr 1 拆幂与函数参数，ring 闭合。vanishing 的结构件真证：在该等式重写与频域衰减件 "
     "$|\\hat r(2a\\delta)|^2\\le a^2C$（被积有界 × 支撑收缩层；数值件 F 已实测 $A-1$ 单调 "
     "1.86×10⁻²→3.09×10⁻⁹，$a$ 0.5→0.008）假设下，非对角配对和主导因子按 $a^2$ 衰减闭合。")
para("一处数学诚实修正：原 axiom 陈述 (fourierCos (scaleKernel a r) (2δ))² ≤ a²·N 对任意 $N$ 全称量化，"
     "数学上过宽（$\\hat r(0)=1$ 不消失，且 fourierCos_scale 只给等式、给不了界）。修正为带正参数 $C$ 的"
     "显式假设形式——vanishing 的归因从「核因子衰减」纠正为「核因子缩放 + 频域衰减件」，后者由数值件 F "
     "实测支撑。")

# ---------- 5 L1 不变 ----------
h1t("5　L1 不变真证：normL1 降级（Core + Stage3）")
h2t("5.1　normL1 真定义")
para("normL1 从 axiom 降为 Bochner 积分真定义：$\\|f\\|_1 = \\int |f|$（$\\mathbb{R}$ 上 volume；mathlib 对不可积"
     "函数按惯例取 0）。这一降级使「积分层」中 $L^1$ 范数件从抽象算子变为可计算的积分对象。")
h2t("5.2　scaleKernel_L1_invariant 证明链")
para("缩放变量替换的 $L^1$ 不变性（$a>0$）：")
math_para(r"\int |a^{-1}r(x/a)|\,dx = a^{-1}\int |r(a^{-1}x)|\,dx = a^{-1}|a|\int |r(y)|\,dy = \int |r|",
          space_after=4)
para("引理件：abs_mul + abs_of_pos（第一段）、MeasureTheory.integral_const_mul（常数因子提出）、"
     "MeasureTheory.Measure.integral_comp_inv_mul_left（Haar 变量替换）、field_simp（$a\\ne 0$ 归约）。"
     "修坑记录：field_simp 已闭合时尾部 ring 报 No goals（删除）。")

# ---------- 6 (L4) 引理 4 ----------
h1t("6　(L4)：BGS 引理 4 移植——$T^{3/8}$ 切割链（Main）")
h2t("6.1　机制")
para("离线误差的机制（文档 S7.5 定理 N3 / S7.1 §3）：Weil 显式公式余项按零点高度切割为两段——低频段 "
     "offcritLow（≤ $T^{3/8}$ 切割，弱实部假设压离临界带项，$\\beta\\le 1-c/\\log T$ 型）与高频段 offcritHigh"
     "（> $T^{3/8}$ 切割，零点计数 $N(T)$ 主项吸收，Riemann–von Mangoldt 平凡界）；两段贡献均为 "
     "$O(\\sqrt{\\log T})$ 量级。")
h2t("6.2　结构落位")
para("offcritLow/offcritHigh 以 opaque 定义；bgs4_offcrit_split（余项 = 低频 + 高频）、bgs4_offcrit_low"
     "（$|\\mathrm{offcritLow}(s)|\\le R_1\\sqrt{\\log s}$）、bgs4_offcrit_high（$|\\mathrm{offcritHigh}(s)|\\le "
     "R_2\\sqrt{\\log s}$）为命名 axiom（数论件，文档层论证）——切割链的三个机制件独立成声明。")
h2t("6.3　offcritical_small 组装真证")
para("由切割分解 rw + abs_add_le（三角不等式）+ add_le_add（双段界并）+ ring（$R_1\\sqrt{\\log s}+R_2"
     "\\sqrt{\\log s}=(R_1+R_2)\\sqrt{\\log s}$）组装 $R=R_1+R_2$。修坑记录：add_le_add 直接给出 "
     "$R_1\\sqrt{\\log s}+R_2\\sqrt{\\log s}$，需 calc 末步 ring 归 $(R_1+R_2)\\sqrt{\\log s}$。")

# ---------- 7 清单状态 ----------
h1t("7　清单状态与下一步")
caption("表 2　击破清单状态快照（2026-10-27）")
hdr2 = ["项", "状态"]
rows2 = [
    ["(L1) landau_explicit_L（Yildirim 公式 (6) 重排）", "精确陈述完成；真证需 Mellin 变换引理——长线"],
    ["(L2) siegel_walfisz_chi5（PNT in AP）", "精确陈述完成；真证需 PNT 算术级数版——长线"],
    ["(L3) pair_sum_expansion（BGS 引理 3–5 移植）", "完成（本档 §3）"],
    ["(L4) offcritical_small（BGS 引理 4 T^{3/8} 切割链）", "完成（本档 §6）"],
    ["Stage3：fourierCos_scale（频域变量替换）", "待积分层（Fourier 变换真定义）"],
    ["Stage3：f0_sub_feps_L1_bound", "待 mathlib 聚合（IntervalIntegral）"],
]
add_table(hdr2, rows2, widths=[10.0, 5.4])
para("下一步候选：(a) (L2) SW 显式公式件移植（半形式化，同 (L3)(L4) 模式）；(b) 超支撑素数项层真证"
     "（Abel 求和 + χ₅ 部分和衔接）；(c) 本轮新产物推 GitHub（push.ps1，待用户指示）。", space_after=6)

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] 攻防 XLII-S7.1（d1 已交付）：形式化证明 Lean 落地——Yildirim 公式 L 版展开与 BGS 引理逐条移植（2026-10-25）.",
    "[2] 攻防 XLII-S7.2（d1 已交付）：数值件 F——超支撑素数项可忽略性实测（|S_a|≈2.05）.",
    "[3] 攻防 XLII-S7.3（d1 已交付）：骨头 1——BGS 引理 5 超支撑推广（N1）.",
    "[4] 攻防 XLII-S7.4（d1 已交付）：骨头 2——ε–λ 联动（N2，n2_linkage O(ε)）.",
    "[5] 攻防 XLII-S7.5（d1 已交付）：骨头 3——离线项一致版本（N3，BGS 余项跨 λ 一致）.",
    "[6] 攻防 XLII-S7.6（d1 已交付）：SW 常数显式化——L(s,χ₅) 素数项显式界 (C,c).",
    "[7] 本工作 Lean 工程（2026-10-27）：C:\\proj2\\QRH\\S7_1_Core.lean / S7_1_Main.lean / S7_1_Stage3.lean "
        "（Lean 4 v4.34.0-rc2 + mathlib）；编译证据 build_qrh_l4b.txt（2604 jobs 全绿）.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
