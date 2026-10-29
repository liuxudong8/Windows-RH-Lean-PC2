# -*- coding: utf-8 -*-
"""S7.12 中文落档生成脚本（无模板新建）。"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.12-fourierCos真定义与fourierCos_scale缩放律真证.docx'
BLACK = RGBColor(0, 0, 0)
HEADER_SHADE = 'D9D9D9'


def set_style_font(st, cn='宋体', en='Times New Roman', size=12, bold=False):
    st.font.name = en
    st.font.size = Pt(size)
    st.font.bold = bold
    st.font.color.rgb = BLACK
    rPr = st.element.get_or_add_rPr()
    rFonts = rPr.get_or_add_rFonts()
    rFonts.set(qn('w:eastAsia'), cn)


def set_run_font(r, cn='宋体', en='Times New Roman', size=12, bold=False):
    r.font.name = en
    r.font.size = Pt(size)
    r.font.bold = bold
    r.font.color.rgb = BLACK
    rPr = r._element.get_or_add_rPr()
    rFonts = rPr.get_or_add_rFonts()
    rFonts.set(qn('w:eastAsia'), cn)


def set_first_line_chars(p, chars=200):
    pPr = p._p.get_or_add_pPr()
    ind = pPr.find(qn('w:ind'))
    if ind is None:
        ind = OxmlElement('w:ind')
        pPr.append(ind)
    ind.set(qn('w:firstLineChars'), str(chars))
    ind.set(qn('w:firstLine'), '480')


def shade_cell(cell, color):
    tcPr = cell._tc.get_or_add_tcPr()
    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'), 'clear')
    shd.set(qn('w:color'), 'auto')
    shd.set(qn('w:fill'), color)
    vAlign = tcPr.find(qn('w:vAlign'))
    if vAlign is not None:
        vAlign.addprevious(shd)
    else:
        tcPr.append(shd)


doc = Document()

# 页面设置
sec = doc.sections[0]
sec.page_width = Cm(21.0)
sec.page_height = Cm(29.7)
sec.top_margin = Cm(2.5)
sec.bottom_margin = Cm(2.5)
sec.left_margin = Cm(2.5)
sec.right_margin = Cm(2.5)

# 页脚页码（居中 PAGE 域）
fp = sec.footer.paragraphs[0]
fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
fld1 = OxmlElement('w:fldChar'); fld1.set(qn('w:fldCharType'), 'begin')
instr = OxmlElement('w:instrText'); instr.set(qn('xml:space'), 'preserve'); instr.text = 'PAGE'
fld2 = OxmlElement('w:fldChar'); fld2.set(qn('w:fldCharType'), 'end')
r0 = fp.add_run()
r0._r.append(fld1); r0._r.append(instr); r0._r.append(fld2)
set_run_font(r0, size=9)

# 样式
set_style_font(doc.styles['Normal'], '宋体', 'Times New Roman', 12, False)
doc.styles['Normal'].paragraph_format.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
doc.styles['Normal'].paragraph_format.line_spacing = 1.5
doc.styles['Normal'].paragraph_format.space_before = Pt(0)
doc.styles['Normal'].paragraph_format.space_after = Pt(0)

set_style_font(doc.styles['Title'], '黑体', 'Times New Roman', 18, True)
doc.styles['Title'].paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
doc.styles['Title'].paragraph_format.space_after = Pt(18)

set_style_font(doc.styles['Heading 1'], '黑体', 'Times New Roman', 16, True)
doc.styles['Heading 1'].paragraph_format.space_before = Pt(14)
doc.styles['Heading 1'].paragraph_format.space_after = Pt(6)
set_style_font(doc.styles['Heading 2'], '黑体', 'Times New Roman', 14, True)
doc.styles['Heading 2'].paragraph_format.space_before = Pt(11)
doc.styles['Heading 2'].paragraph_format.space_after = Pt(5)
set_style_font(doc.styles['Heading 3'], '黑体', 'Times New Roman', 12, True)
doc.styles['Heading 3'].paragraph_format.space_before = Pt(9)
doc.styles['Heading 3'].paragraph_format.space_after = Pt(4)


def add_heading(text, level):
    p = doc.add_heading(level=level)
    r = p.add_run(text)
    sizes = {1: 16, 2: 14, 3: 12}
    set_run_font(r, '黑体', 'Times New Roman', sizes[level], True)
    p.paragraph_format.keep_with_next = True
    return p


def add_body(text, indent=True):
    p = doc.add_paragraph()
    r = p.add_run(text)
    set_run_font(r, '宋体', 'Times New Roman', 12, False)
    p.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
    p.paragraph_format.line_spacing = 1.5
    p.paragraph_format.space_before = Pt(0)
    p.paragraph_format.space_after = Pt(0)
    if indent:
        set_first_line_chars(p, 200)
    return p


# ============ 正文 ============
p = doc.add_paragraph(style='Title')
r = p.add_run('路 2 攻防 XLII-S7.12：fourierCos 本体真定义与 fourierCos_scale 缩放律真证')
set_run_font(r, '黑体', 'Times New Roman', 18, True)

p = doc.add_paragraph()
r = p.add_run('（积分/解析层件 · 2026-10-29 · 落档 d1 惯例）')
set_run_font(r, '楷体', 'Times New Roman', 12, False)
p.alignment = WD_ALIGN_PARAGRAPH.CENTER
p.paragraph_format.space_after = Pt(12)

add_heading('1  结论摘要', 1)
add_body('本轮完成 QRH Lean 形式化项目（C:\\proj2\\QRH）积分/解析层第 5 件：频域抽象算子 fourierCos 由 axiom 降为 Bochner 积分真定义，其缩放律 fourierCos_scale（r̂_a(z) = r̂(az)）由 axiom 降为真证 lemma。全量 lake build QRH 通过：2704 jobs、0 error、0 warning。')
add_body('同时修正一处旧结论：S7.3 文档与代码注释此前判定"fourierCos_scale 真证需积分层（MeasureTheory.IntervalIntegral 或 Riemann 积分模块），待 mathlib 聚合生成后恢复"。本轮实证否决该判断——mathlib v4.34 已将 Bochner 积分重构为 Integral/Bochner/ 子目录，全空间 Haar 变量替换定理 Measure.integral_comp_inv_mul_left 在现有"具体模块 import"路线下即可用，且不要求被积函数正则性。缩放律因此无需等待任何模块聚合，直接闭证。')
add_body('残余命名 axiom 净减 1（fourierCos_scale 出账）；n1_diag_invariant、n1_offdiag_scale_eq 两个依赖使用点陈述与编译均不受影响。')

add_heading('2  背景与定位', 1)
add_heading('2.1  fourierCos 在 S7.1 形式化中的角色', 2)
add_body('fourierCos 是频域抽象算子：对配对核 K 与频点 z，给出 ∫ K(x)·cos(2πzx) dx，对应谱对偶体系中的核 Fourier 变换 r̂(z)。S7.1 定理骨架中，配对常数 A_L 的上界链条经核 Fourier 变换的 L¹ 界与频域衰减件传递；S7.3 的 N1 超支撑结构件 n1_diag_invariant（z = 0 特化）与 n1_offdiag_scale_eq（z = 2δ 特化）均以 rw [fourierCos_scale ...] 为唯一依赖。')
add_heading('2.2  axiom 积压状态', 2)
add_body('Core §4b 原为三个命名 axiom：fourierCos（载体）、fourierCos_Khat（K̂ 闭式）、khat_lipschitz（带限整函数导数件）；Stage3 N1 区另有 fourierCos_scale（频域缩放）。本轮目标为 fourierCos 本体与 fourierCos_scale 两项出账，fourierCos_Khat 与 khat_lipschitz 保持 axiom（前者需核闭式解析层，后者需导数件，另属攻坚线）。')

add_heading('3  口径变更一：fourierCos 本体真定义', 1)
add_body('Core §4b 中 axiom fourierCos 替换为非计算真定义：')
add_body('fourierCos K z := ∫ x : ℝ, K(x)·cos(2π·z·x) dx', indent=False)
add_body('语义与口径：积分为 Bochner 积分，测度为 ℝ 上 volume；被积函数不可积时 mathlib 积分惯例为 0（与 normL1 真定义同机制）。调用签名 fourierCos K z 未变，primeSum 权重、prime_weight_bounds_Khat 等全部使用点无需改动。注释同步更新为真定义说明。')

add_heading('4  口径变更二：fourierCos_scale 缩放律真证', 1)
add_heading('4.1  陈述', 2)
add_body('对任意 r : ℝ → ℝ（无正则性前提）、0 < a、z : ℝ：', indent=False)
add_body('fourierCos (scaleKernel a r) z = fourierCos r (a·z)', indent=False)
add_body('其中 scaleKernel a r := λx, (1/a)·r(x/a)。')
add_heading('4.2  证明链', 2)
add_body('四段 calc 链（与 scaleKernel_L1_invariant 2026-10-27 真证同款技术栈）：')
add_body('（1）提出常数因子：被积函数 (1/a)·r(x/a)·cos(2πzx) 经 integral_congr_ae + ring 重构为 (1/a)·(r(x/a)·cos(2πzx))，再用 integral_const_mul 提出 1/a。')
add_body('（2）被积函数重构：x/a 改写为 a⁻¹·x（div_eq_inv_mul），cos 参数同步改写为 2π·z·(a·(a⁻¹·x))——后者需 field_simp [ne_of_gt ha] 消去 a⁻¹，这是本步唯一的场运算点。')
add_body('（3）Haar 变量替换：直接调用 Measure.integral_comp_inv_mul_left，得 ∫ r(a⁻¹·x)·cos(2π·z·(a·(a⁻¹·x))) dx = |a|·∫ r(y)·cos(2π·z·(a·y)) dy。该定理为全空间版本，对任意函数成立，无需可测性前提。')
add_body('（4）cos 参数重写与消因子：z·(a·y) 重写为 (a·z)·y（integral_congr_ae + ring），末项 (1/a)·(|a|·X) 用 abs_of_pos ha 与 field_simp [ne_of_gt ha] 消为 X，即 fourierCos r (a·z)。')
add_heading('4.3  关键件与使用点', 2)
add_body('可用件：integral_const_mul、integral_congr_ae（filter_upwards 逐点架构）、Measure.integral_comp_inv_mul_left（全空间、无正则性前提）——全部位于 Integral/Bochner/Basic.olean，项目现有 import 链内。使用点 n1_diag_invariant（rw [fourierCos_scale a ha r 0]）与 n1_offdiag_scale_eq（rw [fourierCos_scale a ha r (2·δ)]）签名一字未改，照常编译。')

add_heading('5  旧结论修正：IntervalIntegral 依赖判断的推翻', 1)
add_heading('5.1  旧判断', 2)
add_body('S7.3 落档及代码注释记录："fourierCos_scale 真证需积分层（MeasureTheory.IntervalIntegral 或 Riemann 积分模块）——mathlib 聚合生成后恢复"，依据是探针确认 IntervalIntegral.olean 缺失、顶层 Integral.olean 缺失。')
add_heading('5.2  实证否决', 2)
add_body('（a）缺失判断本身正确：IntervalIntegral.olean、顶层 Integral.olean、旧名 Bochner.olean 均不存在。')
add_body('（b）结论错误：v4.34 将 Bochner 积分重构为 Integral/Bochner/ 子目录，∫ 记号、integral_const_mul、integral_congr_ae、integral_map 均位于 Bochner/Basic.olean（与 normL1 真定义同源，项目早已在 import 链内）；且 Measure.integral_comp_inv_mul_left 是全空间 Haar 变量替换、无被积函数正则性前提。故缩放律证明无需 IntervalIntegral，也无需等待 mathlib 聚合。')
add_heading('5.3  死路清单（勿重试）', 2)
add_body('（a）import Mathlib.MeasureTheory.Integral.Integral：顶层 olean 缺失，必失败。')
add_body('（b）全空间逐点版 integral_congr：v4.34 不存在（仅 integral_congr_ae 与 L1 类版本），一律用 integral_congr_ae + filter_upwards / ae_of_all。')
add_body('（c）integral_map 通用化：该定理要求 AEMeasurable φ 与 AEStronglyMeasurable f（被积函数），对任意 r 不可用；测度层缩放公式 volume_map_mul_left / map_mul_left 在 v4.34 不存在。全空间变量替换唯一可靠出口是 Measure.integral_comp_inv_mul_left。')

add_heading('6  构建验证', 1)
add_body('全量 lake build QRH：2704 jobs、exit = 0、0 error、0 warning（日志 C:\\proj2\\QRH\\dbg_build_fourier.txt）。三版探针（FourierProbe.lean：Import 缺失验证、命名空间陷阱验证、积分件清单验证）完成使命后已删除。')

add_heading('7  残余命名 axiom 状态表', 1)
rows = [
    ('名称', '位置', '状态'),
    ('fourierCos_Khat', 'Core §4b', '命名 axiom（K̂ 闭式，解析层件）'),
    ('khat_lipschitz', 'Core §4b', '命名 axiom（带限整函数导数件）'),
    ('bgs5_khat_fourier_supp', 'Main', '命名 axiom（BGS 引理 5 频域支撑）'),
    ('siegel_walfisz_chi5', 'Main', '命名 axiom（SW 定理 χ₅ 版）'),
    ('landau_explicit_L', 'Main', '命名 axiom（Landau 显式公式 L 版）'),
    ('f0_sub_feps_L1_bound', 'Stage3', '命名 axiom（精确陈述，真证需积分层）'),
    ('N_L_lower_bound', 'Stage3', '命名 axiom（结构件，S6 零点计数）'),
    ('n2_linkage', 'Stage3', '命名 axiom（结构件，S7.4 定理 N2）'),
    ('n3_remainder_uniform', 'Stage3', '命名 axiom（结构件，S7.5 定理 N3）'),
]
tbl = doc.add_table(rows=len(rows), cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
widths = [Cm(4.2), Cm(3.2), Cm(8.6)]
for i, row_data in enumerate(rows):
    for j, val in enumerate(row_data):
        cell = tbl.rows[i].cells[j]
        cell.width = widths[j]
        cell.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
        para = cell.paragraphs[0]
        para.alignment = WD_ALIGN_PARAGRAPH.LEFT
        para.paragraph_format.space_before = Pt(2)
        para.paragraph_format.space_after = Pt(2)
        para.paragraph_format.line_spacing = 1.0
        r = para.add_run(val)
        set_run_font(r, '宋体', 'Times New Roman', 10.5, i == 0)
        if i == 0:
            para.alignment = WD_ALIGN_PARAGRAPH.CENTER
            shade_cell(cell, HEADER_SHADE)
    if i == 0:
        trPr = tbl.rows[i]._tr.get_or_add_trPr()
        tblHeader = OxmlElement('w:tblHeader')
        tblHeader.set(qn('w:val'), 'true')
        trPr.append(tblHeader)
    trPr = tbl.rows[i]._tr.get_or_add_trPr()
    cantSplit = OxmlElement('w:cantSplit')
    trPr.append(cantSplit)

add_body('')
add_body('注：上表为 2026-10-29 快照。fourierCos 与 fourierCos_scale 已出账；其余 axiom 各归属独立攻坚线，见各章记录。')

doc.save(OUT)
print('saved:', OUT)
