# -*- coding: utf-8 -*-
"""骨架A讨论稿生成脚本（无模板创建）"""
import os
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.enum.section import WD_SECTION
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx"

doc = Document()

# ---------- 页面设置 ----------
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
sec.top_margin = sec.bottom_margin = sec.left_margin = sec.right_margin = Cm(2.5)

def set_font(run, cn_font, en_font, size, bold=False):
    run.font.size = Pt(size)
    run.font.bold = bold
    run.font.color.rgb = RGBColor(0, 0, 0)
    run.font.name = en_font
    r = run._element.rPr.rFonts
    r.set(qn('w:eastAsia'), cn_font)

def set_para(p, align=WD_ALIGN_PARAGRAPH.JUSTIFY, first_indent=True,
             line15=True, before=0, after=0, keep_next=False):
    pf = p.paragraph_format
    pf.alignment = align
    if first_indent:
        pf.first_line_indent = Pt(21)  # 2字符（10.5pt）
    else:
        pf.first_line_indent = Pt(0)
    if line15:
        pf.line_spacing_rule = WD_LINE_SPACING.ONE_POINT_FIVE
    else:
        pf.line_spacing_rule = WD_LINE_SPACING.SINGLE
    pf.space_before = Pt(before)
    pf.space_after = Pt(after)
    if keep_next:
        pf.keep_with_next = True

def add_title(text):
    p = doc.add_paragraph()
    p.style = doc.styles['Title']
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    run = p.add_run(text)
    set_font(run, '黑体', 'Times New Roman', 18, bold=True)
    p.paragraph_format.space_after = Pt(18)
    return p

def add_h1(text):
    p = doc.add_paragraph()
    p.style = doc.styles['Heading 1']
    run = p.add_run(text)
    set_font(run, '黑体', 'Times New Roman', 12, bold=True)
    set_para(p, align=WD_ALIGN_PARAGRAPH.LEFT, first_indent=False,
             before=14, after=6, keep_next=True)
    return p

def add_h2(text):
    p = doc.add_paragraph()
    p.style = doc.styles['Heading 2']
    run = p.add_run(text)
    set_font(run, '黑体', 'Times New Roman', 10.5, bold=True)
    set_para(p, align=WD_ALIGN_PARAGRAPH.LEFT, first_indent=False,
             before=11, after=5, keep_next=True)
    return p

def add_body(text, bold_lead=None):
    p = doc.add_paragraph()
    p.style = doc.styles['Normal']
    if bold_lead:
        r0 = p.add_run(bold_lead)
        set_font(r0, '宋体', 'Times New Roman', 10.5, bold=True)
    run = p.add_run(text)
    set_font(run, '宋体', 'Times New Roman', 10.5)
    set_para(p, before=0, after=0)
    return p

def add_ref(text):
    p = doc.add_paragraph()
    p.style = doc.styles['Normal']
    run = p.add_run(text)
    set_font(run, '宋体', 'Times New Roman', 9)
    set_para(p, align=WD_ALIGN_PARAGRAPH.LEFT, first_indent=False,
             line15=False, after=3)
    pf = p.paragraph_format
    pf.left_indent = Pt(18)
    pf.first_line_indent = Pt(-18)
    return p

# ---------- 页脚页码 ----------
footer = sec.footer
fp = footer.paragraphs[0]
fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
fld = OxmlElement('w:fldSimple')
fld.set(qn('w:instr'), 'PAGE \\* MERGEFORMAT')
fp._p.append(fld)

# ---------- TOC 域 ----------
def add_toc():
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    run = p.add_run('目  录')
    set_font(run, '黑体', 'Times New Roman', 12, bold=True)
    p.paragraph_format.space_after = Pt(12)
    p2 = doc.add_paragraph()
    fld = OxmlElement('w:fldSimple')
    fld.set(qn('w:instr'), r'TOC \o "1-2" \h \z \u')
    p2._p.append(fld)
    return p2

# =============== 正文 ===============
add_title('弱 BSD 秩 1 的 Hecke 显式公式重证明')
add_title('骨架 A 讨论稿（K = ℚ(√5)）')
doc.add_paragraph()

add_toc()

# 分页
from docx.enum.text import WD_BREAK
pb = doc.add_paragraph()
pb.add_run().add_break(WD_BREAK.PAGE)

add_h1('1  引言：目标与已知边界')
add_h2('1.1  弱 BSD 的已知状态')
add_body('设 K 为全实域，E/K 为椭圆曲线。弱 BSD 断言：解析秩（L(E,s) 在 s = 1 的零点阶）等于代数秩（Mordell–Weil 秩）。对 K = ℚ 上解析秩 ≤ 1 的模椭圆曲线，该断言已由 Gross–Zagier [1] 与 Kolyvagin [2] 证明：解析秩 0 推出代数秩 0，解析秩 1 推出代数秩 1。对全实域，Zhang [3] 将 Gross–Zagier 公式推广到 GL₂ 情形，提供了同样的 Heegner 点机制。因此，“解析秩 ≤ 1 ⟹ 代数秩 = 解析秩”是定理，不是猜想。')
add_body('未证方向恰是反过来的那一步：代数秩 ≥ 1 时能否推出解析秩 ≥ 1，特别是代数秩 1 ⟹ L′(E,1) ≠ 0。这是弱 BSD 真正开放的部分，也是本文骨架 A 的目标——在 K = ℚ(√5) 上为曲线 37a1 构造一个不依赖 Gross–Zagier 的 Hecke 显式公式论证。')
add_h2('1.2  谱对偶路线的承接')
add_body('在 K-GRH 谱对偶路线中，本项目 2026-10-05 的 G7 核验判死了一条关键链：在测试函数族 h(t) = (1+t²)⁻ᵏ 下，非平凡零点虚部 γ ≥ 6.65 使零点侧坍缩为 O(10⁻³) 级余项（真实 Σ_零点 约 6×10⁻⁴），谱侧的 O(1) 平衡中零点贡献根本不参与——“谱点集 = 零点虚部集”的全局配对在数值端不成立。文档中此前标称的约 7% 系统差实为三个 O(1) 项的偶然抵消，不是 Σ_零点。')
add_body('BSD 落点与此本质不同：解析秩是 L(E,s) 在 s = 1 邻域的局部整数值（零点阶），不涉及零点虚部的全局集合。G7 的量级失配在 BSD 侧自动消失。切换到此主线是结构性的，不是修补。')
add_h2('1.3  路线总览')
add_body('骨架 A 的论证由四层构成：Hecke 标签（模性 + Ramanujan 界）、链 2（素理想 ↔ 轨道长度）、显式公式分解（Weil 显式公式的一阶 Taylor）、反证（假设 L′(E,1) = 0 导出矛盾）。数值端已完成 Hecke 层（1142 个素理想、Ramanujan 违反 0 例）；判秩所需的完整 L 函数数值延拓留待补。')

add_h1('2  对象与模性')
add_h2('2.1  主曲线')
add_body('主曲线取 E = 37a1：y² + y = x³ − x，判别式 Δ = −37，坏约化仅在 𝔭 | 37 处。作为 K = ℚ(√5) 上的曲线（系数属于 ℤ ⊂ 𝒪_K），其代数秩 ≥ 1 由有理点 P = (0,0) 构造性给出：LMFDB [6] 记录 E(ℚ) 秩为 1，Mordell–Weil 生成元即 (0,0)，故 P 无限阶。')
add_body('选择理由：ℚ 端秩 1 已知是双刃剑——它保证“代数秩 ≥ 1”这一未证方向假设侧的构造性输入成立；而 L′(E,1) ≠ 0 在 ℚ 端已是定理（弱 BSD 秩 1 情形），真正的新对象是 K = ℚ(√5) 端。')
add_h2('2.2  模性')
add_body('Freitas–Le Hung–Siksek [4]（2015）证明：实二次域上所有椭圆曲线是模的。故存在权 2 全纯 Hilbert 模本征形式 f，使 L(E,s) = L(f,s)；后者是 degree 2 自守 L 函数，中心点 s = 1，函数方程符号由根数决定。本文不利用 ℚ(√5) 的类数或单位群的特殊结构——它们是链 2 的输入而非模性的输入。')

add_h1('3  无条件输入')
add_h2('3.1  Ramanujan 界')
add_body('对权 2 全纯 Hilbert 模本征形式，好素 𝔭 处 Hecke 特征值满足 |a_𝔭| ≤ 2√Nm(𝔭)。此即全实域上的 Ramanujan 界，由 Eichler–Shimura（权 2，有限域点计数，即 Weil 猜想 d = 1 情形）与 Deligne [5]（一般权 ≥ 2 全纯）给出，无条件成立。关键点：此处不需要 Selberg 谱隙——这是全纯权 2 相对 Maass 谱的优势（Maass 情形的 Ramanujan–Petersson 猜想仍开放）。')
add_h2('3.2  链 2：素理想与轨道长度')
add_body('本项目链 2（定理 10 核心成果）断言：对 K = ℚ(√5) 的希尔伯特模曲面上单位群轨道，轨道长度 ℓ₁ + ℓ₂ 与素理想范数对数满足逐点恒等：ℓ₁ + ℓ₂ = log Nm(𝔭)。排序配对（保序）已经数值验证。这一恒等是 Hecke 加权显式公式中“素数项与轨道项”的接口：显式公式的素数项 Σ a_𝔭 Λ(Nm(𝔭))/Nm(𝔭)^s 与迹公式几何侧的轨道积分在 ℓ = log Nm 下逐项一致。')

add_h1('4  显式公式分解（骨架核心）')
add_h2('4.1  Weil 显式公式（Hecke 加权）')
add_body('对 L(f,s)（中心 s = 1，degree 2），取偶、速降测试函数 h，Weil 显式公式给出：Σ_ρ h(γ) = 主项 − Σ_𝔭 a_𝔭 Λ(Nm(𝔭))/Nm(𝔭)^(1/2) · ĥ(log Nm(𝔭)/(2π)) + Γ 项 + 常数项，其中零点 ρ = 1/2 + iγ，ĥ 为傅里叶变换。')
add_body('形式警告（G7 教训）：本项目在 K-GRH 线已两次栽在显式公式的“形式”上——其一，(1+t²)⁻ᵏ 族下零点侧坍缩为余项；其二，pt5c 口径中三个 O(1) 项偶然抵消冒充 Σ_零点（文档标称的约 7% 系统差）。故 4.1 的精确系数（对数常数项、平凡零点口径、Γ 因子符号）必须按标准 Weil 公式约定逐项钉死。本文先给出骨架，系数核对列为待补。')
add_h2('4.2  一阶 Taylor 分解')
add_body('若 L(E,s) 在 s = 1 处一阶零点，则 L′(E,1) 等于其一阶系数。反证假设 L′(E,1) = 0（即解析秩 ≥ 2），显式公式在 s = 1 邻域的展开要求：主项(s) − Σ_𝔭 a_𝔭 Λ(Nm(𝔭))/Nm(𝔭)^s + Γ′(s) 项 = 0 至足够阶。逐项控制：Γ 项是已知函数；素数项由 Ramanujan 界 |a_𝔭| ≤ 2√Nm 与链 2 的轨道计数控制。')
add_h2('4.3  反证骨架')
add_body('假设 L′(E,1) = 0。则 s → 1 时主项与素数项加 Γ′项的差须高阶相消。候选矛盾源：(a) 素数项的主项（由 Ramanujan 界与素理想计数共同控制）不随测试函数族的调整而消失；(b) 链 2 的逐点恒等把素数项的权重固定在 ℓ = log Nm 上，使几何侧与算术侧在逐项层面一致，没有吸收残差的自由度。')
add_body('卡点诚实标注：目前 (a)(b) 只是候选矛盾源，“全消条件确实违反 Ramanujan 界与计数”这一步尚未构成严格证明。骨架 A 的数学未闭合处正是此处；本文不声称完成证明。')
add_h2('4.4  与 G7 的对比')
add_body('G7 的失败是零点侧坍缩（全局量）；BSD 的解析秩是 s = 1 局部量，不涉及 γ ≥ 6 的全局零点集，权重坍缩问题消失。但 4.1 的形式闭合问题（主项、素数项、Γ 项的精确系数）在 BSD 侧同样存在——这是骨架 A 需要“上一个量级”的真正关口。')

add_h1('5  数值支撑')
add_h2('5.1  Hecke 端表（K = ℚ(√5)，E = 37a1，Nm ≤ 20000）')
add_body('素理想总数 1142；Ramanujan 违反 0/1142；惰性素理论核对 a_{p²} = a_p² − 2p（好约化）全部吻合（p = 2 特征 2 修正后 a₄ = 0；p = 37 坏约化排除）。a_𝔭 前 24 项（节选）：a₄ = 0，a₅ = −2，a₉ = 3，a₁₁ = −5，a₁₉ = 0，a₂₉ = 6，a₃₁ = −4，a₄₁ = −9，a₄₉ = −13，a₅₉ = 8。')

# 表格：惰性素理论核对示例
t = doc.add_table(rows=6, cols=4)
t.style = 'Table Grid'
t.alignment = WD_TABLE_ALIGNMENT.CENTER
headers = ['p（惰性）', 'Nm(𝔭)', 'a_𝔭（计算）', 'a_p² − 2p（理论）']
rows_data = [
    ['2', '4', '0', '0'],
    ['3', '9', '3', '3'],
    ['7', '49', '−13', '−13'],
    ['13', '169', '−22', '−22'],
    ['17', '289', '−34', '−34'],
]
# 填表头
for j, htxt in enumerate(headers):
    c = t.cell(0, j)
    c.text = ''
    p = c.paragraphs[0]
    run = p.add_run(htxt)
    set_font(run, '宋体', 'Times New Roman', 10.5, bold=True)
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'), 'clear'); shd.set(qn('w:fill'), 'D9D9D9')
    c._tc.get_or_add_tcPr().append(shd)
    c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
# 数据行（a4.py 核对值：a_{p²} = a_p² − 2p 全 ✓）
for i, row in enumerate(rows_data, start=1):
    pv, nm, av, tv = row
    for j, val in enumerate([pv, nm, av, tv]):
        c = t.cell(i, j)
        c.text = ''
        p = c.paragraphs[0]
        run = p.add_run(val)
        set_font(run, '宋体', 'Times New Roman', 10.5)
        p.alignment = WD_ALIGN_PARAGRAPH.CENTER
        p.paragraph_format.first_line_indent = Pt(0)
        p.paragraph_format.line_spacing_rule = WD_LINE_SPACING.SINGLE
        c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
# cantSplit + tblHeader
for row in t.rows:
    trPr = row._tr.get_or_add_trPr()
    cs = OxmlElement('w:cantSplit'); trPr.append(cs)
for j in range(len(headers)):
    trPr = t.rows[0]._tr.get_or_add_trPr()
    th = OxmlElement('w:tblHeader'); trPr.append(th)

add_body('惰性素（Nm = p²）Hecke 特征值理论核对示例（完整 1142 素理想核对见脚本 a4.py 输出，全部吻合；p = 37 为坏约化，理论式不适用，排除）。', bold_lead='注：')

add_h2('5.2  欧拉积闭合')
add_body('欧拉积在 Re s > 3/2 绝对收敛：L_cut(2.0) = 0.894，L_cut(1.5) = 0.700。该截断值在收敛域内稳定，不触及 s = 1 的解析延拓信息。')
add_h2('5.3  方法学修正')
add_body('素数项探针 ν(s) = Σ a_𝔭 log q / q^s 不判秩：对秩 1 曲线 37a1，拟合 A ≈ 0，秩 1 曲线同样收敛。原因：L(E,s) 在 s = 1 的零点来自解析延拓层（Γ 因子与函数方程），欧拉积本身在 s = 1 收敛。判秩必须走完整 L 函数数值延拓，不能靠素数项探针。')
add_h2('5.4  待补清单')
add_body('(i) degree-2 数值延拓：先在 ℚ 端 37a1 上验证 L(E,1) = 0 且 L′(E,1) ≠ 0，方法闭环后迁移到 ℚ(√5)；(ii) 4.1 显式公式的精确形态按标准 Weil 公式核对；(iii) 4.3 全消矛盾的严格化。')

add_h1('6  结论与下一步')
add_body('骨架 A 给出了弱 BSD 秩 1 未证方向（代数秩 1 ⟹ 解析秩 1）的一条独立论证框架：Hecke 标签（无条件）+ 链 2（已成立）+ 显式公式分解（骨架）+ 反证（卡点明确）。数值端 Hecke 层全绿；判秩数值延拓与显式公式精确系数是下一步的两条闭合路径。')

# 参考文献
add_h1('参考文献')
refs = [
    '[1] Gross B, Zagier D. Heegner points and derivatives of L-series[J]. Inventiones Mathematicae, 1986, 84(2): 225–320.',
    '[2] Kolyvagin V A. Euler systems[M]//The Grothendieck Festschrift. Progress in Mathematics, 1990, 87: 435–483.',
    '[3] Zhang S W. Gross–Zagier formula for GL₂[J]. Asian Journal of Mathematics, 2001, 5(2): 183–290.',
    '[4] Freitas N, Le Hung B V, Siksek S. Elliptic curves over real quadratic fields are modular[J]. Mathematische Annalen, 2015, 363(3–4): 789–813.（卷页待核）',
    '[5] Deligne P. La conjecture de Weil. I[J]. Publications Mathématiques de l\u2019IHÉS, 1974, 43: 273–307.',
    '[6] LMFDB. Elliptic curve 37.a1[EB/OL]. [2026-10-05]. https://www.lmfdb.org/EllipticCurve/Q/37a/.',
]
for r in refs:
    add_ref(r)

doc.save(OUT)
print('SAVED:', OUT)
