# -*- coding: utf-8 -*-
"""攻防 XLII · S7.1 落档：形式化证明 Lean 落地——Yildirim 公式 (7) L 版展开 + BGS 引理 3-5 逐条移植
+ 离线误差精细控制。项目：C:\\proj2\\QRH（S7_1_Core.lean / S7_1_Main.lean / QRH.lean）。
母本：gen_s7_doc.py（S7 定稿样式链）。
"""
import os
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

TARGET = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.1-形式化证明Lean落地-Yildirim公式L版展开与BGS引理逐条移植.docx"

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
para("路2攻防XLII—S7.1：形式化证明 Lean 落地", style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("（Yildirim 公式 (7) 的 L(s,χ_5) 版展开 + BGS 引理 3-5 逐条移植 + 离线误差精细控制）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S7.1 形式化", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 25 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S7.1 把 S7 的构造骨架落成 Lean 4 形式化项目（工作区 C:\\proj2\\QRH）。任务三件套："
     "Yildirim 公式 (7) 的 L(s,χ_5) 版展开、BGS 引理 3-5 逐条移植、离线误差精细控制。工具链："
     "lean-toolchain 钉 v4.34.0-rc2（elan 已装），lakefile.toml 注册顶级 lean_lib QRH（BSD 同款布局："
     "根文件 QRH.lean + 子目录 QRH\\S7_1_Core.lean、QRH\\S7_1_Main.lean）。mathlib Windows 侧聚合 olean"
     "（Mathlib.olean）缺、lake build 全量触发 ir 链读取失败——绕行：Core/Main 改 import 具体模块"
     "（Data.Real.Basic、Trigonometric.Basic、Positivity、Continuity、Topology.Algebra.Order.Field、"
     "Exp、Log.Basic 的 olean 均存在并验证可用），不依赖聚合。阶段成果：**Core 件五个真证明件全过**"
     "（无 sorry、无 axiom）：sin(1/√2)≠0、K̂ 偶性、K̂(0)=1、K̂ 频域衰减界（三角不等式）、f0 连续性；"
     "**Main 骨架件可编译**（axiom 占位四条 L1-L4 + 定理 S7.1 陈述 + s71_main sorry，符合先占位后击破"
     "惯例）；**QRH 根模块可编译**。离线误差精细控制：f0−fε 的 L1 偏差界 ≤ 2ε·(√2·|sin(1/√2)|)⁻¹、"
     "pair_const_eps_bias（C1 显式）已列入击破清单——依赖 IntervalIntegral 模块（Windows 侧 olean 缺，"
     "mathlib 全量构建后恢复）。诚实边界：本档为阶段结果——Core 真证明 + Main 骨架可编译；五条"
     "（S7 §7 ①-⑤）的完整证明（含 BGS 引理 3-5 逐条移植的 Lean 实现）按 Stage 1-4 击破清单推进，"
     "见 §7。", space_after=6)

para("关键词：Lean 4；Yildirim 公式 (7)；BGS 引理；L(s,χ_5) 配对公式；离线误差；形式化证明",
     space_after=10)

# ---------- 1 承接 ----------
h1t("1　承接与形式化目标")
para("S7 文档（路2攻防XLII-S7）§7 诚实披露五条待形式化项：① 公式 (7) 的 L 版展开；② BGS 引理 "
     "3-5 逐条移植；③ 离线误差 O(ε) 显式常数；④ 复共轭对称转和型引理；⑤ Selberg 类公理 (i)-(iv) "
     "标注。S7.1 的任务即把 ①-⑤ 落成 Lean 4 可编译的形式化骨架：以 S7 定理 S7.1（弱实部假设下 "
     "A_L(K) ≤ C_MT+O(ε)+o(1)）为目标定理，先 Core 真证明件（核的解析性质——配对常数偏差控制的"
     "底层事实），再 Main 骨架件（分析引理 axiom 占位 + 主定理陈述），最后按击破清单逐条降级。")
para("工作区约定：用户指令「lean项目：C:\\proj2 内容存入：C:\\proj2\\QRH」——即既有 Lean 攻坚现场 "
     "C:\\proj2（BSD/OrderPreservingBijection/QRH 子目录共存）内新建 QRH 顶级模块。BSD 现场历史产物"
     "（build_*/fix_* 脚本）保持不动。")

# ---------- 2 工具链 ----------
h1t("2　工具链与 mathlib 绕行")
h2t("2.1　版本与环境")
para("lean-toolchain 钉 leanprover/lean4:v4.34.0-rc2，与 elan 已装 toolchain "
     "（leanprover--lean4---v4.34.0-rc2）匹配。调用入口：PATH 前置 $env:USERPROFILE\\.elan\\bin 后 "
     "lake env lean <file>——正确解析到 v4.34.0-rc2，不触发 elan 下载新版本（裸跑 lean --version "
     "会触发 v4.35.0 下载卡住，已多次验证规避）。lakefile.toml 追加 [[lean_lib]] name=\"QRH\"——"
     "BSD 同款顶级模块布局；srcDir/root 指向 QRH 子目录的写法报模块路径错误，已回退。")
h2t("2.2　mathlib 阻塞与绕行策略")
para("lake build QRH 首跑触发 mathlib 全量构建：失败——C:\\proj\\mathlib4-master 经 junction 软链接，"
     "Windows 侧部分 .ir 读取失败（如 Mathlib\\Tactic\\Ring\\Common.ir），聚合 Mathlib.olean 缺。"
     "绕行：Core/Main 不 import Mathlib 聚合，改 import 具体模块并逐一验证 olean 存在："
     "Data.Real.Basic、Analysis.SpecialFunctions.Trigonometric.Basic、Tactic.Positivity、"
     "Tactic.Continuity、Topology.Algebra.Order.Field、Analysis.SpecialFunctions.Exp、"
     "Analysis.SpecialFunctions.Log.Basic 全部 True；Data.Real.Pi、MeasureTheory.Integral."
     "IntervalIntegral False（后者为离线误差 L1 界所需——mathlib 全量构建后恢复）。")

# ---------- 3 Core 真证明件 ----------
h1t("3　Core 真证明件（编译全过，无 sorry 无 axiom）")
para("S7_1_Core.lean 是 S7.1 的底层真证明件：五个引理全部通过 lean 编译（0 错误）。全部为配对常数"
     "偏差控制的解析事实——核 Khat（MT 最优核 f0 的余弦傅里叶变换、解析式 cos(√2x)/(√2·sin(1/√2))）"
     "在 u=0 与频域远端的良定义与界。编译迭代 12 轮（build_core1..12.txt）——主要修错集中在 K̂(0)=1"
     "的商化简（sqrt 2 的非平凡代数：div_lt_one 分母正性、π 下界引理名 two_le_pi、field_simp 与 "
     "mul_div_assoc/div_self 组合、Real.sq_sqrt 显式替换 √2²=2）与 sin(1/√2)>0 的界链"
     "（0<1/√2<1<2≤π，sin_pos_of_pos_of_lt_pi）。")
h2t("3.1　sin_inv_sqrt2_ne_zero：sin(1/√2) ≠ 0（分母良定义）")
para("证明链：0 < 1/√2（positivity）→ 1 < √2（Real.sqrt_one 还原 + sqrt_lt_sqrt，1<2）→ "
     "1/√2 < 1（div_lt_one 的 mpr，分母 √2>0）→ 1 < π（two_le_pi：2 ≤ π，linarith）→ "
     "1/√2 < π（linarith）→ sin 在 (0,π) 上正（Real.sin_pos_of_pos_of_lt_pi）→ 非零。"
     "——K̂ 分母 √2·sin(1/√2) 良定义，且 |sin(1/√2)| 的绝对值化在 Khat_abs_le 中可做。")
h2t("3.2　Khat_neg：K̂ 偶性（复共轭对称的频域表现）")
para("unfold 后 ring_nf 自动闭合——sin 参数中 −2π(−u) 与 +2πu 的环化简使两侧 sin 参数归一为同一"
     "形式。偶性是差型配对转和型（BGS 引理 4 的复共轭对称）的核侧前提。")
h2t("3.3　Khat_zero：K̂(0)=1（对角主项 K̂(0)·N_L 的归一化）")
para("展开 K̂(0) = [sin(√2/2)/√2 + sin(√2/2)/√2]/(√2·sin(1/√2))——hsq2（√2/2 = 1/√2）"
     "与 hmerge（两项合并）后 field_simp [sin_inv_sqrt2_ne_zero] 归一化 → 主目标 "
     "2·sin(1/√2)/sin(1/√2) = √2²——mul_div_assoc 提出 2·(sin/sin)、div_self 消商、"
     "Real.sq_sqrt 替换 √2²=2、norm_num 闭合。这是配对常数对角主项 = 1 的核侧事实。")
h2t("3.4　Khat_abs_le：频域衰减界（素数项窗口定量）")
para("|K̂(u)| ≤ [1/|√2−2πu| + 1/|√2+2πu|]/(√2·|sin(1/√2)|)：三角不等式 "
     "（abs_add_le）→ 逐项 |sin|/|den| ≤ 1/|den|（abs_sin_le_one + div_le_div_of_nonneg_right）→ "
     "整体乘 (√2·|sin(1/√2)|)⁻¹（hden：abs_inv + abs_mul + √2>0 绝对值化；hpos：乘积正性）——"
     "mul_le_mul_of_nonneg_right 闭合。这是数值件 E 的核频域窄支撑的解析版本：K̂(δlogp) 只在 "
     "p≈1 有贡献的定量依据（分母在 u=±√2/(2π) 处一阶零点——衰减界在远端给出 O(1/u) 形态）。")
h2t("3.5　f0_continuous：f0 连续性（核正则化论证基础件）")
para("f0(x)=cos(√2x)/(√2·sin(1/√2)) 常数分母 + cos 连续——continuity tactic 直接闭合。"
     "这是 ε 正则化（Lamzouri η_ε 机制）中 f0 作为基核的分析正则性前提。")

# ---------- 4 Main 骨架件 ----------
h1t("4　Main 骨架件（axiom 占位 + 主定理陈述；可编译）")
para("S7_1_Main.lean 按「先 sorry/axiom 占位保证编译通过→逐个击破」惯例搭骨架，import "
     "QRH.S7_1_Core + Exp + Log.Basic + Data.Complex.Basic（open scoped BigOperators）。编译迭代 7 轮"
     "（build_main1..7.txt）——修错集中在 ZeroSet 的 reducibility（def→abbrev，Membership 实例解析）、"
     "∑ 符号（Σ'→∑'、in→∈ 的 Finset 绑定语法）。")
h2t("4.1　抽象对象")
para("ZeroSet = Set ℂ（abbrev）；ConjClosed（复共轭不变性，starRingEnd）；pairConstant "
     "(K δ N Z : ℝ→ℝ，本轮 def 返回 1 占位——配对常数公式 A=1+Σ_{Δ≠0}K(δΔ)²/N_Z 的正式实现列击破清单)；"
     "WeakRealPart（BGS 弱实部假设占位：|β−1/2|≤1/(2logT)，对 T^{3/8}<γ≤T）；zerosLChi5 = {z | True}"
     "（L(s,χ_5) 零点集占位）+ zerosLChi5_conj_closed 引理（simp 过）。")
h2t("4.2　axiom 占位四条（L1-L4）")
para("L1 landau_explicit_L：Landau/Weil 显式公式 L 版（Yildirim 公式 (6) 机制）——零点加权和 ↔ "
     "素数幂加权和 + 平凡项 + 离线项（对 L(s,χ) 无条件；数学陈述在 docstring）。L2 "
     "siegel_walfisz_chi5：模 5 点态 Siegel–Walfisz |Σ_{n≤x}Λ(n)χ_5(n)| ≤ c·x·e^{−c′√logx}（无条件、"
     "子指数——固定模替代 GRH-PNT 的素数项层事实，S7 §3.2）。L3 pair_sum_expansion：配对和展开 = "
     "对角主项 + 素数项 + 离线误差（弱实部假设压下）。L4 offcritical_small：离线误差 o(1)（弱假设 + "
     "T^{3/8} 切割，BGS 引理机制）。")
h2t("4.3　定理 S7.1 形式化陈述")
para("s71_main：∀ T≥1、WeakRealPart T zerosLChi5、ε>0，∃ C1,C2≥0：pairConstant Khat "
     "(logT/2π) (logT/2π) zerosLChi5 ≤ C_MT + C1·ε + C2——即 A_L(K) ≤ C_MT+O(ε)+o(1) 的骨架形式"
     "（C_MT = 1/2+(1/√2)cot(1/√2) = 1.3274992963 由 Core 定义；证明体 sorry 占位）。")

# ---------- 5 离线误差 ----------
h1t("5　离线误差精细控制（路线与依赖）")
para("离线误差两层：其一为 ε 正则化偏差（C_MT 最优核 f0 → 正则化核 fε = f0·w_ε，w_ε 为端点过渡窗"
     "min(1, (1/2−|x|)/ε)——配对常数偏差 |A(fε)−A(f0)| ≤ C1·ε，C1 由 f0 的 L1 偏差界给出）；"
     "其二为弱实部假设下的零点离线项（T^{3/8} 切割，BGS 引理机制 → o(1)）。本档落成：Core 已含 "
     "f0/fε/w_eps 定义与 f0 连续性；f0_sub_feps_L1_bound（|f0−fε| 的 L1 偏差 ≤ "
     "2ε·(√2·|sin(1/√2)|)⁻¹）与 pair_const_eps_bias（C1 显式）列入击破清单——依赖 "
     "MeasureTheory.Integral.IntervalIntegral 模块（Windows 侧 olean 缺：lake build mathlib 全量"
     "构建后恢复；届时 Core 文件尾注释的 import 恢复点启用）。诚实披露：离线误差的显式常数在"
     "本档尚未形式化——Stage 2-3 目标。")

# ---------- 6 编译证据 ----------
h1t("6　编译证据与产物")
para("三模块全部编译通过（lean v4.34.0-rc2，lake env lean 直接编译验证）：Core（build_core12 终轮 "
     "exit=0）、Main（build_main7 终轮 exit=0，仅剩预期占位警告：sorry 使用 + unused variable）、"
     "QRH 根（build_root2 exit=0）。产物 olean 均已落盘：QRH.olean、QRH\\S7_1_Core.olean、"
     "QRH\\S7_1_Main.olean（C:\\proj2\\.lake\\build\\lib\\lean\\）。迭代证据链保留：build_core1..12.txt、"
     "build_main1..7.txt、build_root1..2.txt。")
caption("表 1　S7.1 模块结构与编译状态")
hdr = ["模块", "内容", "真证明/占位", "编译状态"]
rows_tab = [
    ["S7_1_Core.lean", "Khat 定义、sin(1/√2)≠0、偶性、K(0)=1、频域衰减界、f0 连续性", "真证明件 5 个", "0 错误（12 轮迭代）"],
    ["S7_1_Main.lean", "ZeroSet/ConjClosed/pairConstant/WeakRealPart、axiom L1-L4、定理 S7.1", "axiom 4 条 + s71_main sorry", "0 错误（7 轮迭代）"],
    ["QRH.lean", "库根：import Core+Main + example 复述 s71_main", "骨架", "0 错误"],
]
add_table(hdr, rows_tab, widths=[3.0, 6.5, 2.6, 3.5])
para("注：Core 无 sorry 无 axiom（真证明件全过）；Main 的 axiom/sorry 为合法占位（先占位后击破惯例）。",
     size=9, indent_chars=0, space_after=6)

# ---------- 7 击破清单 ----------
h1t("7　击破清单与 Stage 1-4")
para("Stage 1（Core 收尾）：Khat_zero 化简完成后恢复文件尾注释段——f0_sub_feps_L1_bound（ε L1 偏差"
     "界 ≤ 2ε·(√2·|sin(1/√2)|)⁻¹，需 IntervalIntegral）、pair_const_eps_bias（由 L1 界 + Lipschitz "
     "推出，C1 显式）、C_MT<4/3 数值上界、mathlib 聚合恢复 import Mathlib。Stage 2（离线误差）："
     "fε 的 L1 收敛 → 配对常数偏差 O(ε) 显式常数（S7 §7 ③）。Stage 3（BGS 逐条移植）：引理 3-5 的 "
     "Lean 实现——引理 3（弱实部假设下零点离线项 o(1)）、引理 4（复共轭对称转和型——与 Khat_neg "
     "衔接）、引理 5（supp r⊂[−1,1] 核构造——λ≤1/2 域，S6 C_MT 框架）（S7 §7 ②④）；L1-L4 axiom "
     "逐个降级为定理。Stage 4（Selberg 类标注）：类公理 (i)-(iv)（Euler 积、解析延拓、函数方程、"
     "Ramsey 型系数界）对 L(s,χ_5) 逐条标注（S7 §7 ⑤）。")
h2t("7.1　Stage 3+：超支撑断层三件套（推 1 路线的理论闭合）")
para("讨论判定：「干到 1」与 S7 之间存在理论断层——S7 闭路只覆盖 λ≤1/2（BGS 引理 5 的 supp "
     "r⊂[−1,1] 硬条件），而 XLII 推 1 路线要求 λ_eff(T)=(logT)^q→∞（核宽 a→0、谱支撑无限扩大）。"
     "超支撑下 K̂_a(δlogp)=f̂0(au) 失去频域窄支撑保护，素数项不再自动小。分析修正：目标量级放宽"
     "——Abel 求和 + 点态 SW（|ψ(t;χ_5)|≤c·t·e^{−c′√logt}）给出 S(X)=O(√X·poly(logX))，"
     "相对对角主项 N_L~(X/2π)logX 为 o(1)——**无需 e^{−c√logX} 指数级衰减**，A→1 路径在素数项层"
     "打通。据此挂入三条闭合件：")
para("① BGS 引理 5 超支撑推广（N1）：supp r⊂[−a,a]（a→0 任意）时配对展开的对角主项系数与离线项"
     "形态不变——引理 5 重证（λ≤1/2 → 一般 a）。② ε–λ 联动（N2）：核宽 a(λ) 与正则化 ε 的显式"
     "匹配——a 不能快于 ε 容忍，O(ε) 与超支撑余项同时压到 1（推 1 的枢纽）。③ 离线项一致版本"
     "（N3）：弱实部假设下 o(1) 跨 λ 一致成立——K̂ 宽支撑拉入远零点的一致余项（引理 3 超支撑推广）。"
     "配套三条新真证明件：Abel 求和引理、K̂_a 一致界（偶核版本、二阶主导：|K̂_a(δlogp)−f̂0(0)|≤"
     "½|K̂″(0)|(aδlogp)²+O(a⁴δ⁴log⁴p)，一阶校正恒为零；数值件 F 实测 K̂″(0)≈−3.06、ratio=1.000 "
     "@ aδ≤3×10⁻³）、N_L 对数增长下界（N_L≥c·T·logT）。数值件 F 已落地（S7.2 文档）：超支撑素数项"
     "实测（λ 取 logT、X 扫 10⁴→10⁸）——|S_a|/N_L 单调衰减至 1×10⁻⁸、|S_a|≈2.05 有界收敛，"
     "验证 √X·poly(logX) 量级与二阶校正 (aδ)²·log²p 形态（偶核：一阶校正恒为零，原「一阶校正 "
     "a·δ·logp」表述已修正）。")

# ---------- 8 判定 ----------
h1t("8　判定总结")
para("S7.1 形式化项目落地：工作区 C:\\proj2\\QRH（三个 .lean + lakefile 注册 + olean 产物），"
     "mathlib 具体模块绕行成功。Core 真证明件五引理全过（核解析性质——sin 非零、偶性、K(0)=1、"
     "频域衰减界、连续性——0 错误）；Main 骨架可编译（axiom 占位 L1-L4 + 定理 S7.1 陈述）；"
     "离线误差（f0−fε L1 界与 C1 显式）路线明确、依赖模块已标识。**阶段判定：S7.1 从「构造骨架」"
     "推进到「可编译形式化骨架 + 底层真证明件全绿」**——0.6725 严格化的最后形式化步骤已实质启动。"
     "本轮新增：超支撑断层三件套（N1 引理 5 超支撑推广、N2 ε–λ 联动、N3 离线项一致版本）与三条"
     "配套真证明件（Abel 求和、K̂_a 一致界、N_L 对数下界）挂入击破清单 Stage 3+（推 1 路线的理论"
     "闭合）。数值件 F 已落地（S7.2 文档，d1 已交付）：超支撑素数项 O(√X·poly(logX)) 相对 N_L 为 "
     "o(1)（实测 |S_a|/N_L≤1×10⁻⁸、有界收敛），无需指数级衰减；校正形态二阶主导（偶核，一阶项"
     "恒为零）——N2 敏感量修正为 (aδ)²。剩余：Stage 1-4 + Stage 3+ 按清单逐条推进。诚实边界："
     "主定理 s71_main 的证明体仍为 sorry 占位（axiom 依赖待击破），本档交付的是「可编译骨架 + "
     "Core 真证明」的阶段性结果。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] Yildirim C Y. The pair correlation of zeros of Dirichlet L-functions and primes in arithmetic progressions[J]. manuscripta mathematica, 1991, 72(1): 325-334（公式 (6) Landau 型显式公式无条件、公式 (7) 积分形式——S7.1 L 版展开的对象）.",
    "[2] Murty R, Zaharescu A. Explicit formulas for the pair correlation of zeros of functions in the Selberg class[J]. Forum Mathematicum, 2002, 14: 65-83（Selberg 类 GRH-free 配对显式公式——显式公式层锚点）.",
    "[3] Baluyot D, Goldston D A, Suriajaya A I, Turnage-Butterbaugh C L. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（引理 3-5：弱实部假设、复共轭对称、核支撑 supp r⊂[−1,1]——S7.1 逐条移植对象）.",
    "[4] 攻防 XLII-S7（d1 已交付）：Yildirim 方法移植闭路——定理 S7.1 骨架、数值件 E、§7 五条待形式化项 ①-⑤.",
    "[5] 本工作 Lean 项目（可复跑）：C:\\proj2\\QRH\\S7_1_Core.lean / S7_1_Main.lean / QRH.lean + lakefile.toml；编译证据 build_core1..12.txt、build_main1..7.txt、build_root1..2.txt；olean 产物 C:\\proj2\\.lake\\build\\lib\\lean\\QRH*.olean.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
