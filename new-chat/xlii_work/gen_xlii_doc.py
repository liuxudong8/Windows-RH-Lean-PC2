# -*- coding: utf-8 -*-
"""攻防 XLII S0 数值定向落档：论文级 Word 生成（无模板创建）。
数据源：qrh_work/xlii_s0_v3.json、xlii_s0_gue_sim.json；图：xlii_work/*_300.png。
"""
import json
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
WORK = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xlii_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLII-全尺度GUE配对与在线比例1-o(1)-S0数值定向-口径修正与超GUE排斥.docx"

v3 = json.load(open(QRH + r"\xlii_s0_v3.json", encoding="utf-8"))
gue = json.load(open(QRH + r"\xlii_s0_gue_sim.json", encoding="utf-8"))

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
    # 移除主题字体属性，避免显式字体被 theme 覆盖
    for attr in ("w:asciiTheme", "w:hAnsiTheme", "w:eastAsiaTheme"):
        if rf.get(qn(attr)):
            del rf.attrib[qn(attr)]
    rf.set(qn("w:ascii"), ascii_); rf.set(qn("w:hAnsi"), ascii_); rf.set(qn("w:eastAsia"), east)

n = doc.styles["Normal"]
set_fonts(n, "宋体", size=10.5)

tstyle = doc.styles["Title"]
set_fonts(tstyle, "黑体", size=16, bold=True)
tstyle.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
tstyle.paragraph_format.space_after = Pt(6)
pf = n.paragraph_format
pf.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
pf.line_spacing = 1.5
pf.space_before = Pt(0); pf.space_after = Pt(0)
ind = n.element.get_or_add_pPr().get_or_add_ind()
ind.set(qn("w:firstLineChars"), "200"); ind.set(qn("w:firstLine"), "420")

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

# 表格单元格段落格式在 style_cell() 中逐格显式设置（字体/缩进/行距），不依赖命名样式

# ---------- 辅助 ----------
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
    p = doc.add_heading(text, level=1)
    return p

def h2t(text):
    p = doc.add_heading(text, level=2)
    return p

def caption(text):
    p = doc.add_paragraph(text, style="Caption")
    return p

def set_cell_borders(cell, top=8, bottom=8, insideH=None):
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

def add_table(headers, rows, widths=None, header_east="黑体"):
    t = doc.add_table(rows=len(rows) + 1, cols=len(headers))
    t.alignment = WD_TABLE_ALIGNMENT.CENTER
    t.autofit = False
    tblPr = t._tbl.tblPr
    # 表头行跨页重复
    trPr = t.rows[0]._tr.get_or_add_trPr()
    th = OxmlElement("w:tblHeader"); th.set(qn("w:val"), "true"); trPr.append(th)
    # 行不跨页
    for r_ in t.rows:
        rp = r_._tr.get_or_add_trPr()
        cs = OxmlElement("w:cantSplit"); rp.append(cs)
    # 三线表边框（顶 1pt、底 1pt、表头下 0.5pt 用每行下边框近似）
    for j, htxt in enumerate(headers):
        c = t.rows[0].cells[j]
        set_cell_borders(c, top=8, bottom=4)
        style_cell(c, htxt, bold=True, align=WD_ALIGN_PARAGRAPH.CENTER, east=header_east)
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
para("路2攻防XLII—全尺度GUE配对与在线比例1−o(1)：S0数值定向", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（口径修正、超GUE排斥与理论对应）", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S0 生死门判定", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 24 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII 承接 XLI 主线「干到 1」——把前提假设 (H2) 升级为 λ(T)→∞ 的全尺度 GUE 配对（强 Montgomery 型对固定模实特征 L(s,χ₅)），由 Lamzouri Proposition 2.1 直接给出配对常数 A→1、并集在线简单零点比例 →1−o(1)。本篇完成 S0 数值定向（生死门判定）。方法：T=6×10⁵ 零点数据（ζ 999354 根、L(χ₅) 1149836 根），核族 K_a(u)=sinc²(πu/a)、谱支撑 λ_eff=π/a，配对常数 A=1+ΣK²/N（有序全对），局部归一化 u=|Δ|·ρ(t_mid)，双侧 GUE/泊松对照。结果：A(λ) 全曲线（λ_eff∈[0.39,31.4]）实测紧贴双侧 GUE 预测、窄端单调逼近 1 无反弹（a=0.5→0.1 时 A−1 由 1.49e-2 降至 1.3e-4）；极小间距无重零点迹象（s_min=0.0123/0.0133，s<0.01 计数 0）；实测系统性低于 GUE（超 GUE 排斥），GUE 模拟排除有限 N 伪影，段间漂移显示负偏差随 T 收敛。三项口径修正：λ_eff 换算钉死（XLI 旧口径倒挂）、L 密度 −1 项校准（最近邻均值 0.9197→1.0027）、全局 δ 与局部 ρ 差 0.7%（XLI 数值结论不翻转）。判定：S0 通过、进 S1。理论对应三层：Montgomery 配对猜想（GUE 普适类）、β=2 水平排斥 O(a³)（普适形状）、超 GUE 负偏差归因有限 T 算术项（BGS 误差/Montgomery F(α)≥|α| 同源）。", space_after=6)

para("关键词：全尺度 GUE 配对；在线简单零点比例 1−o(1)；配对常数；超 GUE 排斥；口径修正", space_after=10)

# ---------- 1 承接与主线 ----------
h1t("1　承接与主线")
h2t("1.1　XLI 坐标与「干到 1」路线")
para("攻防 XLI（d1 已交付）在拟随机（GUE）前提下闭合 QRH 常数机制：单族配对常数 A_min=1.0079（ζ）/1.0114（L）（核 fejer_a0.5），7/8 门槛 A≤1.125 达标、余量 0.1171/0.1136；分解论证给出并集在线简单零点比例 ≈0.990；定理形态为纯假设（弱前提），前提 (H1)(H2) 可数值直接检验。XLI §8 将下一阶段主线立为：把 (H2) 升级为 λ(T)→∞ 的全尺度 GUE 配对——强 Montgomery 型对固定模实特征 L(s,χ₅)（框架内开放构造）——则 Proposition 2.1 直接给出 A→1、在线比例 →1−o(1)，即文献「强配对猜想 ⟹ 几乎全部零点简单」的框架内版本；7/8 门槛保持为现行定理坐标。用户否决 31/32 门槛（7/8 为现行 AI 值），主线目标定为「干到 1」。")
h2t("1.2　四阶段规划与 S0 生死门")
para("「干到 1」规划为 S0-S3 四阶段：S0 数值定向（生死门：A(λ) 长程行为是否单调逼近 1 且无反弹）；S1 理论构造（λ(T) 增长方案与 A=1+O(λ^{-1}) 收敛推导、并集加权定理形态）；S2 数值验证（Weil 显式公式实部口径注入敏感性：N_off·δ²·(logx)² 累积可测性）；S3 闭环落档。本篇执行 S0 并给出判定。")

# ---------- 2 数值口径与方法 ----------
h1t("2　数值口径与方法")
h2t("2.1　数据与零点密度")
para("零点数据 T=6×10⁵、剔除 t<300：ζ 999354 根、L(s,χ₅) 1149836 根。归一化密度 ρ_ζ(t)=log(t/2π)/2π；L 族密度 ρ_L=(1/2π)[log(t/(2π))−1+log5] 的常数项 −1 经校准为错误：去 −1 后最近邻均值 nn_mean 由 0.9197 升至 1.0027（ζ 恰为 1.0000），校准因子 ≈1.087。全局口径 δ=logT/2π=2.1175（XLI 沿用）在宽带数据下 u 平均≈1.74≠1，宽核放大归一化误差——S0 改局部归一化 u=|Δ|·ρ(t_mid)。")
h2t("2.2　核族与谱支撑换算")
para("核 K_a(u)=sinc²(πu/a)。谱支撑 λ_eff(a)=π/a（Fourier 约定 e^{-2πiξu}），换算见表 1。XLI 文档「fejer_a0.5 谱支撑≈0.5」为倒挂错误口径——fejer_a0.5 实际 λ_eff=π/0.5=6.28≫1/2，远超无条件框架允许的 λ≤1/2（该自由度正来自拟随机放宽）。")
caption("表 1　核宽 a 与谱支撑 λ_eff=π/a 换算（节选）")
add_table(["a", "0.1", "0.25", "0.5", "1.0", "2.0", "4.0", "8.0"],
          [["λ_eff=π/a", "31.42", "12.57", "6.28", "3.14", "1.57", "0.79", "0.39"]])
para("", indent_chars=0, space_after=2)
h2t("2.3　配对常数、归一化与双侧对照")
para("A(K)=1+Σ_{有序对}K(δΔ)²/N（有序全对 i≠j 两侧都计入；Proposition 2.1 的 ΣK² 即该口径）。GUE 双侧预测 GUE2(a)=1+2∫₀^∞(1−sinc²πu)sinc⁴(πu/a)du（二点相关 ρ₂=1−sinc²πu）；泊松基线 Poi2(a)=1+2a/3。初版单侧对照（缺因子 2）把有序全对的和按半量计，造成「超 Poisson 上偏/负偏差」假警报——最小几何验证（常数强度泊松窄带、ρ≡1 均匀点、解析 ∫sinc⁴=1/3）定位为约定问题而非代码 bug；终版采用双侧对照。")
h2t("2.4　三项口径修正")
para("(1) λ_eff 换算：fejer_a0.5 实为 6.28 而非 0.5（倒挂修正）；(2) L 密度 −1 项：去 −1 后 nn_mean=1.0027；(3) 全局 δ 与局部 ρ：ζ a0.5 全局口径 1.00789（复现 audit6 分毫不差）对局部口径 1.01494，差 0.7%，XLI 结论（余量 0.11-0.12）不翻转——但 XLI 数值声明（表 1/表 3、ρ_L 公式、λ_eff 标注）在下次修订时需同步披露。")

# ---------- 3 S0 结果 ----------
h1t("3　S0 结果")
h2t("3.1　A(λ) 全曲线（表 2、图 1）")
AG = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
rows2 = []
for a in AG:
    s = str(a)
    rows2.append([a, v3["lambda_eff"][s], v3["A_zeta_fine"][s], v3["A_L_fine"][s],
                  v3["A_GUE2"][s], v3["A_Poisson2"][s], v3["verdict"]["zeta_dev_vs_GUE2"][s]])
caption("表 2　配对常数 A(λ) 全曲线（T=6×10⁵，局部归一化，有序全对；ζ−GUE2 为实测对双侧 GUE 预测的偏差）")
add_table(["a", "λ_eff=π/a", "A_ζ", "A_L", "GUE2", "Poi2", "ζ−GUE2"], rows2)
para("", indent_chars=0, space_after=2)
para("读数：(i) 三层结构 Poisson>GUE>实测——排斥压低配对和；(ii) 实测紧贴 GUE2（宽端偏差 −0.020~−0.022 平台），全尺度无反弹；(iii) 窄端单调→1：a=0.5→0.1 时 A_ζ−1 由 0.01494 单调降至 0.00013，A_L−1 由 0.01440 降至 0.00017——单调判定 True。")
add_picture_centered(WORK + r"\xlii_s0_fig1_300.png", 14.5)
caption("图 1　A(λ) 全曲线 vs 双侧 GUE/Poisson（T=6×10⁵，局部归一化）：实测（ζ 黑、L 红）紧贴 GUE 预测（蓝），三层结构、7/8 门槛与 C_MT 参照，窄端单调→1 无反弹")
h2t("3.2　极小间距与重零点探测（表 3）")
mz, ml = v3["min_gap"]["zeta"], v3["min_gap"]["L"]
rows3 = [
    ["ζ", mz["n"], round(mz["s_min"], 5), mz["counts"]["0.05"], mz["counts"]["0.01"],
     mz["counts"]["0.005"], mz["counts"]["0.001"], mz["gue_pred"]["0.01"]],
    ["L", ml["n"], round(ml["s_min"], 5), ml["counts"]["0.05"], ml["counts"]["0.01"],
     ml["counts"]["0.005"], ml["counts"]["0.001"], ml["gue_pred"]["0.01"]],
]
caption("表 3　极小间距与重零点计数（s<ε 为归一化最近邻间距小于 ε 的零点数；GUE 列为理论预测）")
add_table(["族", "n", "s_min", "s<0.05", "s<0.01", "s<0.005", "s<0.001", "GUE(s<0.01)"], rows3)
para("", indent_chars=0, space_after=2)
para("s<0.01 计数 0（GUE 预测 1.1/1.2）——无重零点迹象。结构重零点（其配对项 K(0)=1 不随核尺度消失）会阻止 A→1，此处排除该障碍。")
h2t("3.3　有限 T 涨落标定（表 4）")
rows4 = []
for fam in ("zeta", "L"):
    for a in ("0.3", "0.5", "1.0", "2.0"):
        d = v3["drift"][fam][a]
        rows4.append([a, "ζ" if fam == "zeta" else "L"] + [round(x, 6) for x in d["vals"]] +
                     [d["max_adj"], d["range"]])
caption("表 4　A 的段间漂移（5 段，300−6×10⁵，局部归一化；相邻为相邻段最大差，极差为全程差）")
add_table(["a", "族", "段1", "段2", "段3", "段4", "段5", "相邻max", "极差"], rows4)
para("", indent_chars=0, space_after=2)
para("判定：窄端信号远超漂移（ζ a0.5 相邻 ≤0.00092、极差 0.00184；L ≤0.00074/0.0014）；宽端负偏差（−0.02 平台）超段间漂移约 3 倍——系统信号。负偏差随高度收敛：ζ a0.5 五段 1.0138→1.0154 向 GUE2=1.0177 靠拢，L 同向——有限 T 算术项签名。")
h2t("3.4　GUE 模拟对照")
para("GUE 矩阵模拟（N=4000×12，谱归一化校准后 nn_mean=1.0000）：A_sim 与 GUE2 理论几乎重合（正偏 +0.001~+0.006：a0.5 1.01863 对 1.01771、a8 5.39678 对 5.39162）；实测系统性低于 GUE 且偏差超段间漂移约 3 倍——负偏差为真实超 GUE 排斥信号，非有限 N 伪影。方向（排斥更强→配对更少→A 更小→比例更近 1）支持「干到 1」。")
add_picture_centered(WORK + r"\xlii_s0_fig2_300.png", 14.5)
caption("图 2　A−1 收敛速率（log-log）：实测（ζ 黑、L 红）与 GUE2 理论（蓝）平行下降、整体略低——超 GUE 排斥；GUE 模拟（紫三角）≈理论，排除有限 N 伪影；窄端 O(a³) 斜率")

# ---------- 4 判定与理论对应 ----------
h1t("4　判定与理论对应")
h2t("4.1　S0 生死门判定")
para("四条件逐项核验：A(λ) 单调逼近 1 无反弹（通过）；全曲线贴 GUE（通过）；无重零点迹象（通过）；有限 T 涨落可控（通过）。判定：S0 通过，主线可进 S1。")
h2t("4.2　三层理论对应")
para("(i) 曲线整体贴 GUE ⟺ Montgomery 配对猜想/RMT 普适类：对 ζ 为猜想（Odlyzko 在 10²² 高度强数值验证）；对固定模实特征 L(s,χ₅) 文献中无无条件版——正是 (H2)/(H2′)。数据在低高度（T=6×10⁵）呈现 GUE 结构，与普适性在低高度即显现的已知经验一致。")
para("(ii) 窄端 A−1~O(a³) ⟺ GUE β=2 水平排斥普适形状：1−sinc²πu~π²u²/3（u→0，二点相关二次零点），窗内 sinc⁴≈1，∫₀^a u²du~a³；Dyson 对数气体对 GUE 类是定理、对 ζ 是猜想。数据独立复现 β=2 斜率（图 2 实测与 GUE2 平行），排除泊松 β=0（A−1~a）与辛系综 β=4（A−1~a⁵）——最强锚点。")
para("(iii) 超 GUE 负偏差 ⟺ 有限 T 算术项：BGS Lemma 5 误差 O_f(1/√logT) 带核依赖常数；Montgomery F(α)≥|α|（|α|<1，素数项给出非平凡下界，GUE 预测取等）为同源结构，Parseval 下翻译为实空间配对和偏差（符号与形状待 S1a 严格推导）。决定性证据：段间漂移显示负偏差随 T 收敛（低 t 段偏离多、高 t 段向 GUE 靠拢）——「偏差=随 T 衰减的算术项」的直接签名；GUE 模拟排除有限 N 修正方向。")
h2t("4.3　诚实边界")
para("① 数据只到 T=6×10⁵、λ_eff≤31.4；「无限高度 λ(T)→∞ 全尺度」仍是假设 (H2′)，不是定理。② 超 GUE 排斥边缘显著（ζ a0.5 偏差 −0.00277，超相邻段间漂移 0.00092 约 3 倍），暂不作定理前提，只记方向有利。③ XLI 旧口径数值（全局 δ、含 −1 的 ρ_L、λ_eff≈0.5 标注）与本文档不一致，结论不翻转但需在 XLI 修订时披露。④ 核族扫描有限（fejer 系），未穷尽变分解空间。")

# ---------- 5 下一步 ----------
h1t("5　下一步：S1 拆解")
h2t("5.1　S1a 算术项归因（层 3 理论对应定量化）")
para("① Parseval：把 A(a)−GUE2(a) 翻译成 F(α,T)−|α|（α∈(0,1)），对照 Montgomery 下界超出量，验证符号与形状；② 衰减律：5 段上拟合 Δ(a;T)~c(a)/logT 或 c(a)/√logT，区分 BGS 误差结构；③ 核依赖常数：fejer/sinc/gauss 三族偏差按 Fourier 支撑平滑性排序（audit6 数据现成）。")
h2t("5.2　S1b λ(T) 方案构造")
para("(H2′) 显式化（λ(T)→∞ 的强 Montgomery 型，含增长速率与误差形状）；A=1+O(λ^{-1}) 收敛推导；结构重零点项并入（s<0.01 已排除）；并集加权 → 在线比例 1−o(1) 的定理形态。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（Proposition 2.1（N₀ˢ≥2Σ1−ΣK²）、Lemma 3.2（最优核、C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963）、Remark 3.4（C_η≥C_MT））——XLI 全文回读.",
    "[2] Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（Lemma 5：无条件配对公式、误差 O_f(1/√logT)、权 w(z)=4/(4−z²)；BGS 推广至固定模 L(χ) 为开放构造）.",
    "[3] Özlük A E. On the pair correlation of zeros of Dirichlet L-functions（1982，GRH 下至少 11/12 简单，带权）——经 Kandhil-Languasco-Moree 引言转述核实.",
    "[4] Kandhil N, Languasco A, Moree P. Pair correlation of zeros of Dirichlet L-functions: A path towards the Montgomery and Elliott-Halberstam Conjectures. arXiv:2411.19762（Yıldırım 定理/Conjecture 1：跨字符平均配对相关，GRH 前提）——XLI 全文精读.",
    "[5] Carneiro E, Milinovich M B, Ramos A P. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913（F 平均 0.9303-1.3208、含 Dirichlet L 函数族）.",
    "[6] Odlyzko A M. The 10^22-nd zero of the Riemann zeta function（10¹⁰ 个零点数值验证 RH 与 GUE 配对相关）.",
    "[7] 攻防 XLII 数值件（本工作，Anaconda python 可复跑）：qrh_work/xlii_s0.py（v1 全局口径）、xlii_s0_v2.py（v2 局部、含错 L 密度）、xlii_s0_v3.py（终版：局部归一化+双侧 GUE+L 校准）、xlii_s0_check.py（泊松模拟/ρ₂ 查错）、xlii_s0_debug.py（2 倍因子最小验证）、xlii_s0_gue.py（GUE 模拟）、xlii_s0_plot.py（出图）；结果 xlii_s0_v3.json、xlii_s0_gue_sim.json；零点数据 zeros_T6e5.npz（T=6×10⁵、ζ 999354/L 1149836 根）.",
    "[8] 攻防 XLI（d1 已交付）：拟随机并集定理条件形态——7/8 门槛、fejer_a0.5 最优核、分解论证、前提可靠性三层.",
    "[9] 攻防 XL（d1 已交付）：配对侧无条件界理论构造——0.6725 常数缺口属 QRH 机制；攻防 XXXIX（S4）：在线比例桥余项精细形态.",
]
for rtext in refs:
    para(rtext, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
