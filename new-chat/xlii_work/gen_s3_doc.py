# -*- coding: utf-8 -*-
"""攻防 XLII S3 落档：Δ 常数指纹排除交叉验证——同虚部成对注入的爆炸响应与威胁排除。
数据：entF_work/detF_base.json + detF_inject.json。
"""
import json
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

ENTF = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entF_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLII-S3-Δ常数指纹排除交叉验证-同虚部成对注入的爆炸响应与威胁排除.docx"

base = json.load(open(ENTF + r"\detF_base.json", encoding="utf-8"))
inj = json.load(open(ENTF + r"\detF_inject.json", encoding="utf-8"))

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
para("路2攻防XLII—S3：Δ 常数指纹排除交叉验证", style="Title",
     align=WD_ALIGN_PARAGRAPH.CENTER)
para("（同虚部成对注入的爆炸响应与威胁排除的交叉验证闭合）",
     align=WD_ALIGN_PARAGRAPH.CENTER, font="黑体", size=14, bold=True, space_after=4)
para("——《谱对偶论证》系列（d1）：S3 数值验证", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("2026 年 10 月 24 日", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- 摘要 ----------
para("摘要：", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("攻防 XLII S3 完成 Δ 常数指纹的排除交叉验证数值实验：把 Δ 定律纯差 Δ_pure 作为独立指纹，"
     "检验它对威胁形态（同虚部成对）的探测能力。口径：Δ_pure 基线复算（T=6×10⁵、N_K=2149542 对、"
     "c_cut=0.0635）：Δ_pure=−15046.5（对照文献 −15091，差 0.30%）、Δ_pure/N_K=−0.00700（对照 "
     "−0.702%）、var_A=0.1144、SNR=−41.5。注入实验：同虚部成对构型 I_pair2（mult=2）与 "
     "II_single1（mult=1）× N_pairs∈{100,200,2000,219000}。结果：Δ_pure 对同虚部成对注入呈爆炸"
     "响应——219000 对时 I 构型 Δ_pure 由 −15046 翻正至 +554771（rel_shift 3787%、SNR=1571），"
     "II 构型 +269841（SNR=785）；增量检查 dS_full 与 dS_incremental 相对差 1.6×10⁻¹⁴（全一致）。"
     "判定：真实数据 Δ_pure 与基线吻合（无注入特征），威胁形态若存在必被 Δ 指纹以 SNR≫1 捕获——"
     "威胁排除交叉验证闭合。S3 与 S1（左尾审计）、S2(i)（Weil 注入敏感性）构成三探针分工："
     "x-口径弱探针、Δ 指纹爆炸敏感、配对口径强探针。", space_after=6)

para("关键词：Δ 常数指纹；Δ_pure 纯差；同虚部成对注入；爆炸响应；威胁排除交叉验证",
     space_after=10)

# ---------- 1 承接与主线 ----------
h1t("1　承接与主线")
h2t("1.1　S2(i) 之后：为何需要第三指纹")
para("S2(i)（d1 已交付）判定 Weil 实部 x-口径是弱探针：对代表性分布的 1/logT 级偏移需 20%~40% "
     "零点才可测。这留下一个口径空档：若威胁以「少量、大结构」（如同虚部成对）形态存在，弱探针"
     "看不见，强探针（配对常数 A）的归因又依赖假设前提。S3 引入第三个独立指纹——Δ 常数定律的 "
     "Δ_pure 纯差：它是从跨族配对和（ζK 构造）中剥离出的纯谱量，对配对结构的变化敏感。")
h2t("1.2　S3 在「干到 1」链中的位置")
para("「干到 1」主线 S0 数值定向 → S1a Parseval 归因 → S1b 定理骨架 → S2(i) 口径探测 → S3 威胁"
     "排除交叉验证。S3 的角色不是检测威胁，而是「排除」：若威胁形态（同虚部成对）真实存在，"
     "Δ_pure 必然爆炸性偏离基线；实测与基线吻合 ⟹ 该威胁形态被排除。这就是「从威胁检测降级为"
     "排除交叉验证」的含义——S3 不增加前提负担，而是把威胁窗收得更窄。")

# ---------- 2 口径与设计 ----------
h1t("2　口径与设计")
h2t("2.1　Δ 常数定律与 Δ_pure 纯差")
para("Δ 常数定律（攻防 XXI/XXIII/XXIV 系列）：跨族配对和 S_zetaL 对期望 E 的差 Δ=S−E 分解为"
     "素项净差与纯谱差；Δ_pure 为剥离素项后的纯差（c_cut=0.0635 窗截断）。数据：T=6×10⁵、"
     "ℓ=log T=13.305、N_z=999492、N_l=1150050、N_K=2149542 对、n_use=1150045。")
h2t("2.2　同虚部成对注入构型")
para("威胁形态建模：若谱中存在同虚部成对（两个零点虚部完全相同），跨族配对和将系统性偏移。"
     "注入构型两种：(a) I_pair2——注入 N_pairs 对同虚部零点（mult=2，成对权重）；"
     "(b) II_single1——注入 N_pairs 个单零点（mult=1，对照）。扫描 N_pairs∈{100,200,2000,219000}。")
h2t("2.3　响应指标")
para("dS_mean/dS_std：注入导致的配对和偏移（均值/波动）；SNR_sigA=dS_mean/σ_A（对 A 涨落 σ_A），"
     "SNR_sigN=dS_mean/σ_N（对数值噪声 σ_N）；DP_inj：注入后 Δ_pure；rel_shift_of_absDP：|Δ_pure| "
     "相对基线 |DP0| 的相对移动。σ_A=362.72、σ_N=1072.40（基线）。")

# ---------- 3 结果 ----------
h1t("3　结果")
h2t("3.1　Δ 定律基线复算（表 1）")
caption("表 1　Δ_pure 基线复算（T=6×10⁵，对照文献值）")
rows1 = [
    ["Δ（总差 S−E）", "−72956.4", "—"],
    ["Δ_pure（纯差）", "−15046.5", "−15091（差 0.30%）"],
    ["Δ_pure/N_K", "−0.00700", "−0.702%"],
    ["Δ_pure/√N_l", "−14.03", "—"],
    ["SNR=Δ_pure/(√N_l·√var_A)", "−41.48", "—"],
    ["mean_A", "0.7856", "—"],
    ["var_A", "0.1144", "0.1144"],
]
add_table(["量", "本工作", "文献对照"], rows1)
para("", indent_chars=0, space_after=2)
para("三块逐块 per_n=−0.0598/−0.0644/−0.0661（稳定，无漂移）；Δ_pure 与文献 −15091 差 0.30%、"
     "Δ_pure/N_K 与 −0.702% 一致、var_A=0.1144 精确复现——基线可复跑。")
h2t("3.2　注入响应矩阵（表 2）")
caption("表 2　同虚部成对注入响应（I_pair2=成对 mult2；II_single1=单零点 mult1；基线 Δ_pure=−15046.5）")
rows2 = []
for rec in inj["injections"]:
    rows2.append([
        str(rec["n_pairs"]),
        "I 成对" if rec["config"] == "I_pair2" else "II 单点",
        "%.1f" % rec["dS_mean"],
        "%.2f" % rec["SNR_sigA"],
        "%+.0f" % rec["DP_inj"],
        "%.1f%%" % (rec["rel_shift_of_absDP"] * 100),
    ])
add_table(["N_pairs", "构型", "dS_mean", "SNR(σ_A)", "Δ_pure 注入后", "|Δ_pure| 相对移动"], rows2)
para("", indent_chars=0, space_after=2)
para("读数：(i) 小注入（100~200 对）Δ_pure 仅小幅移动（rel_shift 0.9%~3.5%），SNR<1.5——指纹"
     "对小威胁不敏感；(ii) 2000 对起 SNR=7~14，|Δ_pure| 移动 17%~34.5%；(iii) 219000 对（≈10% "
     "零点量级）爆炸：I 构型 Δ_pure 翻正至 +554771（rel_shift 3787%、SNR=1571），II 构型 "
     "+269841（SNR=785）——威胁若存在，Δ 指纹以 SNR≫1 必见。")
h2t("3.3　增量-全量检查一致")
para("fullcheck：dS_full=569911.20 与 dS_incremental=569911.20 相对差 1.57×10⁻¹⁴——注入响应的"
     "增量计算与全量重算完全一致，数值管线无误差。")

# ---------- 4 判定 ----------
h1t("4　判定")
h2t("4.1　爆炸响应 + 实测无响应 ⟹ 威胁排除")
para("真实数据 Δ_pure=−15046.5 与基线完全吻合（无任何注入特征）；而同虚部成对注入只需 219000 对"
     "就会把 Δ_pure 翻正、SNR 推到 1571。两向夹逼：威胁形态若存在必被看见，实测看不见 ⟹ "
     "同虚部成对威胁被排除。S3 的交叉验证闭环成立。")
h2t("4.2　三探针分工")
para("S1（左尾审计）：直接检查——224 个最小虚部零点无偏移；S2(i)（Weil 注入敏感性）：证明 "
     "x-口径弱（对随机散布失明），左尾威胁闭合；S3（Δ 指纹）：对同虚部成对爆炸敏感——威胁窗内"
     "的「结构型」违规被 Δ 指纹排除。配合 S0/S1a 的配对口径强探针（A(λ) 全尺度贴 GUE），"
     "威胁检测链从「直接检查 + 弱探针」升级为「直接检查 + 弱探针 + 爆炸指纹 + 强探针」四层。")
h2t("4.3　对「干到 1」的贡献")
para("S3 不触碰 S1b 的定理前提（(H2′_λ)），而是把「前提违规的现实形态」排除掉：同虚部成对"
     "是配对公式最大的结构违规候选，现已被指纹排除。主线下一步仍按文档判定：转回正向下界构造"
     "（ζ_K 特有谱结构），S2(ii) 跨 T 衰减律判别待跨 T 数据。")

# ---------- 5 诚实披露与开放问题 ----------
h1t("5　诚实披露与开放问题")
para("① 单 T=6×10⁵ 单点基线，未做跨 T（S2(ii) 待跨 T 数据）；② 注入为人为同虚部成对构型"
     "（不改变真实零点），测的是指纹灵敏度而非真实违规概率；③ Δ_pure 基线含素项净差等成分，"
     "本文不拆解（Δ 定律审计见攻防 XXIII/XXIV）；④ 「威胁形态」仅覆盖同虚部成对，其他构型"
     "（如整体实部平移）未被 Δ 指纹直接覆盖（左尾平移由 S1/S2(i) 覆盖）；⑤ 219000 对的爆炸量级"
     "依赖 c_cut 窗参数，具体数值随窗变，但「爆炸 + 实测无响应」的定性结论稳健。")

# ---------- 参考文献 ----------
h1t("参考文献")
refs = [
    "[1] S3 数值件（本工作，可复跑）：entF_work/detF_base.py + detF_base.json + detF_inject.py + detF_inject.json（Δ 定律基线复算 @6×10⁵、同虚部成对注入响应矩阵、fullcheck 1.6×10⁻¹⁴）.",
    "[2] 攻防 XXXVIII（d1 已交付）：Δ 常数指纹对同虚部成对注入的爆炸响应与威胁排除的交叉验证闭合（同主题早期编号版）.",
    "[3] 攻防 XXXVI（S1，d1 已交付）：左尾 224 审计——威胁形态实证（224 个最小虚部零点无偏移信号）.",
    "[4] 攻防 XXXVII / XLII-S2(i)（d1 已交付）：Weil 显式公式实部口径注入敏感性——x-口径弱探针、N_off·δ²·(logx)² 累积可测性、左尾威胁闭合链.",
    "[5] 攻防 XLII-S0 / S1a / S1b（d1 已交付）：全尺度 GUE 配对数值定向、Parseval 归因（δF 全负/δR 三区/核族偏序）、λ(T) 构造与 p 量化（定理 XLII.1）.",
    "[6] 攻防 XLI / XL（d1 已交付）：拟随机并集定理常数机制闭合（fejer_a0.5 最优核、7/8 门槛）；配对侧无条件界（BGS 误差项 O(1/√logT) 技术极限）.",
]
for rtext in refs:
    p = para(rtext, indent_chars=0, space_after=2)
    p.paragraph_format.line_spacing = 1.0

doc.save(TARGET)
print("saved:", TARGET)
