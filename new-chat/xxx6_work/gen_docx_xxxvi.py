# -*- coding: utf-8 -*-
"""生成《路2攻防XXXVI-左尾224审计与威胁形态实证-零点实部实测与盲区威胁收窄判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVI-左尾224审计与威胁形态实证-零点实部实测与盲区威胁收窄判定.docx"
SONG, HEI, KAI, TNR = "宋体", "黑体", "楷体", "Times New Roman"

doc = Document()
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21), Cm(29.7)
sec.top_margin = sec.bottom_margin = sec.left_margin = sec.right_margin = Cm(2.5)

normal = doc.styles["Normal"]
normal.font.name = TNR
normal.font.size = Pt(10.5)
normal.element.rPr.rFonts.set(qn("w:eastAsia"), SONG)
npf = normal.paragraph_format
npf.space_before = Pt(0); npf.space_after = Pt(0); npf.line_spacing = 1.5

def set_fonts(run, eastasia=SONG, latin=TNR, size=10.5, bold=False, italic=False,
              sub=False, sup=False, color=None):
    run.font.name = latin
    run._element.rPr.rFonts.set(qn("w:eastAsia"), eastasia)
    run.font.size = Pt(size)
    run.font.bold = bold
    run.font.italic = italic
    if sub: run.font.subscript = True
    if sup: run.font.superscript = True
    if color: run.font.color.rgb = RGBColor(*color)

def rich(par, segs, size=10.5, eastasia=SONG):
    for kind, text in segs:
        r = par.add_run(text)
        if kind == "n": set_fonts(r, eastasia=eastasia, size=size)
        elif kind == "b": set_fonts(r, eastasia=HEI, size=size, bold=True)
        elif kind == "i": set_fonts(r, eastasia=eastasia, size=size, italic=True)
        elif kind == "sup": set_fonts(r, eastasia=eastasia, size=size, sup=True)
        elif kind == "sub": set_fonts(r, eastasia=eastasia, size=size, sub=True)
    return par

def para(segs, indent=True, align=None, size=10.5, before=0, after=0, line=1.5, eastasia=SONG):
    p = doc.add_paragraph()
    pf = p.paragraph_format
    if indent: pf.first_line_indent = Pt(size * 2)
    if align == "center": pf.alignment = WD_ALIGN_PARAGRAPH.CENTER
    elif align == "right": pf.alignment = WD_ALIGN_PARAGRAPH.RIGHT
    pf.space_before = Pt(before); pf.space_after = Pt(after)
    pf.line_spacing = line
    rich(p, segs, size=size, eastasia=eastasia)
    return p

def formula(segs, number=None, size=10.5):
    p = doc.add_paragraph()
    pf = p.paragraph_format
    pf.alignment = WD_ALIGN_PARAGRAPH.CENTER
    pf.space_before = Pt(4); pf.space_after = Pt(4)
    pf.line_spacing = 1.5
    if number:
        pf.tab_stops.add_tab_stop(Cm(15.9), WD_TAB_ALIGNMENT.RIGHT)
        rich(p, segs, size=size)
        rich(p, [("n", "\t（" + number + "）")], size=size)
    else:
        rich(p, segs, size=size)
    return p

def h1(text):
    p = doc.add_heading(level=1)
    pf = p.paragraph_format
    pf.space_before = Pt(12); pf.space_after = Pt(6)
    pf.line_spacing = 1.5
    r = p.add_run(text)
    set_fonts(r, eastasia=HEI, latin=TNR, size=12, bold=True, color=(0, 0, 0))
    return p

def h2(text):
    p = doc.add_heading(level=2)
    pf = p.paragraph_format
    pf.space_before = Pt(6); pf.space_after = Pt(3)
    pf.line_spacing = 1.5
    r = p.add_run(text)
    set_fonts(r, eastasia=HEI, latin=TNR, size=10.5, bold=True, color=(0, 0, 0))
    return p

def make_table(headers, rows, widths, first_center=True):
    tbl = doc.add_table(rows=1 + len(rows), cols=len(headers))
    tbl.style = "Table Grid"
    tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
    for j, htxt in enumerate(headers):
        c = tbl.rows[0].cells[j]
        c.width = widths[j]
        tcPr = c._tc.get_or_add_tcPr()
        shd = OxmlElement("w:shd")
        shd.set(qn("w:val"), "clear"); shd.set(qn("w:color"), "auto"); shd.set(qn("w:fill"), "D9D9D9")
        tcPr.append(shd)
        p = c.paragraphs[0]
        p.paragraph_format.first_line_indent = Pt(0)
        p.paragraph_format.space_before = Pt(1); p.paragraph_format.space_after = Pt(1)
        p.paragraph_format.line_spacing = 1.15
        p.alignment = WD_ALIGN_PARAGRAPH.CENTER
        r = p.add_run(htxt)
        set_fonts(r, eastasia=HEI, size=9, bold=True)
        c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
    for i, row in enumerate(rows, 1):
        for j, txt in enumerate(row):
            c = tbl.rows[i].cells[j]
            c.width = widths[j]
            p = c.paragraphs[0]
            p.paragraph_format.first_line_indent = Pt(0)
            p.paragraph_format.space_before = Pt(1); p.paragraph_format.space_after = Pt(1)
            p.paragraph_format.line_spacing = 1.15
            p.alignment = WD_ALIGN_PARAGRAPH.CENTER if (first_center and j == 0) else WD_ALIGN_PARAGRAPH.LEFT
            r = p.add_run(txt)
            set_fonts(r, eastasia=SONG, size=9)
            c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
    for row in tbl.rows:
        trPr = row._tr.get_or_add_trPr()
        cant = OxmlElement("w:cantSplit")
        trPr.append(cant)
    trPr0 = tbl.rows[0]._tr.get_or_add_trPr()
    th = OxmlElement("w:tblHeader")
    trPr0.append(th)
    return tbl

def caption(text, before=2, after=6):
    para([("n", text)], indent=False, align="center", size=9, before=before, after=after)

footer_p = sec.footer.paragraphs[0]
footer_p.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = footer_p.add_run()
fld1 = OxmlElement("w:fldChar"); fld1.set(qn("w:fldCharType"), "begin")
instr = OxmlElement("w:instrText"); instr.set(qn("xml:space"), "preserve"); instr.text = "PAGE"
fld2 = OxmlElement("w:fldChar"); fld2.set(qn("w:fldCharType"), "end")
run._r.append(fld1); run._r.append(instr); run._r.append(fld2)
set_fonts(run, size=9)

# ---------- 标题区 ----------
tp = doc.add_paragraph()
tp.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp.paragraph_format.space_after = Pt(0)
tp.paragraph_format.line_spacing = 1.5
rich(tp, [("b", "路2攻防XXXVI—左尾224审计与威胁形态实证：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(10)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "零点实部实测、假根判定与盲区威胁的实证收窄")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：B4 低峰高零点的 mpmath 局部实部测量、两族求根质量对照与威胁带压缩")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 23 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行新攻坚第一步：把攻防 XXXV 遗留的盲区 δ<0.05（需超密度假设级界）转化为 ζ_K 特有谱结构的实证测量。对象：B4 全区间峰高实测的左尾——ĥ<3 共 224 个最低峰高零点（ζ 216 / L 8），即「离线零点」的候选集。快速定向（entB_lt_fast.json）确认：ζ 族求根几乎完美（全长计数偏差仅 −15，无漏根趋势），L 族漏根确认（−3146.7，与攻防 XIX 的 0.27% 一致），跨族极近对 386 ≈ 独立零点重合预期 ~380（并集口径自洽）——方向反转（ζ216 vs L8）排除「L 型漏根」解释。完整审计（entB_lt_full.py，在线判定优先）：峰高重跑口径与 B4 全等（并集 mean=14.7475/std=2.1298 复核命中）→ 左尾唯一 224 条 → mpmath 局部实部测量（|ζ_K(0.5+iγ)|<1e-2 判在线；非在线点 σ∈[0.30,0.70] 粗扫 0.02+精化 0.002；L(s,χ₅)=5^{−s}[ζ_H(s,1/5)−ζ_H(s,2/5)−ζ_H(s,3/5)+ζ_H(s,4/5)]）。判定：**在线真零点 223、假根 1（L 族 γ=500327.77，σ≈0.528 处最小模 0.183，无零点）、离线（δ>0.01）0 个**；在线真零点的 |ζ_K(0.5+iγ)| 中位 1.15e-5（求根精度 ~1e-5），4 个边界样本（~1e-3–5e-3）。结论 1：左尾低峰高全部归因于素项背景负涨落（重尾），非离线零点、非求根伪影——B4 峰高基线可信度审计通过。结论 2：假根仅 1 个——ζ 族求根质量确认；L 族 1 个孤立假根与 0.27% 漏根为独立缺陷形态。结论 3（对主线）：峰高可分辨范围内不存在 δ>0.01 的离线零点——威胁（若存在）必须挤在 δ≤0.01 且 >21.9 万——相对攻防 XXXV 的 δ<0.05 收窄 5 倍，算术上更不自然。证据结构升级：无条件段 + 数值闭合段 + 盲区（收窄为 δ≤0.01 超浅带）+ 实证剖面。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "左尾审计；零点实部实测；假根判定；背景负涨落；威胁形态实证；盲区收窄")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXXV 文献核实判定：盲区 δ<0.05 的无条件闭合需要超密度假设级界（σ=0.55 处指数 κ≤0.8721），文献中不存在——通用零密度路径闭合；唯一开放方向是 ζ_K 特有谱结构（在线比例桥/显式公式余项精细形态）构造专用论证。本攻防为新攻坚第一步：威胁形态的实证测量。")], indent=True)
para([("n", "威胁形态是「极浅且极多」：δ<0.05、>21.9 万离线零点。若这种构型真实存在，其零点应在零点数据中留下可测的实部结构。B4 全区间峰高实测的左尾——ĥ<3 共 224 个最低峰高零点（ζ 216 / L 8）——正是「离线零点」候选集：峰高口径下最可疑的样本。B4 未存左尾位置明细（复算需重跑峰高），本攻防重跑并逐一做局部实部测量。")], indent=True)

# ---------- 2 ----------
h1("2　快速定向：两族求根质量对照")
para([("n", "先做秒级定向（entB_lt_fast.py，可复跑）：测 ζ 族与 L 族的求根结构签名——间距分布（漏根⟹大间距异常）、计数剖面趋势（攻防 XIX 的 −0.0052/单位）、极近对（假根/重复嫌疑）、跨族重合。")], indent=True)
caption("表 1　ζ 族与 L 族求根质量对照（T=6×10⁵，zeros_T6e5.npz）", before=4, after=2)
t1 = make_table(
    ["指标", "ζ 族（n=999492）", "L 族（n=1150050）", "解读"],
    [
        ["计数偏差（10 段合计）", "−15.0（每段 −1.5）", "−3146.7（每段 −314.7）", "ζ 几乎完美；L 漏根确认（XIX 一致）"],
        ["间距中位 d_p50", "0.5759", "0.5039", "两族密度口径正常"],
        ["间距 1% 分位 d_p1", "0.1328", "0.1176", "无非正常近对"],
        ["极近对（<1e-3）", "0", "0", "无重复根/假根成对"],
        ["大间距（>5× 中位）", "29", "18", "漏根候选位置极少"],
        ["跨族极近对（<1e-4）", "并集 386 个", "—", "≈ 独立重合预期 380，非伪影"],
    ],
    [Cm(3.6), Cm(3.2), Cm(3.2), Cm(5.6)])
para([("n", "读数：ζ 族求根质量极好（全长 −15 个，无趋势）——ζ 216 个左尾不是「L 型漏根」来源；L 族漏根 −3146.7 与攻防 XIX 的 0.27%/−3147 完全一致（漏根是「缺失」，不产生低峰高项）；跨族极近对 386 个与独立零点重合的泊松预期 N_ζ·N_L·(2×10⁻⁴/T)=999492×1150050×3.33×10⁻¹⁰≈380 吻合——并集口径自洽。方向反转（ζ216 vs L8）指向两个假说：H1（ζ 族求根含假根/低质量根，计数完美不排除真假互换）；H2（素项背景大负涨落重尾，族间采样差异）。须局部实部测量定论。")], indent=True)

# ---------- 3 ----------
h1("3　峰高重跑与左尾定位")
para([("n", "重跑 B4 全区间峰高（entB_lt_full.py Part1，口径与 entB_full.py 逐行一致：EPS=0.1、DT_BG=0.2、D_CUT=5、掩码 |d|>1e-6、并集 2 145 942 零点），复核命中：并集 mean=14.7475/std=2.1298、ζ 14.7787/2.1762、L 14.7204/2.0883——与 B4 全等，口径可信。结果落盘 h_full.npz（可复用）。")], indent=True)
para([("n", "左尾定位：ĥ<3 共 224 个（ζ 216 / L 8）、ĥ<1 共 46 个（ζ 44 / L 2）；明细脚本输出 270 条（含 46 条 lt1⊂lt3 重复，去重后唯一 224）。左尾最近邻间距 min 0.120 / med 0.522 / max 2.127——无异常孤对或极近对。")], indent=True)

# ---------- 4 ----------
h1("4　局部实部测量")
h2("4.1　方法")
para([("n", "对左尾 224 个零点逐一测量 ζ_K 在实部方向的零点结构（entB_lt_full.py Part3，mpmath dps=8）。在线判定优先：|ζ_K(0.5+iγ)|<1e-2 判为在线真零点（真零点处模≈0；判据精确保证 δ>0.01 的离线不被误判为在线）；非在线点做 σ∈[0.30,0.70] 粗扫（步长 0.02）+ 最小邻域精化（步长 0.002）。ζ_K(s)=ζ(s)·L(s,χ₅)，L 用 Hurwitz zeta 精确表示：")], indent=True)
formula([("n", "L(s,χ₅) = 5^{−s}[ζ_H(s,1/5) − ζ_H(s,2/5) − ζ_H(s,3/5) + ζ_H(s,4/5)]，　ζ_H 为 Hurwitz zeta。")], "1")
para([("n", "判据：有零点 ⟺ 最小模 m_min<1e-2 且 m_min<0.5·背景幅值（背景幅值取 σ=0.5 处模 m_half 的保守界）；离线深度 δ=0.5−σ_min（仅当有零点且 σ_min<0.5）；δ>0.01 的离线再做对称伙伴检查（σ=1−σ_min+iγ 处 |ζ_K|，函数方程配对）。")], indent=True)
h2("4.2　判定统计")
caption("表 2　左尾 224 的局部实部测量判定（唯一口径）", before=4, after=2)
t2 = make_table(
    ["判定", "数量", "说明"],
    [
        ["在线真零点", "223", "|ζ_K(0.5+iγ)|<1e-2（含 4 个边界样本 ~1e-3–5e-3）"],
        ["假根（无零点）", "1", "L 族 γ=500327.77：σ≈0.528 处最小模 0.183，背景 0.213"],
        ["离线（δ>0.01）", "0", "非在线分支 σ 扫描未发现任何 δ>0.002 的离线零点"],
        ["合计", "224", "ζ 216 / L 8"],
    ],
    [Cm(3.2), Cm(1.8), Cm(9.4)])
para([("n", "唯一假根：γ=500327.7696（L 族）、峰高 2.811、最近邻 0.163——σ 扫描全带最小模 0.183（无零点），判定为 R-S 求根的孤立假根；与 L 族 0.27% 漏根是独立的求根缺陷形态。假根占比 1/224≈4.5×10⁻³（左尾）、4.7×10⁻⁷（全数据）——不影响任何统计口径。")], indent=True)
caption("表 3　在线真零点 223 个的 |ζ_K(0.5+iγ)| 分布（求根精度指示）", before=4, after=2)
t3 = make_table(
    ["统计量", "数值", "说明"],
    [
        ["最小值", "7.4×10⁻¹⁰", "零点位置精度 ~1e-9 级"],
        ["中位数", "1.15×10⁻⁵", "整体求根精度 ~1e-5 级"],
        ["最大值", "5.4×10⁻³", "γ=302700.2（L 族），边界样本"],
        [">1e-3 计数", "4", "边界样本（ζ 2 / L 2），判据保守界"],
        [">1e-4 计数", "31", "精度稍差样本，仍远小于判据 1e-2"],
    ],
    [Cm(3.0), Cm(3.6), Cm(7.8)])
para([("n", "边界样本（m_half∈[1e-3,1e-2] 共 4 个）即便按最坏解读为浅离线，其深度受 |ζ_K′(ρ)|·δ≲m_half 约束——ζ_K 在零点处的典型导数模为 O(1) 级，对应 δ≲10⁻³ 量级；无论如何远小于 0.05。判据本身精确保证：**δ>0.01 的离线零点在左尾 224 中为 0 个**。")], indent=True)

# ---------- 5 ----------
h1("5　判定：假根否定、背景重尾确认、威胁实证收窄")
para([("n", "（i）H1（ζ 族假根）否定：假根仅 1 个且落在 L 族——ζ 族求根质量经实部测量确认无假根问题。ζ 216 个左尾不是伪影。")], indent=True)
para([("n", "（ii）H2（背景负涨落）确认：左尾 223 个在线真零点的低峰高全部归因于素项背景（ζ_K 显式公式素数项和 Σa_p e^{−it log p} 的正则化对数导数）在零点位置的深负涨落；ζ216 vs L8 的族间差来自背景在 ζ 族零点位置采样到更深负尾（L 族零点密度与位置分布不同，主项含 log 5）。背景重尾形态：46 个 ĥ<1 超高斯预期约 3 个量级（攻防 XXXIII 已披露）——左尾审计给出微观确认：这些低峰高点都是真零点，峰高统计正确，只是背景负尾深。")], indent=True)
para([("n", "（iii）威胁实证收窄：峰高可分辨范围内（左尾=最低峰高端）不存在 δ>0.01 的离线零点。若威胁（>21.9 万离线）存在，其零点必须挤在 δ≤0.01 的超浅带内且峰高不可分辨——相对攻防 XXXV 的 δ<0.05 收窄 5 倍，算术上更不自然：>21.9 万零点在实部偏差 ≤0.01 处堆积、每零点配对称伙伴、且完全不改变任何可测结构。")], indent=True)

# ---------- 6 ----------
h1("6　对主线的意义")
para([("n", "（i）B4 基线加固：左尾 224 个最低峰高处无离线污染——峰高统计的 SE（0.00145）可信，反推上界（δ≥0.05 的 ≤2139@2σ / 3208@3σ）成立。基线 mean 14.75 与理论在线基线 ~12.4 的偏置 ~2.35 归因于背景素项和的正均值（含 χ₅ 字符调制），非离线零点——模型误差 ~2 的检测限限制不变。")], indent=True)
para([("n", "（ii）证据结构升级：θ_K≥7/8 等价式的证据 = 无条件段（δ≥0.0902）+ 数值闭合段（δ∈[0.05,0.0902]）+ 盲区（δ≤0.01 超浅带，含实证剖面——本攻防）+ 理论门槛（超密度假设 κ≤0.8721@σ=0.55）。盲区威胁与实测剖面相容（0 个 δ>0.01 样本不排除理论构型），但其形态约束从「极浅 δ<0.05」压缩到「超浅 δ≤0.01」，且与密度假设兼容的余量（允许 31.7 万）与 21.9 万目标带的差距不变。")], indent=True)
para([("n", "（iii）后续攻击面（S2-S4）：Weil 显式公式实部口径注入敏感性（离线零点在 Weil 公式中成对贡献 √x·cos(t logx)·(1+δ²log²x/2)——N_off·δ²·(logx)² 累积可测性）；Δ 常数定律对离线注入的响应（整体谱指纹检测器候选）；在线比例桥 0.6725 的精化。本攻防为这些方向提供「数据无深离线」的实证基线。")], indent=True)

# ---------- 7 ----------
h1("7　诚实边界与未决")
para([("n", "① 在线判据 1e-2 允许 δ≤~0.01 的极浅离线不可分辨（与在线真零点合并）——审计精确保证的是「δ>0.01 的离线为 0」；δ∈(0,0.01] 与在线不可严格区分。② σ 精化网格 0.002——δ 分辨率 ~0.002，δ<0.002 的超浅离线在扫描分支同样不可分辨（并入判据边界）。③ 审计范围 = 峰高<3 的左尾 224：它们是峰高口径下最可疑样本；若离线零点不压低峰高（峰叠加只看虚部间距），左尾不是完备候选集——但「最低峰高处无深离线」本身加固基线；全零点实部普查（~40 分钟级，214 万点逐点测量）未做，列为可选。④ 唯一假根 γ=500327.77 未重新求根确认（最小模 0.183 对「无零点」已足够）。⑤ 快速定向与完整审计的 ζ/L 族间背景负尾差异（27:1）的机理（背景统计的族间采样）未定量——需背景分布分族刻画，列为后续。")], indent=True)

# ---------- 8 ----------
h1("8　判定总结")
para([("n", "左尾 224 审计完成并落档：峰高重跑与 B4 全等（mean=14.7475/std=2.1298）；mpmath 局部实部测量判定——在线真零点 223、假根 1（L 族 γ=500327.77）、离线（δ>0.01）0 个。快速定向排除 L 型漏根解释（ζ 族计数 −15、L −3146.7、跨族重合 386≈380）。判定：H1（ζ 族假根）否定——假根仅 1 个；H2（背景负涨落重尾）确认——左尾低峰高全为真在线零点的背景负采样；威胁实证收窄——峰高可分辨范围内无 δ>0.01 离线，威胁带从 δ<0.05 压缩到 δ≤0.01（收窄 5 倍）。B4 基线可信度审计通过（最低峰高处无离线污染）。证据结构升级为无条件段 + 数值闭合段 + 盲区（δ≤0.01 超浅带）+ 实证剖面。主线下一步：S2（Weil 显式公式实部口径注入敏感性）/ S3（Δ 常数指纹）——在「数据无深离线」的实证基线上构造超密度假设级的 ζ_K 专用论证。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XIX：《在线比例桥》数值剖面（xxx1_work/atk19_read0.txt；在线比例 0.6725−O(10⁻⁵~10⁻³)；L 族 0.27% R-S 漏根 −0.0052/单位）.",
    "攻防 XXXIII：路2攻防XXXIII-入口B密度剖面与威胁窗闭合-全区间峰高实测与盲区收缩判定.docx（B4 峰高口径 EPS=0.1/D_CUT=5、左尾 224、反推 δ≥0.05 离线 ≤2139@2σ；峰高统计 SE=0.00145）.",
    "攻防 XXXIV：路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx（配对和对 σ 二阶盲；盲区数值攻击路线关闭）.",
    "攻防 XXXV：路2攻防XXXV-盲区理论门槛文献核实-零密度路径闭合与超密度假设判定.docx（盲区 δ<0.05 需超密度假设界 κ≤0.8721@σ=0.55；零密度路径闭合）.",
    "数值数据：entB_work/entB_lt_fast.py/.json（快速定向）；entB_work/entB_lt_full.py/.json、h_full.npz（峰高重跑+局部实部测量，可复跑）；zeros_T6e5.npz.",
    "mpmath 库（Hurwitz zeta ζ(s,a) 任意精度求值；L(s,χ₅)=5^{−s}Σχ₅(a)ζ_H(s,a/5)，χ₅(1,2,3,4)=(1,−1,−1,1)）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
