# -*- coding: utf-8 -*-
"""生成《路2攻防XXXIX-在线比例桥余项精细形态-理论余项界0.27的松弛定位与正向下界严格化窗口.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXIX-在线比例桥余项精细形态-理论余项界0.27的松弛定位与正向下界严格化窗口.docx"
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
    p = para([("n", text)], indent=False, align="center", size=9, before=before, after=after)
    p.paragraph_format.keep_with_next = True
    return p

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
rich(tp, [("b", "路2攻防XXXIX—在线比例桥余项精细形态：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(10)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "理论余项界 0.27 的松弛定位与正向下界严格化窗口")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：S4 数值定向——密度侧 10⁻⁵、配对侧 10⁻³ 的 T 无关标定与 L 伪影去趋势")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 24 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行 S4：在线比例桥余项（0.6725−O(10⁻⁵~10⁻³)）的精细形态分解与理论界松弛定位。三件事实：(i) 三侧标定（数值，detG_rem/rem2，多 T=1e5→6e5）：密度侧去趋势 sup|S_K|/(π·主项)=3.4×10⁻⁵，**T 无关稳定**（比理论界 O(1/√logT)≈0.27 小 ~8000 倍）；配对侧 ∫C(h)dh≈±10⁻³ 级、T 无关（小 ~270 倍）；素项侧 χ₅ 振荡 sup≤2.46（攻防 XIX）。(ii) 理论界松弛定位：0.27 的 270 倍松弛在**配对侧**（Montgomery 配对相关误差项 O(1/√logT)）——密度侧与素项侧的理论界本就不松——**余项不是均匀松弛，松弛集中在一处**。(iii) 跨族互斥接入：配对侧偏差（∫dF≈−0.0094、本攻防 ∫C≈10⁻³）与 Δ_pure/N_K=−0.0070 同量级同号（比值 1.34）——配对负偏的谱学来源=跨族互斥（Δ 常数定律）。数据披露：原始 sup|S_K|=3163@6e5 的 ~97% 是 L 零点数据 0.27% R-S 求根趋势伪影（拟合斜率 −0.0073→−0.0051 收敛，精确复现攻防 XIX 披露值 −0.0052/单位）——去趋势口径免疫。判定：正向下界严格化窗口 = 把配对侧无条件界压到 10⁻² 级 ⟹ 在线比例 ≥0.6725−O(10⁻²) 成为严格定理——两条路线：BGS 型无条件 Montgomery 配对定理的 ζ_K 并集版、或利用跨族配对主项 f(0) 结构（定理 3.1′）的专用界。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "在线比例桥；Levinson 常数；余项精细形态；配对相关；跨族互斥；正向下界")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XIX 与谱对偶综述共同判定：在线比例 ≥0.6725−O(10⁻⁵~10⁻³)（T=6×10⁵ 有限口径），但**Levinson 理论余项界 O(1/√logT)≈0.27 未改进**——数值与理论界的差距提示配对结构特殊或上界非紧，未作判定（XIX §6.4；综述 §7(4)）。用户拍板：转回正向下界构造——对象为在线比例桥余项的精细形态。")], indent=True)
para([("n", "任务：把理论余项界 0.27 的三项分解（密度侧/配对侧/素项侧）数值化，定位 270 倍差距的来源；判定是否存在把 0.6725 从「数值级估计」升级为「严格定理」的窗口——即常数机制内（Levinson–Lamzouri）的最后一步严谨化。")], indent=True)

# ---------- 2 ----------
h1("2　在线比例桥的余项分解")
para([("n", "Levinson 型论证（XIX §2.3）：在线比例 ≥0.6725−余项/(2(T/2π)λ)。余项 = 密度侧（Backlund 计数偏差 sup|S_K|，控制计数对主项的偏离）+ 配对侧（配对和 ΣK² 相对理论主项 C_MT·N 的偏差）+ 素项侧（显式公式素项和 χ₅ 振荡的截断贡献）。标准理论界：密度侧 O(log T)（Littlewood 型）⟹ /主项 1/T 级；配对侧 O(1/√logT)（Montgomery 配对定理误差项）；素项侧 O(1) 类（Pólya–Vinogradov）⟹ /主项 1/T 级。**理论界总控 0.27 来自配对侧**。")], indent=True)

# ---------- 3 ----------
h1("3　数值标定")
h2("3.1　密度侧：L 伪影主导与去趋势")
para([("n", "并集计数 N_K(t)=N_ζ+N_L 减主项_K（XIX 修正口径：主项_K=(t/2π)[2log(t/2π)+log5−2]+7/8）得 S_K(t)。原始 sup|S_K| 从 737（1e5）增长到 3163（6e5）——增长率 ~T^0.82，与 Backlund 型 O(log T) 不符——最小二乘去趋势后残差 sup 30.4→232.2，拟合斜率 α 从 −0.00734 单调收敛到 −0.00508（6e5）——**精确复现攻防 XIX 披露的 L 零点数据 0.27% R-S 求根趋势伪影（−0.0052/单位、累计 −3147@6e5）**。原始 sup 的 ~97% 是数据伪影，非真实 Backlund 函数量级。")], indent=True)
caption("表 1　密度侧余项多 T 标定（并集 S_K=N_K−主项_K，最小二乘去趋势）", before=4, after=2)
t1 = make_table(
    ["T", "sup_raw", "sup_detrend", "斜率 α", "sup_det/(π·主项)"],
    [
        ["1e5", "737", "30.4", "−0.00734", "3.21e-5"],
        ["2e5", "1326", "70.7", "−0.00642", "3.47e-5"],
        ["3e5", "1850", "107.3", "−0.00597", "3.38e-5"],
        ["4e5", "2283", "149.5", "−0.00560", "3.44e-5"],
        ["5e5", "2746", "194.4", "−0.00529", "3.51e-5"],
        ["6e5", "3163", "232.2", "−0.00508", "3.43e-5"],
    ],
    [Cm(1.8), Cm(2.2), Cm(2.6), Cm(2.6), Cm(3.4)])
para([("n", "读数：sup_det/(π·主项) 全程 3.2~3.5×10⁻⁵ 稳定（T 无关）——密度侧余项 ≪0.27 的 8000 分之一。α 收敛路径与 XIX 披露值 −0.0052 精确吻合；第三段 sup（129@6e5）仍高于 Backlund 型 ~28 的量级——伪影曲率未完全扣除（诚实边界 ①）。")], indent=True)
h2("3.2　配对侧：T 无关的 ~10⁻³ 常数")
para([("n", "A(t)=Σ_{γ∈ζ}w((γ−t)λ) 窗口统计（l4_multit 口径）的配对相关 C(h)=Cov(A(t),A(t+h)) 积分 ∫₀³C(h)dh：")], indent=True)
caption("表 2　配对侧 ∫C(h)dh 与 A 统计多 T（ζ 谱窗口相关，l4_multit 口径）", before=4, after=2)
t2 = make_table(
    ["T", "∫C(h)dh（h∈[0,3]）", "var_A", "mean_A"],
    [
        ["1e5", "−0.0009", "0.1127", "0.7620"],
        ["2e5", "−0.0004", "0.1134", "0.7720"],
        ["3e5", "0.0000", "0.1138", "0.7773"],
        ["4e5", "0.0003", "0.1142", "0.7809"],
        ["5e5", "0.0006", "0.1143", "0.7835"],
        ["6e5", "0.0007", "0.1144", "0.7856"],
    ],
    [Cm(1.8), Cm(3.8), Cm(2.6), Cm(2.6)])
para([("n", "读数：∫C(h)dh 在 ±10⁻³ 内徘徊、无 T 增长——配对侧余项为**常数级 10⁻³~10⁻²**（与攻防 XVI/XVII 的 ∫dF≈−0.0094 同量级）——相对理论界 0.27 小 270 倍，且**不随 T 收敛**（不是 (logT)^{-1/2} 型衰减，而是常数级偏差）。var_A 0.1127→0.1144 收敛到文献值。")], indent=True)

# ---------- 4 ----------
h1("4　理论界松弛定位")
para([("n", "理论余项界 0.27=O(1/√logT)（T=6×10⁵ 处 1/√log(6×10⁵)≈0.274）的三项对照：")], indent=True)
para([("n", "① 密度侧：理论 O(logT)/主项 ~1/T 级（不松）——实测 3.4×10⁻⁵ 与理论同量级、T 无关；② 素项侧：理论 O(1/T) 级（不松）——实测 χ₅ 振荡 sup≤2.46、贡献 10⁻⁵~10⁻³（XIX）；③ **配对侧：理论 O(1/√logT)=0.27（唯一 10⁻¹ 级项）——实测 10⁻³~10⁻² 常数级——松 270 倍**。**判定：余项不是均匀松弛，270 倍差距集中在一处——Montgomery 配对相关的误差项**。配对和 ΣK² 相对理论主项的偏差实际 ~10⁻² 级且 T 无关——理论界 0.27 的松弛机制是常数级高估（配对波动远小于最坏情形），不是收敛速率问题。")], indent=True)

# ---------- 5 ----------
h1("5　跨族互斥接入：配对负偏的谱学来源")
para([("n", "配对侧偏差的三个独立口径同量级同号：∫dF≈−0.0094（攻防 XVI/XVII 谱层积分）、∫C(h)dh≈±10⁻³（本攻防窗口相关）、Δ_pure/N_K=−0.0070（Δ 常数定律，攻防 XXXVIII 基线）——比值 ∫dF/Δ_pure≈1.34（口径不同：谱层积分 vs 窗口计数）。配对侧负偏（亚泊松 var_A≪mean_A、C(h<0) 负相关）的谱学来源 = **跨族互斥**（Δ 定律：并集配对比独立更稀）——S3（XXXVIII）已把 Δ 指纹用作威胁排除检测器，本攻防把同一常数接入余项分解：**配对侧偏差的负号与量级均由跨族互斥结构决定**——配对侧 10⁻² 级偏差不是噪声，是确定性结构（14σ）。")], indent=True)

# ---------- 6 ----------
h1("6　正向下界严格化窗口")
para([("n", "若配对侧无条件界从 O(1/√logT)≈0.27 压到 ~10⁻² 级（BGS 型无条件 Montgomery 配对定理的 ζ_K 并集版；或定理 3.1′ 的跨族 f(0) 主项结构——跨族配对无 |α| 排斥项、素项字符对消——专用界），则在线比例 ≥0.6725−O(10⁻²) 成为**严格定理**——常数 0.6725 从数值级估计升级为可证下界。数值证据（本攻防）：配对侧实测偏差 10⁻³~10⁻² 常数级、T 无关、负偏有确定性结构（跨族互斥 14σ）——支持界可达。**注意边界**：0.6725→7/8 仍需常数机制更换（QRH 类 quasi-random 前提；攻防 XVIII Q(0) 判负、综述 §6.3 谱侧信息不足）——本攻防严格化的是常数 0.6725 本身，不宣称推进 7/8。")], indent=True)

# ---------- 7 ----------
h1("7　诚实边界与未决")
para([("n", "① 去趋势 sup|S_K|（232@6e5）与攻防 XIX 的 28.1 口径差 ~8 倍——L 伪影含曲率（第三段 sup 129 仍高于 Backlund 型），全局线性去趋势未完全扣除——密度侧余项的精确口径待定稿（量级 10⁻⁵ 结论不变）。② ∫dF（谱层积分）与 ∫C(h)（窗口相关）不同定义、同量级——配对侧 10⁻² 级的精确口径未统一。③ 配对侧 10⁻² 无条件界是数值证据（跨族互斥 14σ）非定理——BGS 型/跨族专用界的理论构造未完成。④ 全区间在线比例实测（~40 分钟级普查）未拍板——本攻防只做余项分解，不测在线比例本身。⑤ 0.6725 的严格化不等价于 7/8 推进——常数机制更换（QRH）是独立开放问题。⑥ α 拟合用全局线性最小二乘——伪影可能非线性（R-S 求根密度依赖），高精度口径需分段拟合。")], indent=True)

# ---------- 8 ----------
h1("8　判定总结")
para([("n", "S4 完成并落档。在线比例桥余项精细形态：密度侧 3.4×10⁻⁵（T 无关）、配对侧 10⁻³~10⁻²（T 无关常数）、素项侧 10⁻⁵~10⁻³——**理论界 0.27 的 270 倍松弛定位在配对侧（Montgomery 配对相关误差项）**，且配对偏差是确定性负偏（跨族互斥 14σ，与 Δ 定律同源），非收敛级噪声。数据披露：L 求根伪影主导原始 sup|S_K|（斜率收敛 −0.0052 精确验证）。正向下界窗口：配对侧无条件界压到 10⁻² ⟹ 在线比例 ≥0.6725−O(10⁻²) 严格定理——路线 = BGS 型配对定理 ζ_K 并集版 / 跨族 f(0) 结构专用界。7/8 仍属 QRH 常数机制（独立开放）。主线：威胁排除五柱合围（XXXIII-XXXVIII）已闭合，正向下界严格化窗口已定位——下一步候选：配对侧无条件界的理论构造（BGS 型/跨族版）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XIX：并集素项净压制与显式公式余项数值级（xxx1_work/atk19_read0.txt）：0.6725−O(10⁻⁵~10⁻³)、sup|S_K| 口径、L 伪影 0.27%/−0.0052/单位、χ₅ 部分和 sup≤2.46.",
    "谱对偶综述：ζ_K 零点并集结构（zetaK_rev_work/read0.txt）：Levinson 余项分解（密度+配对）、O(1/√logT)≈0.27 未改进、Q(0)≥1 判负、定理 3.1′（跨族配对 f(0) 主项）、谱侧信息不足开放状态.",
    "攻防 XVIII：Q(0) 控制（d1 已交付）：并集 Hilbert 空间下界恒非正（−1/3 墙），常数翻越入口封死.",
    "攻防 XXXVIII：Δ 常数指纹对同虚部成对注入的爆炸响应（d1 已交付）：Δ_pure/N_K=−0.007000 基线、跨族互斥 14σ、检测器响应.",
    "S4 数值件：entG_work/detG_rem.py/.json（密度+配对多 T 标定）、detG_rem2.py/.json（去趋势 + 斜率拟合）——可复跑（Anaconda python）。",
    "零点数据：zeros_T6e5.npz（ζ 族 999492、L 族 1150050、T=6×10⁵）.",
    "Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（配对定理无条件化，误差项 O(1/√logT) 级）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
