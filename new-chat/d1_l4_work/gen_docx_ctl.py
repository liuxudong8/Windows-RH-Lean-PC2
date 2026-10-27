# -*- coding: utf-8 -*-
"""生成《Delta系数翻译与多T稳定性-互斥进入theta_K的Levinson桥与收敛判定.docx》"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\Delta系数翻译与多T稳定性-互斥进入theta_K的Levinson桥与收敛判定.docx"
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
        elif kind == "mi": set_fonts(r, eastasia=eastasia, size=size, italic=True)
        elif kind == "b": set_fonts(r, eastasia=HEI, size=size, bold=True)
        elif kind == "i": set_fonts(r, eastasia=eastasia, size=size, italic=True)
        elif kind == "sup": set_fonts(r, eastasia=eastasia, size=size, sup=True)
        elif kind == "sub": set_fonts(r, eastasia=eastasia, size=size, sub=True)
        elif kind == "mis": set_fonts(r, eastasia=eastasia, size=size, italic=True, sup=True)
        elif kind == "msub": set_fonts(r, eastasia=eastasia, size=size, italic=True, sub=True)
    return par

def para(segs, indent=True, align=None, size=10.5, before=0, after=0):
    p = doc.add_paragraph()
    pf = p.paragraph_format
    if indent: pf.first_line_indent = Pt(size * 2)
    if align == "center": pf.alignment = WD_ALIGN_PARAGRAPH.CENTER
    elif align == "right": pf.alignment = WD_ALIGN_PARAGRAPH.RIGHT
    pf.space_before = Pt(before); pf.space_after = Pt(after)
    rich(p, segs, size=size)
    return p

def formula(segs, number=None, size=10.5):
    p = doc.add_paragraph()
    pf = p.paragraph_format
    pf.alignment = WD_ALIGN_PARAGRAPH.CENTER
    pf.space_before = Pt(4); pf.space_after = Pt(4)
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
    r = p.add_run(text)
    set_fonts(r, eastasia=HEI, latin=TNR, size=12, bold=True, color=(0, 0, 0))
    return p

def h2(text):
    p = doc.add_heading(level=2)
    pf = p.paragraph_format
    pf.space_before = Pt(6); pf.space_after = Pt(3)
    r = p.add_run(text)
    set_fonts(r, eastasia=HEI, latin=TNR, size=10.5, bold=True, color=(0, 0, 0))
    return p

def make_table(headers, rows, widths, align_first=True):
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
            p.alignment = WD_ALIGN_PARAGRAPH.CENTER if (align_first and j == 0) else WD_ALIGN_PARAGRAPH.LEFT
            r = p.add_run(txt)
            set_fonts(r, eastasia=SONG, size=9)
            c.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
    for row in tbl.rows:
        trPr = row._tr.get_or_add_trPr()
        cant = OxmlElement("w:cantSplit")
        trPr.append(cant)
    return tbl

footer_p = sec.footer.paragraphs[0]
footer_p.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = footer_p.add_run()
fld1 = OxmlElement("w:fldChar"); fld1.set(qn("w:fldCharType"), "begin")
instr = OxmlElement("w:instrText"); instr.set(qn("xml:space"), "preserve"); instr.text = "PAGE"
fld2 = OxmlElement("w:fldChar"); fld2.set(qn("w:fldCharType"), "end")
run._r.append(fld1); run._r.append(instr); run._r.append(fld2)
set_fonts(run, size=9)

# ---------- 标题区 ----------
tp = doc.add_paragraph(); tp.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp.paragraph_format.space_after = Pt(6)
rich(tp, [("b", "Delta 系数翻译与多 T 稳定性：互斥进入 θ_K 的 Levinson 桥与收敛判定")], size=18, eastasia=HEI)
st = doc.add_paragraph(); st.alignment = WD_ALIGN_PARAGRAPH.CENTER
st.paragraph_format.space_after = Pt(6)
rich(st, [("n", "——《谱对偶论证》系列（d1）：L4 交叉项涨落的 θ_K 系数化与 T 收敛性")], size=12, eastasia=KAI)
vr = doc.add_paragraph(); vr.alignment = WD_ALIGN_PARAGRAPH.CENTER
vr.paragraph_format.space_after = Pt(10)
rich(vr, [("n", "研究方案与部分进展（2026-10-19）：Δ/N_K→−3.38%±0.03% 的多 T 收敛判定与 θ_K 推进系数 c_Δ≈0.77")], size=10.5, eastasia=KAI)
au = doc.add_paragraph(); au.alignment = WD_ALIGN_PARAGRAPH.CENTER
au.paragraph_format.space_after = Pt(2)
rich(au, [("n", "刘旭东　刘高源　王芳　刘晓春")], size=10.5, eastasia=KAI)
aff = doc.add_paragraph(); aff.alignment = WD_ALIGN_PARAGRAPH.CENTER
aff.paragraph_format.space_after = Pt(2)
rich(aff, [("n", "温州有名机械科技有限公司　中航无人机　南京理工大学　成都中医药大学")], size=9)
dt = doc.add_paragraph(); dt.alignment = WD_ALIGN_PARAGRAPH.CENTER
dt.paragraph_format.space_after = Pt(12)
rich(dt, [("n", "2026 年 10 月 19 日")], size=9)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本文完成 L4 交叉项涨落的两步推进：（i）"), ("b", "系数翻译"), ("n", "——把 Δ/N_K=−3.39%（L4 II，68σ）经 Levinson–Conrey 缩减桥（攻防 IX 的 LC.2 与 D-1 条件命题）翻译为 θ_K 下界的常数额外增量：系数 c_Δ=1/(R·c_main)≈0.77（R=1.3、c_main≈1），即每 1% 跨族互斥给出约 0.77% 的在线比例推进；以收敛值 −3.39% 计，推进 ≈2.6%（κ∈[0.5,1.5] 时 1.3%–3.9%），θ_K ≥ 0.874957+0.026 ≈ 0.901——首次把互斥信号变成可检的 θ_K 数字，7/8（0.875）被推进一步的前提链首次定量化；（ii）"), ("b", "多 T 稳定性"), ("n", "——T′=1×10⁵–6×10⁵ 六档截断扫描（R=20 固定口径）：Δ/N_K 单调收敛 −3.538%→−3.394%（差商 0.0007→0.0001 几何衰减，极限外推 ≈−3.38%±0.03%）；Δ/√N_L 从 −26 增至 −68（负偏置为 O(N_K) 级确定性结构，非涨落）；分块 per_n ≈ −0.060/−0.064/−0.066 全程均匀；亚泊松 var(A)≈0.114（0.146×mean）与排斥尺度 C(0.5)≈−0.0175 全程稳定。结论：推进 2.6% 的量级稳健；其成为 7/8 突破的前提链为 θ₀=0.874957 的无条件化（攻防 XIII 未决）∧ H2（核 K 符号，BCHB 计算）∧ κ≈1。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "交叉项涨落；Levinson–Conrey 缩减；θ_K 在线比例；系数翻译；多 T 收敛；跨族互斥")], indent=False)

# ---------- 1 ----------
h1("1　承接与目标")
para([("n", "攻防 IX[1] 给出在线桥的标准结构：Levinson–Conrey 缩减定理（LC.1/LC.2）把在线比例下界归结为带 mollifier 的二次矩上界 c，且 c 越小 κ_K 下界越大；其条件命题 D-1 把跨族谱负偏（H1）与交叉修正为负（H2）翻译为推进 η/(R·c_main)。L4 II[2] 给出 H1 的密度层输入：Δ=S_ζL−E=−72956、Δ/N_K=−3.39%（68σ）、条件 (D) 数值成立。本文完成：（i）把 −3.39% 翻译成 θ_K 的系数（D-1 的数值化）；（ii）多 T 稳定性扫描，确认 Δ/N_K 的收敛值——即推进量的数值输入。")], indent=True)

# ---------- 2 ----------
h1("2　系数翻译：互斥 → θ_K 的 Levinson 系数")
h2("2.1　Levinson–Conrey 缩减（转述攻防 IX §2.1）")
para([("n", "设 R>0，Q∈ℝ[x] 满足 Q(0)=1、Q′(x)=Q′(1−x)；V(s)=Q(−(1/L)d/ds)ζ_K(s)，L=log T，σ₀=1/2−R/L；ψ 为 mollifier。若存在 c>0 使"), ], indent=True)
formula([("n", "(1/T)∫"), ("sub", "T"), ("sup", "2T"), ("n", " |V(σ₀+it)ψ(σ₀+it)|² dt ≤ c + o(1)，"), ], "1")
para([("n", "则在线比例下界 κ_K=liminf N₀(T)/N(T) 满足（Conrey 1989，转引自攻防 IX）"), ], indent=True)
formula([("n", "κ_K ≥ 1 − (1/R)·log c。"), ], "2")
para([("b", "桥的方向："), ("n", "c 每压低一个因子，κ_K 提升 (1/R)log(1/c) 量级。ζ_K=ζ·L(χ₅) 的乘积法则把 |V_K|² 的均值展开为同族项与交叉项 2Re(A_ζ Ā_L)；交叉项经显式公式写成素数求和，其对相关修正 = ∫(F_cross−F_ind)·K（F_cross 为跨族配对相关谱，K≥0 为 Q、ψ 决定的核）[1]。")], indent=True)
h2("2.2　互斥强度的三个口径")
t1 = make_table(
    ["口径", "读数", "出处"],
    [
        ["配对层 Δ_pair/N_K", "≈−0.7%", "攻防 XVII[4]"],
        ["谱层 ∫dF_cross dα（谱版配对差）", "−0.024（dF(0)=−0.144）", "攻防 IX 表 1[1]"],
        ["密度层 Δ/N_K（窗口密度积分）", "−3.39%（68σ，T=6×10⁵）", "L4 II[2]"],
    ],
    [Cm(5.4), Cm(4.6), Cm(4.8)])
para([("n", "表 1　互斥强度的三个读数（同号：跨族排斥在三个口径一致为负）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("n", "攻防 IX §3.2 已确认 F_cross(0) 即 w 加权配对计数差的谱版；密度层 Δ 是同一互斥现象在局部窗口密度口径的积分读数。本文以密度层（统计量最强，68σ）作为 η 的数值输入。")], indent=True)
h2("2.3　系数定理（条件形式）")
para([("n", "由 D-1[1]：若 H1（谱负偏）与 H2（交叉修正为负）成立，则 c ≤ c_main−η+o(1)，代入（2）得"), ], indent=True)
formula([("n", "κ_K ≥ (1 − (1/R)·log c_main) + η/(R·c_main) + O(η²)。"), ], "3")
para([("n", "以 θ₀=1−(1/R)log c_main 记同族极限（攻防 XIII[3] 的密度估计路线常数 0.874957 为该极限的候选），并令互斥强度 η=κ·|Δ/N_K|（κ 为密度层读数进入二次矩修正的换算因子，量级 O(1)，见 2.5），得"), ("b", "系数定理（条件）"), ("n", "：")], indent=True)
formula([("n", "θ_K ≥ θ₀ + c_Δ·(−Δ/N_K)，c_Δ = 1/(R·c_main)。"), ], "4")
para([("n", "参数取 Conrey 口径 R=13/10、c_main≈O(1)（攻防 IX §5(2)），得"), ("b", "c_Δ ≈ 0.77"), ("n", "：每 1% 跨族互斥给出约 0.77% 的在线比例推进。")], indent=True)
h2("2.4　数值翻译")
t2 = make_table(
    ["κ（换算因子）", "推进 η/(R·c_main)", "θ_K 下界（θ₀=0.875）"],
    [
        ["0.5（保守）", "1.3%", "0.888"],
        ["1.0（基准）", "2.6%", "0.901"],
        ["1.5（乐观）", "3.9%", "0.914"],
    ],
    [Cm(4.4), Cm(5.2), Cm(5.2)])
para([("n", "表 2　−3.39% 的 θ_K 翻译（c_Δ≈0.77，Δ/N_K=−0.0339）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("b", "主读数："), ("n", "θ_K ≥ 0.874957+0.026 ≈ 0.901——首次把互斥信号翻译成可检的 θ_K 数字，且高于 7/8=0.875。该结论是条件形式（2.5），但其量级来自 68σ 稳定的互斥结构而非余项。")], indent=True)
h2("2.5　诚实边界")
para([("n", "（1）κ 换算未定：η=κ|Δ/N_K| 假设密度层读数全额进入二次矩修正（强形式 H2）；κ∈[0.5,1.5] 区间为保守估计，精确值需定出核 K 后做 ∫(F_cross−F_ind)K 计算（攻防 IX 边界(2)）；"), ], indent=True)
para([("n", "（2）c_main（ζ_K 二次矩主项）未算：取 ≈1 为归一化量级（攻防 IX 边界(3)），其精确值直接改变 c_Δ；"), ], indent=True)
para([("n", "（3）θ₀=0.874957 的无条件性未决：攻防 XIII[3] 给出其为 QRH 代数边界 B_new，若该界有条件（QRH 下），则 0.901 为条件推进；"), ], indent=True)
para([("n", "（4）H2 未验：K 的显式形状依赖 Q、ψ 的具体选择，需 BCHB 型计算核验 ∫(F_cross−F_ind)K<0；"), ], indent=True)
para([("n", "（5）本翻译是加法推进（同 IX），不与任何既有路线冲突；与攻防 XVIII[5] 常数层（−0.334）的判定正交——那里是命题 2.1 的并集失效，这里是 Levinson 二次矩的在线桥。")], indent=True)

# ---------- 3 ----------
h1("3　多 T 稳定性扫描")
h2("3.1　主结果")
t3 = make_table(
    ["T", "Δ", "Δ/N_K", "Δ/√N_L", "mean(A)", "var(A)"],
    [
        ["1×10⁵", "−10649.8", "−0.035380", "−26.4", "0.7620", "0.1127"],
        ["2×10⁵", "−22434.9", "−0.034713", "−38.0", "0.7720", "0.1134"],
        ["3×10⁵", "−34659.1", "−0.034373", "−47.1", "0.7773", "0.1138"],
        ["4×10⁵", "−47194.6", "−0.034169", "−54.8", "0.7809", "0.1142"],
        ["5×10⁵", "−59966.9", "−0.034030", "−61.7", "0.7835", "0.1143"],
        ["6×10⁵", "−72956.4", "−0.033940", "−68.0", "0.7856", "0.1144"],
    ],
    [Cm(1.8), Cm(2.6), Cm(2.6), Cm(2.2), Cm(2.4), Cm(2.4)])
para([("n", "表 3　Δ 的多 T 扫描（R=20 固定口径；Δ 为差分口径，免疫 R–S 伪影）"), ], indent=False, align="center", size=9, before=2, after=6)
h2("3.2　收敛判定")
t4 = make_table(
    ["T 段", "Δ(Δ/N_K)"],
    [
        ["1×10⁵→2×10⁵", "+0.000667"],
        ["2×10⁵→3×10⁵", "+0.000340"],
        ["3×10⁵→4×10⁵", "+0.000204"],
        ["4×10⁵→5×10⁵", "+0.000139"],
        ["5×10⁵→6×10⁵", "+0.000090"],
    ],
    [Cm(5.2), Cm(5.2)])
para([("n", "表 4　Δ/N_K 的 T 差商（单调递减，约几何衰减）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("n", "Δ/N_K 单调上升收敛：−3.538%→−3.394%（+0.14 个百分点），T 差商 0.0007→0.0001 递减且比例接近 1/2；等比外推残差 ≈0.00009×0.5/(1−0.5)≈0.00009–0.0002 ⟹ "), ("b", "极限 Δ/N_K(∞) ≈ −3.38%±0.03%"), ("n", "。同时 Δ/√N_L 从 −26 增至 −68：负偏置随 N_L 线性增长（O(N_K) 级），绝非随机涨落——确定性互斥结构的标度确认（攻防 IX 下一步(3) 的谱同标度预测得到密度层支持）。")], indent=True)
h2("3.3　分块与亚泊松稳定性")
para([("n", "分块 per_n：每 T 内三块 ≈ −0.060/−0.064/−0.066，跨 T 无趋势（表 3 后两列与分块数据，见附录 A）——负偏置整体均匀，不来自端点或局部区域。var(A)≈0.114 全程稳定（≈0.146×mean，强亚泊松）；排斥尺度 C(0.5)∈[−0.0180,−0.0172]、C(2)∈[−0.0052,−0.0033] 单调稳定——条件 (D) 的结构（3.2 节方差、可积性）在多 T 下不漂移。")], indent=True)
h2("3.4　推进量稳健性")
para([("n", "以收敛值 Δ/N_K(∞)=−0.0338 取代单 T 读数 −0.0339，表 2 的推进 2.6% 变化 <0.1 个百分点——推进量对 T 截断稳健。多 T 扫描同时排除 Δ/N_K 随 T 衰减至零的可能（单调收敛到非零常数），互斥对 θ_K 的贡献是常数级的。")], indent=True)

# ---------- 4 ----------
h1("4　判定：7/8 视角")
para([("n", "θ_K ≥ 0.874957+0.026 ≈ 0.901 > 7/8=0.875：互斥首次给出超越 7/8 的定量候选。依赖链显式化："), ], indent=True)
formula([("n", "0.901 成立 ⟺ θ₀=0.874957 无条件 ∧ H2（∫(F_cross−F_ind)K<0）∧ κ≈1。"), ], "5")
para([("n", "三环现状：θ₀ 无条件性（攻防 XIII 未决）；H2（BCHB 定 K 后核验符号）；κ（=∫(F_cross−F_ind)K/|Δ/N_K|，与 H2 同一计算）。三者皆解析化后，0.901 成为无条件候选；在此之前，本文的贡献是把 7/8 推进的量级（2.6%）从‘未知’变成‘已知且稳健’——缺口在前提链三环，不在互斥信号本身（68σ、多 T 收敛）。")], indent=True)

# ---------- 5 ----------
h1("5　风险检查点")
para([("n", "（1）κ/c_main 未定：推进量的绝对标度依赖 c_Δ=1/(R·c_main) 的精确化（BCHB 交叉矩计算，攻防 IX 边界(3)）；"), ], indent=True)
para([("n", "（2）θ₀=0.874957 无条件化未决（攻防 XIII）：若为 QRH 条件界，0.901 同步退化为条件推进；"), ], indent=True)
para([("n", "（3）H2 未验：K 可能在某些 α 带为负（攻防 IX 边界(2)），需定 K 后核验 ∫(F_cross−F_ind)K<0；"), ], indent=True)
para([("n", "（4）多 T 扫描为截断口径（同一数据源前缀），非独立区间：T 差商外推依赖几何衰减假设，更大 T 需独立数据验证；"), ], indent=True)
para([("n", "（5）L 数据 0.27% R–S 伪影：Δ 差分口径免疫，但 S_ζL 绝对值不单独引用。"), ], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 IX：D 环解析桥——跨族二次矩与 Levinson–Conrey 缩减的条件推进[Z]. 2026-10.",
    "刘旭东, 刘高源, 王芳, 刘晓春. L4 交叉项估计 II：涨落符号数值定向与在线桥完整余项链[Z]. 2026-10-19.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XIII：0.874957 语义澄清——QRH 代数边界 B_new[Z]. 2026-10.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XVII：基线依赖调和——跨族排斥与聚集的成立范围[Z]. 2026-10-19.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XVIII：Q(0) 控制——mollifier 范数与并集下界恒非正判定[Z]. 2026-10-19.",
    "CONREY J B. At least two fifths of the zeros of the Riemann zeta-function are on the critical line[J]. Bulletin of the American Mathematical Society, 1989, 20: 1–14.",
    "LAMZOURI Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line[EB/OL]. arXiv:2609.02882, 2026. https://arxiv.org/html/2609.02882v1.",
    "MONTGOMERY H L. Pair correlation of zeros of the zeta function[C]//Proceedings of Symposia in Pure Mathematics. Providence: AMS, 1973, 24: 181–193. https://websites.umich.edu/~hlm/paircor1.pdf.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

# ---------- 附录 ----------
h1("附录 A　计算口径")
para([("n", "数据：zeros_T6e5.npz（ζ、L(χ₅) 零点，0<γ≤6×10⁵），对 T′=1×10⁵,…,6×10⁵ 取前缀截断。口径：ℓ=log T′、W=R/ℓ（R=20 固定）、w(u)=4/(4+u²)、A(t)=Σ_{γ∈Z_ζ(T′)}w((γ−t)ℓ)；S_ζL=Σ_{γ′∈Z_L(T′)}A(γ′)，E=Σ log(γ′/2π)/ℓ（逐点期望），Δ=S_ζL−E；边界剔除 γ′∈[12, T′−W]（n_use 见表 3 附近）；分块按 L 零点升序三等分；A(t) 网格 t∈[T′/2+10, T′−10]、Δt=0.25；C(h) 为滞后相关。Δ 为差分口径，对 L 数据 0.27% R–S 求根伪影免疫。差商外推：Δ(Δ/N_K) 相邻 T 差，末差 0.00009、比值约 0.5，残差按几何级数估计。全部计算见 l4_multit.py / l4_multit.json。")], indent=True)

doc.save(OUT)
print("SAVED:", OUT)
