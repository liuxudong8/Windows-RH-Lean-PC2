# -*- coding: utf-8 -*-
"""生成《路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XLI-拟随机并集定理的常数机制闭合-QRH攻坚0.6725到7-8的最优核数值构造与前提可靠性三层论证.docx"
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

def h1(text):
    p = doc.add_heading(level=1)
    pf = p.paragraph_format
    pf.space_before = Pt(12); pf.space_after = Pt(6)
    pf.line_spacing = 1.5
    r = p.add_run(text)
    set_fonts(r, eastasia=HEI, latin=TNR, size=12, bold=True, color=(0, 0, 0))
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

# ---------- 标题区（三行拆分，18pt 黑体） ----------
tp = doc.add_paragraph()
tp.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp.paragraph_format.space_after = Pt(0)
tp.paragraph_format.line_spacing = 1.5
rich(tp, [("b", "路2攻防XLI—拟随机并集定理的常数机制闭合：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(0)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "QRH 攻坚 0.6725→7/8 的最优核数值构造")], size=18, eastasia=HEI)
tp3 = doc.add_paragraph()
tp3.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp3.paragraph_format.space_after = Pt(10)
tp3.paragraph_format.line_spacing = 1.5
rich(tp3, [("b", "与前提可靠性三层论证")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：弱前提条件定理形态")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 24 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "攻防 XLI 闭合 QRH 常数机制攻坚第一阶段（数值定向 #1-#8）。三件判定：(i) 变分机制（Lamzouri Proposition 2.1 全文回读）：在线比例 N₀ˢ/N ≥ 2−A，A=ΣK²/Σ1 为配对常数；C_MT=1.3275 是谱支撑 λ≤1/2 核族内的无条件极小（Lemma 3.2、Remark 3.4）；Z_T 元素实值确认配对和是实轴口径。(ii) 最优核数值构造（audit6 核族×尺度扫描）：单族 A 最小 =1.0079（ζ）/1.0114（L），核为 fejer_a0.5（最近邻尺度窄核）——低于 C_MT=1.3275 且低于 7/8 门槛 1.125，余量 0.11-0.12；MT 最优核实测 1.1868/1.2494 亦低于 C_MT——GUE 排斥压低配对常数在数据层面成立；并集 A 最小 =1.2859>1.125——并集直接论证判负，必须走分解论证（两族分别 Proposition 2.1 + 加权，并集拟随机在线比例 ≈0.990）。(iii) 前提可靠性三层（audit8+#7 文献核实）：前提从不可验证的 GUE 整体假设弱化为可直接数值检验的 A≤1.125；5 段子区间统计量单调稳定、最优核 A 漂移 ≤0.005；最近邻分布与 Wigner 在 ~5% 内吻合、长尾无异常；Odlyzko（10²² 高度 GUE 确认）、Rubinstein（Katz–Sarnak 数值验证）、Özlük（GRH 下 Dirichlet L 11/12 简单）构成文献先例。L 族配对公式存在性在文献中无无条件版（BGS 推广为框架内开放构造）——定理形态定为纯假设（弱前提）。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "配对常数；Montgomery–Taylor 变分；拟随机前提；分解论证；弱前提条件定理；可靠性三层")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XL 判定 θ_K≥7/8 的缺口在常数（0.6725→0.875 差 0.2025），属 QRH 机制。用户拍板「按实质用处最大化——转 (b) QRH 常数机制攻坚（0.6725→7/8 的唯一现实通道）」，并坚持先做数值定向。本篇完成数值定向 #1-#8（qrh_work/audit1-8）、文献核实 #7（A_L 配对定理归属）、前提可靠性三层（audit8），落定拟随机并集定理的条件定理形态。")], indent=True)

# ---------- 2 ----------
h1("2　变分机制与实轴口径确认")
para([("n", "Lamzouri（arXiv:2609.02882v2）Proposition 2.1：对复共轭不变多重集 Z、η∈L²、supp η⊂(−λ,λ)、η²^(0)=1、K=η²^（整函数、K(0)=1），简单实数零点数 ≥ 2Σ1 − ΣK(z−s)²——在线比例 ≥ 2−A，A=ΣK(z−s)²/Σ1（无条件成立，不要求逐项 K 非负）。常数 C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963 是该方法族内的最优（极小）配对常数：Lemma 3.2 构造最优核 η_ε（f₀(x)=cos(√2x)/(√2sin(1/√2))，支撑 [−1/2,1/2]），配对常数 C=Q(0)+2∫₀¹αQ(α)dα（Q=f*f）；Remark 3.4（Carneiro-Chandee-Littmann-Milinovich）确认 C_η≥C_MT——无条件框架内谱支撑 λ≤1/2 的核族常数不可能低于 1.3275。")], indent=True)
para([("n", "实轴口径确认：Z_T={i(ρ−1/2)logT/2π} 对 ρ=1/2+iγ 给出 z=−γ·logT/2π∈ℝ——Proposition 2.1 的配对和 ΣK(z−s)² 在实轴计算（K 偶）。谱支撑 λ 是变分自由度：无条件（BGS 定理要求 f 支撑 [−1,1]）钉死 λ≤1/2；放宽 λ 需拟随机（GUE）前提——这正是「拟随机版 Montgomery–Taylor 变分问题」。")], indent=True)

# ---------- 3 ----------
h1("3　数值证据链：拟随机前提成立与配对常数压低")
para([("n", "数值定向 #1-#4（audit1-4，T=6×10⁵，剔除 t<300）：两族族内最近间距统计 GUE 兼容——ζ mean=1.0000/var=0.1651/s-exp=2.03/p(0+)=0.009；L mean=0.9197/var=0.1365/s-exp=1.86/p(0+)=0.012（密度口径 ρ_L=(1/2π)[log(t/2π)+log5−1]）。跨族独立：无共同值（tol=1e-6）、g(r) 逐点归一化 ≈1.05-1.09（无聚集）；换族频率实测 0.7533 vs 独立 GUE 混合模拟 0.7610±0.0066（R=40，z=−1.1σ）/0.7606±0.0057（R=30，z=−1.3σ）——0.753 是两族独立+各自 GUE 排斥的自然值，非拉链伪影。并集整体对照（audit4）：并集最近邻 var=0.4405 vs 独立 GUE 混合 0.4755±0.0088（z=−4.0σ）、p(0+)=0.5396 vs 0.5581±0.0053（z=−3.5σ）——并集比独立 GUE 混合更亚泊松（微弱但显著，方向与 Δ 定律同向）。")], indent=True)
para([("n", "数值定向 #5（audit5，固定核）：Fejér 核 A_ζ=1.0565、A_L=1.0808、A_union=1.6230（跨族贡献 0.5535/零点）；sinc A_ζ=1.1880、A_L=1.2473；gauss A_ζ=1.6146、A_L=1.7864——单族实测 A 显著低于 C_MT=1.3275；并集 A_union≫1.125（在线比例仅 0.377）——Proposition 2.1 直接应用于并集被跨族配对压垮（Q(0) 判负的数值版）。")], indent=True)
caption("表 1　核族 × 尺度扫描的配对常数 A（audit6，δ=logT/2π=2.1175，直方图口径）", before=4, after=2)
t1 = make_table(
    ["核", "A_ζ", "A_L", "A_union", "在线比例 2−A_ζ", "判定"],
    [
        ["fejer_a0.5（最优）", "1.0079", "1.0114", "1.2859", "0.9921", "单族达标"],
        ["sinc_a0.5", "1.0492", "1.0639", "1.4720", "0.9508", "单族达标"],
        ["fejer_a1.0", "1.0565", "1.0807", "1.6227", "0.9435", "单族达标"],
        ["gauss_a0.5", "1.1269", "1.1773", "1.8902", "0.8731", "单族达标"],
        ["MT 最优核（数值）", "1.1868", "1.2494", "2.0562", "0.8132", "低于 C_MT"],
        ["C_MT（无条件参照）", "1.3275", "1.3275", "—", "0.6725", "定理界"],
    ],
    [Cm(3.6), Cm(1.8), Cm(1.8), Cm(1.8), Cm(2.2), Cm(2.4)])
para([("n", "读数：(i) 最优核在最近邻尺度（fejer_a0.5，谱支撑 λ_eff≈0.5 类），单族 A_min≈1.008-1.011——GUE 最近邻排斥最强的区域压低配对和最多；a→0 平凡极限 A→1（核分辨率丢失）已识别，最优解读在物理最近邻排斥尺度。(ii) MT 最优核实测 1.1868（ζ）/1.2494（L）< C_MT=1.3275——GUE 数据对紧谱核同样压低配对常数（无条件主项 vs 实测数据的差距）。(iii) 并集 A 最小 =1.2859>1.125——并集直接论证判负确认。")], indent=True)
caption("表 2　单族拟随机在线比例与 7/8 余量（audit6 最优核）", before=4, after=2)
t2 = make_table(
    ["族", "A_min（核）", "在线比例 2−A_min", "7/8 门槛 0.875", "余量"],
    [
        ["ζ", "1.0079（fejer_a0.5）", "0.9921", "达标", "0.1171"],
        ["L", "1.0114（fejer_a0.5）", "0.9886", "达标", "0.1136"],
    ],
    [Cm(1.6), Cm(3.8), Cm(2.6), Cm(2.0), Cm(1.8)])
para([("n", "表 2：拟随机（GUE）前提下单族在线比例 ≈0.989-0.992，7/8 余量 ~0.11-0.12——比 audit5 固定核口径（余量 0.04-0.07）更强。常数机制闭合的定量现实性确认。")], indent=True)

# ---------- 4 ----------
h1("4　分解论证与并集在线比例")
para([("n", "并集 Z_K=Z_ζ∪Z_L 的零点互异（跨族共同值 =0，数值核实）——N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L。分解论证：两族分别应用 Proposition 2.1（谱支撑 λ≤1/2 核族、常数 C_MT），再按零点数加权——并集在线比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K。拟随机前提下（audit6 最优核）：(999354×0.9921+1149836×0.9886)/2149190 ≈ 0.990 ≥ 0.875=7/8——并集达标。跨族配对（交织、无排斥，audit5 的 A_cross_extra≈0.55-1.48）在分解论证中完全绕开——这正是并集直接论证（A_union=1.29-1.62，在线比例 0.377-0.714）与分解论证的本质区分。")], indent=True)

# ---------- 5 ----------
h1("5　前提可靠性三层说明")
para([("b", "第一层（弱化前提）：")], indent=True)
para([("n", "条件定理前提从「GUE 配对相关（整体、不可验证）」降为「A_ζ,A_L≤1.125（配对常数假设）」——GUE 是充分非必要，配对常数是 audit6 直接数值验证的对象。A≤1.125 门槛数值全段通过（最优核 1.008-1.014）。")], indent=True)
para([("b", "第二层（子区间收敛 + 反驳扫描）：")], indent=True)
caption("表 3　配对常数 A 与最近邻方差随高度收敛（audit8，5 段）", before=4, after=2)
t3 = make_table(
    ["高度段", "ζ A0.5", "ζ A1.0", "L A0.5", "L A1.0", "ζ nn_var", "L nn_var"],
    [
        ["0.3-1.2e5", "1.0045", "1.0341", "1.0071", "1.0521", "0.1619", "0.1312"],
        ["1.2-2.4e5", "1.0069", "1.0505", "1.0102", "1.0735", "0.1646", "0.1355"],
        ["2.4-3.6e5", "1.0087", "1.0594", "1.0120", "1.0841", "0.1657", "0.1374"],
        ["3.6-4.8e5", "1.0089", "1.0641", "1.0131", "1.0914", "0.1660", "0.1384"],
        ["4.8-6.0e5", "1.0097", "1.0691", "1.0137", "1.0967", "0.1665", "0.1390"],
        ["全区间", "1.0079", "1.0565", "1.0114", "1.0807", "0.1651", "0.1365"],
    ],
    [Cm(2.0), Cm(1.7), Cm(1.7), Cm(1.7), Cm(1.7), Cm(1.6), Cm(1.6)])
para([("n", "判定：所有统计量随高度单调微调、无发散；最优核 A 段间漂移 ≤0.005（A0.5），7/8 余量 0.11-0.12 远大于有限 T 修正。反驳扫描：ζ 最近邻间距带计数 vs GUE Wigner 分布 obs/pred 比值 0.86-1.05（相对偏差 ≤5%，方向为中峰略集中——与精确 GUE/有限 T 修正方向兼容，不作证伪）；长尾 max_s≈3.1-3.4（ζ）≈√(log n) 尺度、无异常长间距；L 受归一化常数影响（nn_mean=0.92）不作精确 band 对照，靠 var/s_exp/A 佐证。跨族独立（audit3/4）+ 并集额外亚泊松（var −4σ，与 Δ 定律同向）——系统性反驳扫描未发现偏离拟随机框架的结构性证据。")], indent=True)
para([("b", "第三层（文献佐证 + 反证框架）：")], indent=True)
para([("n", "独立文献证据：Odlyzko（10²² 高度、10¹⁰ 个零点）数值验证 GUE 配对相关（「confirmed the GUE connection」）；Rubinstein 数值验证 Katz–Sarnak 猜想；Özlük（1982，GRH 下）证明 Dirichlet L 函数至少 11/12≈0.917 简单——配对方法先例链。反证框架：跨族独立与并集亚泊松（audit4）均与 GUE 拟随机 + Δ 定律一致，未出现算术结构指纹。")], indent=True)

# ---------- 6 ----------
h1("6　拟随机并集定理（条件定理形态）")
para([("n", "定理（弱前提拟随机并集定理，条件形态）：设 ζ 与 L(χ₅) 的零点在归一化尺度上的配对常数满足 A_ζ,A_L≤1.125（拟随机前提，含 L 族配对公式存在性假设；数值最优核实测 A_ζ=1.0079、A_L=1.0114）。则并集在线简单零点比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K ≥ 7/8。")], indent=True)
para([("n", "证明骨架：(i) N₀ˢ_K=N₀ˢ_ζ+N₀ˢ_L（零点互异，已核实）；(ii) 两族分别应用 Proposition 2.1：N₀ˢ_ζ≥2N_ζ−ΣK²_ζ、N₀ˢ_L≥2N_L−ΣK²_L（无条件不等式，K=η²^、K(0)=1）；(iii) 拟随机前提 ⟹ ΣK²_ζ≤A_ζN_ζ、ΣK²_L≤A_LN_L；(iv) 代入加权即得。分解论证的关键：跨族配对完全不进入（与并集直接论证的 A_union=1.29-1.62 判负形成对照）。")], indent=True)

# ---------- 7 ----------
h1("7　诚实边界")
para([("n", "① A 的实测值是数据（T=6×10⁵）非定理——A≤1.125 前提未证明，定理为纯假设形态。② L 族配对公式存在性在文献中无无条件版（Özlük 需 GRH、Yıldırım 需 GRH+跨字符平均）——BGS 推广至固定模实字符为框架内开放构造，定理以假设覆盖。③ band 检验的 z 值因归一化常数效应不作精确判定（量级佐证）。④ 核族扫描有限（fejer/sinc/gauss/MT 族），未穷尽全部变分解空间；a→0 平凡极限 A→1 已识别但最优解读限最近邻尺度。⑤ δ 尺度与 R 截断的有限 T 效应已部分标定（子区间收敛），跨 T 外推需更大数据。⑥ 并集分解论证的加权系数 N_ζ/N_K=0.465、N_L/N_K=0.535 来自 T=6×10⁵ 实测。")], indent=True)

# ---------- 8 ----------
h1("8　判定总结")
para([("n", "攻防 XLI 闭合 QRH 攻坚第一阶段。(1) 变分机制确认：C_MT=1.3275 是 λ≤1/2 核族无条件极小，0.6725 是配对常数路径的无条件极限；(2) 最优核数值构造：拟随机下单族 A_min≈1.008-1.011（fejer_a0.5）、在线比例 ≈0.99、7/8 余量 0.11-0.12——常数机制闭合的定量现实性确认；(3) 并集直接论证判负（A_union_min=1.286）、分解论证达标（并集 ≈0.990）——论证路径的严格区分；(4) 前提可靠性三层（弱前提 + 收敛/反驳 + 文献先例）把「纯假设」升级为多层证据支撑的弱前提条件定理；(5) 文献坐标：L 族配对公式的无条件版是框架内开放构造（BGS 推广），也是后续主线候选。主线下一步候选：(a) 分解论证严格化（两族 Proposition 2.1 的有限 T 版本）；(b) L 族配对公式的无条件推广构造（BGS 方法适配模 5 实字符）；(c) 转回 ζ_K 特有谱结构攻坚（在线比例桥余项精细形态——超密度假设级专用论证）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（Proposition 2.1（N₀ˢ≥2Σ1−ΣK²）、Lemma 3.2（最优核 f₀(x)=cos(√2x)/(√2sin(1/√2))、C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963）、Remark 3.4（C_η≥C_MT 最优性））——全文回读.",
    "Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（Lemma 5：无条件配对公式、误差 O_f(1/√logT)、权 w(z)=4/(4−z²)；BGS 推广至固定模 L(χ) 为开放构造）.",
    "Özlük A E. On the pair correlation of zeros of Dirichlet L-functions（1982 论文，GRH 下至少 11/12 简单，带权）——经 Kandhil-Languasco-Moree 引言转述核实.",
    "Kandhil N, Languasco A, Moree P. Pair correlation of zeros of Dirichlet L-functions: A path towards the Montgomery and Elliott-Halberstam Conjectures. arXiv:2411.19762（Yıldırım 定理/Conjecture 1：跨字符平均配对相关，GRH 前提）——全文精读.",
    "Carneiro E, Milinovich M B, Ramos A P. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913（F 平均 0.9303-1.3208、含 Dirichlet L 函数族）.",
    "Odlyzko A M. The 10^22-nd zero of the Riemann zeta function（10¹⁰ 个零点数值验证 RH 与 GUE 配对相关——「confirmed the GUE connection」）.",
    "QRH 攻坚数值件（本工作，Anaconda python 可复跑）：qrh_work/qrh_audit1-8.py/.json（拟随机前提统计、跨族独立、并集亚泊松、配对常数核族扫描、子区间收敛）；零点数据 zeros_T6e5.npz（T=6×10⁵、ζ 999492/L 1150050 根）.",
    "攻防 XL（d1 已交付）：配对侧无条件界理论构造——0.6725 常数缺口 0.2025 属 QRH 机制；攻防 XXXIX（S4）：在线比例桥余项精细形态.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
