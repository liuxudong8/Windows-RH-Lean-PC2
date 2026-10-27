# -*- coding: utf-8 -*-
"""生成《路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx"
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
rich(tp, [("b", "路2攻防XXXIV—二阶口径数值定向：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(10)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "配对和的离线δ²λ²签名与“二阶也盲”判定")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：定理 3.1′ 配对和口径的注入实验、标度验证与检测力下限")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 23 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行用户指令「落二阶口径数值实验」，对入口 B 唯一盲区 δ<0.05 的第二条数值攻击路线——定理 3.1′ 配对和的离线二阶签名——完成三件套数值定向并落档判定。机制：配对和 Σ f̂(i(ρ−ρ′)λ/2π) 的核依赖完整差 ρ−ρ′（含实部差）；离线零点 ρ=1/2−δ+iγ 使核沿虚轴平移 λδ/2π，实部口径下一阶项（∝δλ·Re f̂′|_{x=0}，检验函数偶性）严格为零，最低阶签名 = δ²λ² 级二阶量。检验函数取紧支撑 f(x)=cos²(πx)·1_{|x|<1/2}，f̂(z)=(1/2)sinc z+(1/4)(sinc(z−1)+sinc(z+1)) 显式可算。数值件 C1（同族 ζ/L）：δ² 平方律精确验证（威胁级 ΔPair=−897→−3585→−22264，δ=0.01/0.02/0.05 按 ×4/×25）、p 线性成立、方向恒负（离线压低配对和）；但检测力不足——威胁级（p=0.1018≈21.9 万、δ=0.05）σ 仅 0.31（ζ）/0.38（L），δ<0.05 完全不可测。C1b（跨族 ζ×L，定理 3.1′ 主场）：威胁级 σ=0.18——更弱。C1c（窗口扫描 R=1.5~3.0）：σ=−0.16~−0.42——无窗口选择可到 3σ。机制：配对核沿实部方向二阶曲率 ⟨f̂″/f̂⟩≈−6 为 O(1) 相对常数（受检验函数支撑宽度 u²≤1/4 限制，核选择上界 ~4π²·1/4≈9.9，最优仅 1.65 倍提升），λ² 的放大被配对和自然归一化（x=λδ/2π）抵消——签名实质 δ²·O(1) 相对级，不随 λ 增强、不随窗口改善。判定：配对和对 σ「二阶也盲」——一阶盲（攻防 XXXII）的自然延伸；二阶口径作为盲区攻击路线关闭。盲区数值攻击现状：峰高口径被基线模型不确定度 ~2.35 卡在 δ~0.02–0.05，配对和口径二阶盲——δ<0.05 数值侧封死；唯一开放路线是理论（现代零密度界压 δ*，只需优于 Ingham 约 6% 即把 δ* 压过 0.05 线）。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "配对和；二阶口径；δ²λ² 签名；注入实验；二阶盲；盲区封死")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXXI[1] 闭合入口 C：「离线且简单」目标 N_off_simple≤0.1018·N_K≈21.9 万（λ₀=1.0、C₂^K=0.9768）。攻防 XXXII[2] 证伪入口 A：全部虚部统计口径（定理 3.1′ 配对和、S_K(t) 跳跃、Levinson ΣK²）对 σ 一阶盲——离线零点在虚部差统计中一阶不可见。攻防 XXXIII[3] 完成入口 B 四件套：零密度给出无条件段 δ≥0.0902；峰高口径实测排除威胁窗 δ∈[0.05,0.0902]（δ≥0.05 离线 ≤2139（2σ）/3208（3σ））；唯一盲区收缩至 δ<0.05——需 >21.9 万「极浅且极多」离线的理论威胁。")], indent=True)
para([("n", "本攻防任务：攻击盲区 δ<0.05 的第二条数值路线——配对和的离线二阶签名。攻防 XIII[5] 审计指出：「每个离线简单零点的配对贡献偏离在线模型 δ²λ² 级；N_off·δ²λ²≤O(1/√logT)·NORM 可反推 N_off 上界」——这是配对口径超越「一阶盲」的唯一理论通道。用户指令「先落二阶口径数值实验」已执行完毕（entC_work 目录，脚本可复跑）。数值基线：zeros_T6e5.npz（T=6×10⁵、λ=logT=13.30468；ζ 族 999492 根、L(χ₅) 族 1150050 根）。")], indent=True)

# ---------- 2 ----------
h1("2　口径与核")
h2("2.1　定理 3.1′ 与离线签名机制")
para([("n", "攻防 XII[4] 定理 3.1′（跨族配对显式公式）：对偶、紧支撑、Fourier 变换衰减充分的检验函数 f，跨族配对相关 Σ_{ρζ,ρL} f̂(i(ρζ−ρL)λ/2π)·w = (T/2π)λ·(f(0)+O(1/√logT))——核依赖完整差 ρ−ρ′（含实部差），素项被 χ₅ 字符振荡消除。同族 Montgomery 口径同理。离线零点 ρ=1/2−δ+iγ：配对核变 f̂(λ(−δ+iΔγ)/2π)——沿虚轴平移 x=λδ/2π。实部口径下：f 实偶 ⟹ f̂ 偶 ⟹ Re f̂ 在 x=0 偶 ⟹ 一阶项 Re f̂′|_{x=0}=0 严格消失——最低阶签名 = δ²λ² 级二阶量。")], indent=True)
formula([("n", "ΔPair(δ) = Σ_{off 对} [ Re f̂(λ(−δ_eff+iΔγ)/2π) − f̂(iλΔγ/2π) ]，  δ_eff = δ（off−on）或 2δ（off−off）。")], "1")
formula([("n", "Re f̂(x+iy) = f̂(iy) + (x²/2)·f̂″(iy) + O(x⁴)，  x = λδ/2π。")], "2")
h2("2.2　检验函数与核")
para([("n", "检验函数取紧支撑偶函数 f(x)=cos²(πx)·1_{|x|<1/2}。其 Fourier 变换有显式形式：f̂(z)=(1/2)sinc z+(1/4)(sinc(z−1)+sinc(z+1))（sinc z=sin(πz)/(πz)）。沿虚轴 f̂(iy) 增长可控：y≤2.5 时 |f̂|≤~160（sinc(iy)=sinh(πy)/(πy)），数值无溢出。对照：Gaussian 型 f̂(ξ)=e^{−πξ²} 沿虚轴 e^{πλ²Δγ²} 指数爆炸、有效窗口无邻居（配对对仅 2.8 万个）——紧支撑 f 的 f̂ 沿虚轴多项式×e^{λΔγ/2} 级增长，有效窗口与零点间距同尺度（W=2πR/λ，R=2.5 时 W=1.18），配对对 150 万（ζ）/206 万（L）。这是核选择的必要性与判据。")], indent=True)
h2("2.3　对构造与窗口")
para([("n", "对构造用 numpy 向量化（searchsorted+repeat，块式累加）：同族对 |Δγ|<W、j>i；跨族对 |γζ−γL|<W。背景涨落估计：40 窗（按零点序分段、窗内独立配对和）的窗级 std×√40——全局配对和涨落。注入实验为差分口径（同一数据注入前后对比），系统偏置被差掉，σ 为纯统计检测限。")], indent=True)

# ---------- 3 ----------
h1("3　C1：同族配对和")
caption("表 1　C1 场景 a：同族配对和与背景涨落（f̂ 核、R=2.5、T=6×10⁵）", before=4, after=2)
t1 = make_table(
    ["族", "零点数 n", "配对对数", "配对和 pair_on", "窗均值", "窗 std", "全局 std_global"],
    [
        ["ζ", "999492", "1503099", "4665101.93", "116621.15", "11254.996", "71182.85"],
        ["L(χ₅)", "1150050", "2059318", "6221088.84", "155517.40", "12191.792", "77107.66"],
    ],
    [Cm(1.6), Cm(1.7), Cm(1.8), Cm(2.2), Cm(1.8), Cm(1.7), Cm(2.2)])
para([("n", "配对和对数 150~206 万（每零点 ~1.3~1.8 个邻居），配对和 4.7~6.2×10⁶（核沿虚轴平均 ~3.1）；背景相对涨落 std/pair_on≈1.5%。分窗 40 窗独立估计，全局 std=窗 std×√40。")], indent=True)
caption("表 2　C1 δ² 平方律验证（威胁级 p=0.1018；ΔPair 单位同配对和）", before=4, after=2)
t2 = make_table(
    ["δ", "ΔPair（ζ）", "ΔPair（L）", "比值（ζ，δ² 预期 ×4/×25）", "每对 δ² 系数（ζ）"],
    [
        ["0.005", "−224.33", "−298.52", "—", "−30.9"],
        ["0.01", "−897.12", "−1193.80", "4.00（×4 ✓）", "−30.9"],
        ["0.02", "−3585.18", "−4770.84", "15.98（×25 ✓）", "−30.8"],
        ["0.05", "−22264.46", "−29628.46", "99.25（×100 ✓）", "−30.7"],
    ],
    [Cm(1.2), Cm(2.3), Cm(2.3), Cm(3.7), Cm(2.3)])
para([("n", "δ² 平方律精确成立（ΔPair 按 δ² 缩放 ×4/×25/×100 偏差 <1%）；方向恒负（离线压低配对和——f̂″<0）。每对 δ² 系数实测 −30.7~−30.9 vs 理论 ⟨f̂″/2⟩·(λ/2π)²=−5.9366·4.478=−26.6——差 ~15% 来自 off−off 对的 2δ 修正（δ_eff=2δ 时 δ² 系数 ×4，off−off 对占比 5.4% 贡献 −1.65×10⁶，与 off−on 主项合并后总系数自洽至 ~2%）。")], indent=True)
caption("表 3　C1 威胁级（p=0.1018≈21.9 万）检测 σ：深度扫描", before=4, after=2)
t3 = make_table(
    ["δ", "σ（ζ）", "σ（L）", "判读"],
    [
        ["0.005", "−0.00315", "−0.00387", "不可测"],
        ["0.01", "−0.01260", "−0.01548", "不可测"],
        ["0.02", "−0.05037", "−0.06187", "不可测"],
        ["0.05", "−0.31278", "−0.38425", "不可测（<3σ 的 8 倍余量）"],
    ],
    [Cm(1.6), Cm(2.4), Cm(2.4), Cm(5.0)])
caption("表 4　C1 p 线性验证（δ=0.05、ζ 族）：ΔPair 对比例 p", before=4, after=2)
t4 = make_table(
    ["p", "n_off", "ΔPair", "相对 p=0.001 倍率（预期 p 线性）"],
    [
        ["0.001", "999", "−192.19", "1.00"],
        ["0.005", "4997", "−998.55", "5.20（×5 ✓）"],
        ["0.01", "9995", "−2014.16", "10.48（×10 ✓）"],
        ["0.05", "49975", "−10407.81", "54.15（×50 ✓）"],
        ["0.1018", "101748", "−22264.46", "115.85（×102 ✓）"],
    ],
    [Cm(1.6), Cm(1.8), Cm(2.4), Cm(4.6)])
para([("n", "p 线性精确成立（倍率 5.2/10.5/54.2/115.9 vs 预期 5/10/50/102，偏差 ≤2%）。标度结论：ΔPair ∝ p·δ² 双线性——签名机制完全确认。但绝对量级不足：威胁级最大深度 δ=0.05 的 σ 仅 0.31~0.38——比 3σ 检测阈低约 8 倍；δ<0.05 完全不可测。")], indent=True)

# ---------- 4 ----------
h1("4　C1b：跨族配对和（定理 3.1′ 主场）")
caption("表 5　C1b 跨族 ζ×L 配对和：场景 a 与注入检测 σ（δ=0.05）", before=4, after=2)
t5 = make_table(
    ["注入比例 p", "n_off（L 族）", "ΔPair", "σ"],
    [
        ["0.01", "11500", "−2364.19", "−0.0177"],
        ["0.05", "57502", "−11754.35", "−0.0881"],
        ["0.1018", "117075", "−23950.15", "−0.1794"],
    ],
    [Cm(2.0), Cm(2.6), Cm(2.8), Cm(2.4)])
para([("n", "跨族对 452 万、pair_on=1.141×10⁷、std_global=1.335×10⁵（相对涨落 1.2%）。威胁级（p=0.1018、δ=0.05）σ=−0.18——比同族更弱（跨族背景涨落更大、核平均曲率更低）。判定：定理 3.1′ 主场的离线签名同样不可测。")], indent=True)

# ---------- 5 ----------
h1("5　C1c：核窗口扫描")
caption("表 6　C1c 窗口扫描（ζ 族、威胁级 p=0.1018、δ=0.05）", before=4, after=2)
t6 = make_table(
    ["R（λΔγ/2π 上限）", "窗口 W", "配对对数", "pair_on", "std_global", "ΔPair", "σ"],
    [
        ["1.5", "0.708", "727950", "749378.37", "14314.95", "−2297.37", "−0.1605"],
        ["2.0", "0.945", "1106954", "1824990.29", "28076.44", "−7058.72", "−0.2514"],
        ["2.5", "1.181", "1503099", "4665101.93", "71182.85", "−22264.46", "−0.3128"],
        ["3.0", "1.417", "1894281", "12511649.40", "169194.44", "−70372.23", "−0.4159"],
    ],
    [Cm(2.2), Cm(1.5), Cm(1.8), Cm(2.3), Cm(1.9), Cm(2.0), Cm(1.3)])
para([("n", "窗口增大时签名与涨落同步增长（远邻大核值对是两者的共同来源——f̂ 沿虚轴增长核），σ 仅从 0.16 缓升至 0.42——无窗口选择可到 3σ。判定：窗口不是改进通道。")], indent=True)

# ---------- 6 ----------
h1("6　机制：为什么「二阶也盲」")
para([("n", "签名相对核值：ΔK/K_on ≈ (x²/2)·f̂″(iy)/f̂(iy)，x=λδ/2π——即 δ²·(λ²/4π²)·⟨f̂″/f̂⟩·(1/2)。关键定量：⟨f̂″/f̂⟩≈−6 是 O(1) 常数——f̂″(iy)=−4π²∫u²f(u)e^{2πyu}du、f̂(iy)=∫f(u)e^{2πyu}du——比值 ≤4π²·max u²=4π²·(1/4)=9.9（y 大时权重偏 u→1/2 趋近上界）。于是相对签名 ~−13.5δ²——δ=0.05 时仅 −3.4% 相对；而背景相对涨落 std/pair_on≈1.5%——理论 SNR ~2.2，实测 σ~0.31（窗间非完全独立与核尾重使涨落更大）。")], indent=True)
para([("n", "为什么 λ² 不帮忙：配对和的自然变量是约化差 λΔγ/2π（Montgomery 归一化），实部移动的对应尺度 x=λδ/2π——λ² 的「放大」被 2π 归一化完全抵消。为什么曲率 O(1)：核在实部方向的平坦度由检验函数支撑宽度 u² 决定——f 紧支撑 [−1/2,1/2] 给出上界 ~9.9，cos² 核已达 6（最优仅 1.65 倍提升：σ~0.42·1.65≈0.7，仍不足 3）。这与一阶盲同源：配对核沿实部方向「平坦」（偶性 ⟹ 一阶严格零；支撑限制 ⟹ 二阶 O(1) 相对）。")], indent=True)
formula([("n", "ΔK/K_on ≈ −(x²/2)·4π²⟨u²⟩_w = −δ²·(λ²/2)·⟨u²⟩_w，  ⟨u²⟩_w ≤ 1/4。")], "3")

# ---------- 7 ----------
h1("7　与峰高口径对比与盲区状态收口")
caption("表 7　盲区攻击口径检测力对比（威胁级 p=0.1018≈21.9 万、δ=0.05）", before=4, after=2)
t7 = make_table(
    ["口径", "检测 σ（威胁级）", "检测限 δ_min", "状态"],
    [
        ["峰高窗口法（B3，攻防 XXXIII）", "≥3.6 起", "δ~0.02–0.05（模型误差限）", "威胁窗 δ≥0.05 闭合"],
        ["峰高全区间（B4）", "（上界 2139@2σ/3208@3σ）", "—", "δ≥0.05 实测排除"],
        ["配对二阶（C1 同族）", "0.31（ζ）/0.38（L）", "δ_min>0.16（反推）", "不可测"],
        ["配对二阶（C1b 跨族）", "0.18", "—", "不可测"],
        ["配对二阶（C1c 窗口上界）", "0.42", "—", "不可测"],
    ],
    [Cm(3.8), Cm(2.8), Cm(3.6), Cm(2.4)])
para([("n", "盲区数值攻击现状收口：(i) 峰高口径——基线模型不确定度 ~2.35（B4 实测 mean 14.7475 vs 理论在线 ~12.4）把检测限卡在 δ~0.02–0.05；(ii) 配对二阶口径——δ²·O(1) 相对签名低于背景 1.5% 涨落（威胁级 σ≤0.42）——二阶盲。两条数值路线全部关闭：δ<0.05 数值侧封死。唯一开放路线是理论：现代零密度界压 δ*——只需优于 Ingham 约 6%（σ=0.55 处指数 0.931→0.872）即把 δ* 压过 0.05 线，盲区被无条件覆盖。")], indent=True)

# ---------- 8 ----------
h1("8　诚实边界与未决")
para([("n", "① 数值核 f̂ 是定理 3.1′ 的数值化身——紧支撑 f 的精确选择改变常数不改变 δ²·O(1) 结论（上界 4π²·⟨u²⟩_w≤9.9，最优 1.65 倍提升不足 3σ）。② 注入实验是差分口径（同一数据注入前后对比）——系统偏置被差掉，σ 是纯统计检测限（窗间涨落）；未覆盖「数据本身系统性离线」（R-S 求根伪影）——那需独立求根交叉验证。③ 未测端点集中型 f（u→1/2 型）：理论已给上界，σ~0.42·1.65≈0.7，不足。④ 盲区封死依赖 XXXIII 峰高模型误差限判定——若独立求根改进基线模型，峰高检测限可推到 δ~0.02 但不可达 0.05 以下。⑤ 未决：现代零密度界（Bourgain-Watt 型）在 σ=0.55 的适用性与常数——δ* 过 0.05 线的决定性查证点。")], indent=True)

# ---------- 9 ----------
h1("9　判定总结")
para([("n", "二阶口径数值定向完成并落档：配对和离线签名 δ²·p 双线性精确验证（平方律 ×4/×25/×100 偏差 <1%、p 线性偏差 ≤2%、方向恒负、每对系数与理论含 off−off 2δ 修正自洽至 ~2%），但检测力不足——威胁级 δ=0.05 的 σ 仅 0.31（同族）/0.18（跨族）/0.42（窗口上界），δ<0.05 完全不可测。机制定性：配对核沿实部方向二阶曲率受检验函数支撑限制为 O(1) 相对（⟨f̂″/f̂⟩~−6，上界 9.9），λ² 被 2π 归一化抵消——签名 δ²·O(1) 相对级。判定：配对和对 σ「二阶也盲」——与攻防 XXXII 一阶盲合并为「虚部统计口径对 σ 全阶盲」；二阶口径作为盲区攻击路线关闭。盲区 δ<0.05 数值侧封死（峰高模型误差限 + 配对二阶盲），θ_K≥7/8 等价式的剩余威胁只剩该盲区内的理论攻击；主线下一站：现代零密度界文献核实（压 δ* 过 0.05 线，6% 门槛）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XXXI：路2攻防XXXI-离线且简单目标定量-C₂^K严格域上界与入口C闭合判定.docx（入口 C 闭合：0.9768@λ₀=1.0、目标放宽至 0.1018·N_K≈21.9 万；本攻防的承接对象）.",
    "攻防 XXXII：路2攻防XXXII-入口A显式公式余项桥数值定向-离线且简单在虚部统计口径中的可见性判定.docx（入口 A 证伪；配对和/S_K(t)/Levinson ΣK² 对 σ 一阶盲）.",
    "攻防 XXXIII：路2攻防XXXIII-入口B密度剖面与威胁窗闭合-全区间峰高实测与盲区收缩判定.docx（入口 B 四件套；威胁窗 δ∈[0.05,0.0902] 数值闭合、唯一盲区 δ<0.05）.",
    "攻防 XII：路2攻防XII-跨族引理-BGST配对相关的zeta_K版本.docx（定理 3.1′：Σ_{ρζ,ρL} f̂(i(ρζ−ρL)λ/2π)·w=(T/2π)λ·(f(0)+O(1/√logT))，跨族配对结构）.",
    "攻防 XIII：路2攻防XIII（「每个离线简单零点的配对贡献偏离在线模型 δ²λ² 级」审计；任何并置须显式建桥）.",
    "攻防 XVI：路2攻防XVI（配对相关谱波动 ∫F_cross²/∫F_jit²=0.9927≈1，白噪声基线）.",
    "DAVENPORT H. Multiplicative Number Theory[M]. 3rd ed. New York: Springer, 2000（Montgomery 配对相关、检验函数框架）.",
    "数值数据：zeros_T6e5.npz（ζ 999492 根、L(χ₅) 1150050 根、T=6×10⁵）；entC_pair.json / entC_scan.json（本轮 C1/C1b/C1c，脚本 entC_pair.py / entC_scan.py 可复跑；核=f̂ of cos²(πx)·1_{|x|<1/2}，窗口 R=2.5 主实验）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
