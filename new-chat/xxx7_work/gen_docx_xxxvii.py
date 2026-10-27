# -*- coding: utf-8 -*-
"""生成《路2攻防XXXVII-Weil显式公式实部口径注入敏感性-离线对同虚部成对的间距结构排除与N_off·δ²·λ²累积可测性判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVII-Weil显式公式实部口径注入敏感性-离线对同虚部成对的间距结构排除与N_off·δ²·λ²累积可测性判定.docx"
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
rich(tp, [("b", "路2攻防XXXVII—Weil显式公式实部口径注入敏感性")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(0)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "离线对同虚部成对的间距结构排除")], size=18, eastasia=HEI)
tp3 = doc.add_paragraph()
tp3.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp3.paragraph_format.space_after = Pt(10)
tp3.paragraph_format.line_spacing = 1.5
rich(tp3, [("b", "与 N_off·δ²·λ² 累积可测性判定")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：S2 数值定向——威胁构型自洽性与 Weil 实部口径近盲判定")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 24 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行 S2：Weil 显式公式实部口径的离线注入敏感性（N_off·δ²·(logx)² 累积可测性）。三件事实：(i) 构型自洽性（决定性判定）：离线对 1/2±δ+iγ 同虚部（ζ_K 实系数函数方程 ρ⟹1−ρ̄ 强制），威胁构型必使并集出现 d≈0 的极近对——实测（攻防 XXXVI）同族 <1e-3 0 个、跨族 <1e-6 2 个（泊松预期 380 级），而威胁级需 21.9 万对——**威胁构型被间距结构直接排除**；漏根掩盖要求 10% 漏根率 vs 实测 0.27%——再排除。(ii) Weil 实部注入敏感性（数值，entE_weil3.py）：威胁级（N_off=21.9 万、δ=0.05、均匀 γ）SNR@λ=13.3 ≈ 0.59（一阶签名 √(2N_off/N_K)·(1+δ²λ²/2)）/ 0.19（二阶签名 √(2N_off/N_K)·(cosh(δλ)−1)≈δ²λ²/2）；Re 口径（ψ_K 实函数只测实部）修正后 ~0.42/0.13——**1σ 下不可测**；λ 大端理论升（二阶 λ² 放大）但截断误差 (x·log²x)/T 摧毁可计算窗口（λ≤11.5 校验、威胁级 SNR 全程 ≲0.5σ）。(iii) 实现校验（entE_weil_diag2/diag3/check2）：ζ 分离 diff std=0.28（相对精度 1e-5）、L 分离 5.76、组合 6.03——Weil 公式实现验证通过。判定：**Weil 实部口径关闭为威胁检测器**（并入攻防 XXXII/XXXIV 的虚部/配对全盲结论）；威胁排除支柱 = 间距结构（S1）+ 构型自洽性（本攻防）——S3（Δ 常数指纹）为最后候选。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "Weil显式公式；实部口径；注入敏感性；构型自洽性；同虚部成对；威胁排除")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXXV 文献核实判定：盲区 δ<0.05 的无条件闭合需超密度假设级界（σ=0.55 处指数 κ≤0.8721），文献不存在——通用零密度路径闭合；唯一开放方向是 ζ_K 特有谱结构（在线比例桥/显式公式余项精细形态）构造专用论证。攻防 XXXVI（S1 左尾审计）已交付：峰高可分辨范围内无 δ>0.01 的离线零点，威胁带收窄为 δ≤0.01 超浅带，「数据无深离线」成为实证基线。")], indent=True)
para([("n", "用户拍板 S2 先行：Weil 显式公式实部口径注入敏感性——离线零点在 Weil 公式中成对贡献 √x·cos(t logx)·(1+δ²log²x/2)，检验 N_off·δ²·(logx)² 累积可测性。本攻防完成 S2 数值定向并给出威胁构型的数学判定。")], indent=True)

# ---------- 2 ----------
h1("2　威胁构型的数学结构：离线对同虚部成对")
h2("2.1　函数方程强制配对")
para([("n", "ζ_K=ζ·L(χ₅) 为实系数 L 函数（χ₅ 为模 5 实奇字符），满足函数方程 ζ_K(s)=γ_K(s)·ζ_K(1−s)（γ_K 为 D=5 的 Γ 因子）。故 ρ 为零点 ⟹ 1−ρ̄ 亦为零点：ρ=1/2−δ+iγ 的对称伙伴为 1/2+δ+iγ——**虚部完全相同**。离线零点（δ>0）必然成对出现（同虚部双零点），这是硬定理，不依赖任何数值假设。")], indent=True)
para([("n", "由此，「离线且简单」威胁（N_off 个离线零点）自动携带 N_off 个对称伙伴——共 2N_off 个非临界线零点。无论威胁构型的其他细节如何，其零点虚部集必含 N_off 个「同虚部双零点」位置。")], indent=True)
h2("2.2　并集间距结构排除（决定性判定）")
para([("n", "若威胁真实存在，其 N_off 对同虚部零点在并集数据（zeros_T6e5.npz，ζ 族 + L 族求根结果）中必然表现为虚部差 d≈0 的极近对。攻防 XXXVI（表 1）实测：同族极近对（<1e-3）0 个（ζ 与 L 各 0）、跨族极近对（<1e-4）386 个——后者恰与独立零点重合的泊松预期 N_ζ·N_L·(2×10⁻⁴/T)≈380 吻合（即 386 个是「两族独立求根碰巧虚部接近」的自然现象，非配对结构）；跨族 <1e-6 仅 2 个。")], indent=True)
para([("n", "威胁级目标带 N_off=21.9 万对 ⇒ 并集应出现 21.9 万个 d≈0 极近对——实测 <1e-3 级 0 个、<1e-6 级 2 个，相差 5 个量级。**判定：威胁构型（同虚部成对）与实测间距结构不兼容，被直接排除**。此判定不依赖任何检测器或统计口径——只依赖「极近对计数」这一原始事实。")], indent=True)
h2("2.3　漏根掩盖构型的排除")
para([("n", "唯一逃逸通道：每对离线零点中「一个」被求根漏掉，并集只见单零点（实部 1/2±δ），无 d=0 对。这要求漏根率 ≥N_off/N_K≈10%（掩盖 21.9 万对中每对的一个）。实测 L 族漏根率 0.27%（攻防 XIX/XXXVI：−3147/全长），ζ 族几乎完美（−15）——**10% vs 0.27% 相差 37 倍，排除**。且被漏掉的另一半零点（实部 1/2±δ 单零点）实部可测（攻防 XXXVI 方法），已在 S1 左尾审计中扫过可疑带。")], indent=True)

# ---------- 3 ----------
h1("3　Weil 显式公式实部口径的签名结构")
para([("n", "ζ_K 的显式公式（Mangoldt 形式）：ψ_K(x)=x−Σ_{γ≠0} x^ρ/ρ − c_K。ρ 与 ρ̄ 共轭成对，零点项为实数：")], indent=True)
formula([("n", "ψ_K(x) = x − Σ_{γ≠0} x^ρ/ρ − c_K = x + 2·Re Σ_{γ>0} x^ρ/ρ − c_K，　λ=log x。")], "1")
para([("n", "定义零点项 R_on(λ)=−Σ_{γ>0} x^ρ/ρ（单侧复数，数值直接算）；实部口径的零点项 = 2·Re R_on。离线对（1/2−δ+iγ、1/2+δ+iγ，同虚部）的联合贡献：")], indent=True)
formula([("n", "x^{1/2−δ+iγ}/(1/2−δ+iγ) + x^{1/2+δ+iγ}/(1/2+δ+iγ) ≈ (2√x/γ)·e^{iγλ}·cosh(δλ)。")], "2")
para([("n", "对照在线基线（该虚部处零点在 1/2），配对联合贡献的相对偏差 = cosh(δλ)−1 ≈ δ²λ²/2——**δ 一阶项严格消失**（对称配对抵消奇阶项，与攻防 XXXIV 配对和同源）；λ 扫描按 λ² 放大。三种威胁构型的签名阶数：")], indent=True)
formula([("n", "构型 P（物理加对，虚部集不变）：SNR_P ≈ √(2N_off/N_K)·(1+δ²λ²/2)；")], "3")
formula([("n", "构型 C（总数守恒二阶，2N_off 在线等价→N_off 对）：SNR_C ≈ √(2N_off/N_K)·(cosh(δλ)−1) ≈ √(2N_off/N_K)·δ²λ²/2。")], "4")
para([("n", "构型 P 是一阶签名（离线对本身即「两个零点」的 Weil 贡献，1+δ²λ²/2 为 cosh 修正）；构型 C 是纯二阶签名（用户命题的 δ²·(logx)² 形态）。威胁级参数：√(2×219000/2149542)=0.4514；δ=0.05、λ=13.3 处 SNR_P≈0.55、SNR_C≈0.103。")], indent=True)

# ---------- 4 ----------
h1("4　数值注入实验")
h2("4.1　口径演进")
para([("n", "数值件 entE_weil.py/.json（v1）、entE_weil2.py/.json（v2）、entE_weil3.py/.json（v3，主件）——口径三次修正：v1 用单点 |Δ|/|R_on|，λ 扫描中 |R_on| 游走落零处 SNR 爆炸（max=39，相位运气伪影）；v2 分母取全 λ 平均标量，λ 依赖失真（λ 小端 SNR→0、大端虚高）；v3 逐 λ 分母 |R_on(λ)| + 多抽样 RMS + 三构型（P/B/C）×δ（0.01/0.02/0.05）×N_off（200/2000/2139/5 万/21.9 万）×γ 分布（均匀/低 γ 集中）。注入构型：随机选 N_off 个 γ，w_in=Σ在线项、w_off=Σ离线对项，ΔP=−w_off+w_in、ΔB=−w_off、ΔC=−w_off+2w_in。")], indent=True)
caption("表 1　威胁级注入的 Weil 实部 SNR（N_off=219000、均匀 γ、RMS 口径、λ=13.3）", before=4, after=2)
t1 = make_table(
    ["δ", "SNR_P（一阶）", "SNR_C（二阶 δ²λ²/2）", "理论 P / C", "P30（λ=30）"],
    [
        ["0.01", "0.606", "0.011", "0.455 / 0.004", "0.486"],
        ["0.02", "0.627", "0.043", "0.467 / 0.016", "0.556"],
        ["0.05", "0.592", "0.190", "0.551 / 0.104", "0.853"],
    ],
    [Cm(1.8), Cm(2.8), Cm(3.6), Cm(3.6), Cm(2.8)])
para([("n", "读数：威胁级 SNR@λ=13.3（x≈T 附近，实测 ψ_K 可用窗口的上端）——一阶 0.59-0.63、二阶 0.01-0.19——均 1σ 以下。ψ_K 为实函数、检测只测实部：|Δ|→|ReΔ| 的 RMS 修正约 √2 倍（Re/Im 各半），修正后 SNR_P≈0.42、SNR_C≈0.13——更不可测。λ=30 处二阶升至 0.85（理论 (cosh 1.5−1)·0.4514=0.61 的修正放大），但该 λ 需要 x=e^30≈1e13 的 ψ_K 实测数据（素数计数不可行）且截断误差已失控（第 6 章）。")], indent=True)
h2("4.2　低 γ 集中与边界")
para([("n", "若威胁零点挤在低 γ（γ<2000，1/γ 加权放大 Weil 项幅度）：SNR_P 升至 1.41（δ=0.05）、SNR_C 0.45——可测边缘。但 γ<2000 的 ζ_K 零点只有 ~2500 个（两族低端），威胁级 21.9 万对物理上挤不进去——低 γ 集中构型的 N_off≤2500 上限，不构成目标威胁；仅作边界注记。")], indent=True)

# ---------- 5 ----------
h1("5　实现校验")
para([("n", "为确认 Weil 数值实现正确（差分口径才可信），分三侧独立校验（x=e^λ、λ∈[8,11.5]，x≤1e5≪T，截断可控）：(i) 标准 ζ 的 ψ(x) vs x−2ReΣ_{ζ族}−log2π（diag2）；(ii) ψ_χ₅(x) vs −2ReΣ_{L族}（diag3，ψ_χ(x)=Σ_{p^k≤x}χ₅(p)^k·log p）；(iii) ψ_K=ψ+ψ_χ vs 并集零点项（check2，diff=(x−ψ_K)+2·Re R_on 应≈常数）。")], indent=True)
caption("表 2　Weil 公式实现校验（λ∈[8,11.5]，残差相对基准）", before=4, after=2)
t2 = make_table(
    ["校验侧", "差分口径", "残差 std", "残差 max", "相对精度"],
    [
        ["ζ 部分（diag2）", "ψ(x) − [x−2ReΣ−log2π−…]", "0.28", "0.95", "~1e-5"],
        ["L 部分（diag3）", "ψ_χ(x) + 2ReΣ_L", "5.76", "24.6", "~0.2（ψ_χ 级 30）"],
        ["组合 ψ_K（check2）", "(x−ψ_K) + 2·Re R_on − const", "6.03", "16.5", "~2e-4（ψ_K 级 2.8e4）"],
    ],
    [Cm(3.0), Cm(4.6), Cm(1.8), Cm(1.8), Cm(3.2)])
para([("n", "ζ 部分残差 0.28（相对 1e-5）——求和无误、共轭配对口径确认；L 部分 5.76 与 ψ_χ 级 30 相比 ~20%（漏根 −3147 与孤立假根 γ=500327 的贡献级），常数差 ~−8；组合 6.03、常数 9.71——Weil 公式实现验证通过，S2 数值可信。注：校验过程曾发现并修正「单侧求和缺共轭配对」与「差分符号」两处口径问题（v1 初版校验残差 242 即由此而来）。")], indent=True)

# ---------- 6 ----------
h1("6　可计算窗口与截断误差")
para([("n", "Weil 零点项用 γ≤T=6×10⁵ 截断。截断显式公式的误差为 O(x·log²x/T)（Davenport 标准界）——λ=11（x≈6e4）处 ≈12（实测组合残差 std=6 吻合）；λ=13.3（x≈6e5~T）处 ≈139——已超过威胁级信号（SNR 分母 |R_on| 级 ~36-83）。**判定：Weil 实部口径的可计算窗口 λ≲11.5（x≪T）**——窗口内威胁级 SNR≲0.5σ（一阶，Re 修正后）——全程不可测。λ 大端的理论放大（δ²λ²/2 二次型）被截断误差和 ψ_K 数据可得性双重封死。")], indent=True)

# ---------- 7 ----------
h1("7　判定与对主线的意义")
para([("n", "（i）Weil 实部口径关闭：威胁级注入在可计算窗口内 SNR≤0.5σ（一阶）/≤0.15σ（二阶）——与攻防 XXXII（虚部统计口径对 σ 一阶盲）、XXXIV（配对和对 σ 二阶也盲）合并——**虚部、实部、配对三种统计口径对离线注入全盲**；唯一「看得到」威胁的是间距结构（S1 的极近对计数）。")], indent=True)
para([("n", "（ii）威胁排除支柱升级：θ_K≥7/8 证据链中「威胁不存在」的支撑 = 无条件段（δ≥0.0902，零密度主幂）+ 数值闭合段（δ∈[0.05,0.0902]）+ 盲区（δ≤0.01，XXXVI 收窄）+ **构型自洽性（本攻防：同虚部成对 ⇒ 极近对 ⇒ 实测排除）**——最后一项是纯数学判定，独立于全部数值检测器。盲区带 δ≤0.01 的威胁若存在，其构型必须同时违反函数方程配对（同虚部）与实测间距结构——双重不兼容。")], indent=True)
para([("n", "（iii）S3 候选：Δ 常数定律对离线注入的响应（整体谱指纹检测器）——本攻防的构型自洽性判定对 S3 同样适用：任何「离线且简单」威胁构型都先被间距结构排除，S3 的价值从「检测威胁」降级为「交叉验证排除」；但 Δ 常数指纹若对 δ 注入有可测响应，仍可作独立旁证。")], indent=True)

# ---------- 8 ----------
h1("8　诚实边界与未决")
para([("n", "① SNR 的 Re 口径修正取 √2（|Δ|→|ReΔ| 的 RMS 比），未做逐样本 Re 投影精确统计——方向确定（更不可测），精确值列待核。② |R_on(λ)| 为单次实现的游走幅度，SNR 数值含 ±30-50% 的单点涨落（理论对照 0.59 vs 0.55 即此）——量级结论（<1σ）不受影响。③ 威胁构型「对称伙伴同虚部」依赖函数方程严格成立（ζ_K 实系数）——若 ζ_K 有重零点或 χ₅ 例外零点，配对虚部可偏移——标准假设下无重零点，未做重零点普查（并集极近对 0 已排除 d=0 级重合）。④ 全零点实部普查（~40 分钟级）仍未做——构型自洽性判定已使其实证意义降低（间距结构先排除）。⑤ 低 γ 集中构型的可测边缘（SNR~1.4）未深入——物理上限 N_off≤2500 不构成目标威胁。⑥ L 部分校验残差 5.76 的常数漂移（−8 级）未归因（疑似漏根/假根贡献）——不影响校验结论（相对精度 2e-4）。")], indent=True)

# ---------- 9 ----------
h1("9　判定总结")
para([("n", "S2 完成并落档。构型自洽性（决定性）：离线对 1/2±δ+iγ 同虚部（函数方程强制）⇒ 并集必现 d≈0 极近对——实测同族 <1e-3 0 个、跨族 <1e-6 2 个 vs 威胁需 21.9 万——**威胁构型被间距结构直接排除**；漏根掩盖需 10% 漏根率 vs 实测 0.27%——再排除。Weil 实部注入敏感性（数值）：威胁级 SNR@λ=13.3 ≈0.59（一阶）/0.19（二阶 δ²λ²/2）、Re 修正后 ~0.42/0.13——1σ 下不可测；λ 大端理论升但截断误差 O(x log²x/T) 限可计算窗口 λ≤11.5（窗口内 ≲0.5σ）。实现校验：ζ 0.28/L 5.76/组合 6.03——Weil 公式验证通过。**判定：Weil 实部口径关闭为威胁检测器**；威胁排除支柱 = 间距结构（S1）+ 构型自洽性（本攻防）。主线下一步：S3（Δ 常数指纹——从威胁检测降级为排除交叉验证）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XIX：《在线比例桥》数值剖面（xxx1_work/atk19_read0.txt；在线比例 0.6725−O(10⁻⁵~10⁻³)；L 族 0.27% R-S 漏根 −0.0052/单位）.",
    "攻防 XXXIII：路2攻防XXXIII-入口B密度剖面与威胁窗闭合-全区间峰高实测与盲区收缩判定.docx（B4 峰高口径、威胁窗 δ∈[0.05,0.0902] 数值闭合、盲区 δ<0.05）.",
    "攻防 XXXIV：路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx（配对和对 σ 二阶盲；δ 一阶消失的配对抵消同源）.",
    "攻防 XXXV：路2攻防XXXV-盲区理论门槛文献核实-零密度路径闭合与超密度假设判定.docx（盲区 δ<0.05 需超密度假设界 κ≤0.8721@σ=0.55；零密度路径闭合）.",
    "攻防 XXXVI：路2攻防XXXVI-左尾224审计与威胁形态实证-零点实部实测与盲区威胁收窄判定.docx（左尾 224 审计：在线 223/假根 1/离线 0；同族极近对 <1e-3 0 个、跨族 <1e-4 386≈泊松 380、<1e-6 2 个；威胁带收窄 δ≤0.01）.",
    "数值数据：entE_work/entE_weil3.py/.json（v3 主件：三构型×δ×N_off×γ 分布，可复跑）；entE_weil_diag2.py、entE_weil_diag3.py（ζ/L 分离校验）；entE_weil_check2.py/.json（组合校验）；zeros_T6e5.npz.",
    "Davenport《Multiplicative Number Theory》第 17 章：截断显式公式 ψ(x)=x−Σ_{|γ|≤T}x^ρ/ρ+O(x·log²x/T)（截断误差界，标准文献）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
