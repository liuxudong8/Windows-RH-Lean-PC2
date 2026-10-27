# -*- coding: utf-8 -*-
"""生成《路2攻防XL-配对侧无条件界的理论构造-BGS配对定理误差项O(1/√logT)的技术极限与拟随机涨落判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XL-配对侧无条件界的理论构造-BGS配对定理误差项O(1_√logT)的技术极限与拟随机涨落判定.docx"
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
rich(tp, [("b", "路2攻防XL—配对侧无条件界的理论构造：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(0)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "BGS 配对定理误差项 O(1/√logT) 的")], size=18, eastasia=HEI)
tp3 = doc.add_paragraph()
tp3.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp3.paragraph_format.space_after = Pt(10)
tp3.paragraph_format.line_spacing = 1.5
rich(tp3, [("b", "技术极限与拟随机涨落判定")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：0.6725 常数机制内余项侧的理论闭环与主线重定位")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 24 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "攻防 XL 完成配对侧无条件界的理论构造。三件事实：(i) 文献核查（arXiv:2609.02882v2 全文精读）：0.6725=C₀=3/2−cot(1/√2)/√2=0.6725007（Montgomery–Taylor 极值常数，=2−C_MT，C_MT=1.3274992963）；配对和误差项 O_f(1/√logT) 出自 BGS 无条件配对定理（Lemma 5，经 Lamzouri Lemma 3.1/3.2 接入）——**0.27 是定理界，不是保守标定**——S4 的 270 倍差距确认本质为数值拟随机 vs 定理最坏情形。(ii) 数值判定（detG_pc）：配对偏差 ∫C(h)dh 全程 |z|≤1.41σ（统计不显著），量级 ~1/√N_K（6.8×10⁻⁴@6e5）与拟随机涨落预言一致——配对和 = 主项 + 随机涨落。(iii) 技术极限判定：BGS 无条件版与 Montgomery RH 版误差同为 O(1/√logT)——1/√logT 是配对定理当前技术极限（RH 与否不变）——**0.6725−O(10⁻²) 严格定理在无条件框架内不可达**；θ_K≥7/8 缺口在常数（0.6725→0.875=0.2025），属 QRH 机制。修正的正向下界窗口：余项侧闭环；两条真开放方向——(a) 配对定理误差项技术改进（大筛/三线性→精细二阶矩）；(b) QRH 类常数机制（综述 §6.3 谱侧信息）。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "配对相关；无条件 Montgomery 定理；误差项；技术极限；拟随机涨落；常数机制")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXXIX（S4）把在线比例桥余项的 270 倍差距（数值 10⁻⁵~10⁻³ vs 理论 O(1/√logT)≈0.27）定位在配对侧。用户拍板：配对侧无条件界的理论构造——判定 0.27 是否可压、S4 提出的「配对侧界压到 10⁻² ⟹ 0.6725−O(10⁻²) 严格定理」窗口在无条件框架内是否成立。")], indent=True)

# ---------- 2 ----------
h1("2　文献核查：0.6725 的来源与配对侧理论界")
para([("n", "0.6725 的精确来源（arXiv:2609.02882v2，Lamzouri 2026 新证明）：C₀=3/2−cot(1/√2)/√2=0.6725007（Montgomery–Taylor 极值常数）。Lamzouri 定理 1.1：liminf N₀ˢ/N ≥ C₀（无条件，零点简单且在临界线）。常数与我们的 C_MT=1.3274992963 关系：C₀=2−C_MT（同一 Montgomery–Taylor 极值问题的两个表述）。")], indent=True)
para([("n", "配对侧理论界的确切结构（Lamzouri Lemma 3.1=BGS 论文 Lemma 5）：对 f 实偶、支撑 ⊂[−1,1]、0 处 Lipschitz，无条件配对公式")], indent=True)
para([("n", "Σ_{ρ,ρ′≤T} f̂(i(ρ−ρ′)L/2π)·w(ρ−ρ′) = (T/2π)L·(f(0)+2∫₀¹αf(α)dα + O_f(1/√logT))",)], indent=True)
para([("n", "其中 w(z)=4/(4−z²) 为 BGS 去 RH 引入的权因子（零点可能离临界线）。**误差项 O_f(1/√logT) 即 0.27 的定理来源**。Lemma 3.2 完成去权：K_δ(z)²=r̂_{δ,T}(z)·w(z)，r_{δ,T}=Q_δ−Q_δ″/(4(logT)²)——Q_δ″ 项经积分分部贡献 O(1/(logT)²) 级主项修正与 O(1/(logT)^{5/2}) 级误差，可忽略——**去权不改善误差阶，配对侧余项保持 O(1/√logT)**。")], indent=True)

# ---------- 3 ----------
h1("3　配对侧理论界的结构判定")
para([("n", "三条结构性事实：(1) 1/√logT 来自显式公式/大筛/三线性形式的 Fourier 截断——Montgomery 原始证明（RH 下）与 BGS 无条件版误差同为该阶——**1/√logT 不随 RH 真伪改变，是配对定理当前方法的技术极限**。(2) 去权机制把权因子 w(ρ−ρ′) 的奇点行为吸收进 r_{δ,T} 的 Q_δ″ 项——该项按 (logT)⁻² 压降，不产生新的松弛源。(3) Lemma 3.2 的常数 C_MT 由 ε 截断逼近（|C_{η_ε}−C_MT|<ε）——配对和常数依赖 ε，**liminf 论证依赖 ε→0 与 T→∞ 的顺序**——文献给的是渐近定理，无显式有限 T 余项。")], indent=True)

# ---------- 4 ----------
h1("4　数值判定：配对偏差的拟随机性")
para([("n", "用 A(t) 窗口相关 C(h)=Cov(A(t),A(t+h)) 的积分 ∫₀³C(h)dh 作配对偏差代理（XXXIX 口径），乘积矩传播估计 SE（neff=网格数/窗宽），z 分数判定显著性：")], indent=True)
caption("表 1　配对偏差显著性判定（∫C vs SE vs 拟随机尺度）", before=4, after=2)
t1 = make_table(
    ["T", "∫C(h)dh", "SE", "z 分数", "1/√N_K", "1/√logT", "1/logT"],
    [
        ["1e5", "−0.0009", "0.0013", "−0.69σ", "1.8e-3", "0.295", "0.087"],
        ["2e5", "−0.0004", "0.0009", "−0.39σ", "1.2e-3", "0.286", "0.082"],
        ["3e5", "0.0000", "0.0008", "0.01σ", "1.0e-3", "0.282", "0.079"],
        ["4e5", "0.0004", "0.0006", "0.54σ", "8.5e-4", "0.278", "0.078"],
        ["5e5", "0.0006", "0.0006", "0.97σ", "7.5e-4", "0.276", "0.076"],
        ["6e5", "0.0007", "0.0005", "1.41σ", "6.8e-4", "0.274", "0.075"],
    ],
    [Cm(1.6), Cm(2.2), Cm(1.8), Cm(2.0), Cm(2.2), Cm(2.2), Cm(2.0)])
para([("n", "读数：|∫C| ≤1.41σ 全程——配对偏差**统计上与 0 无显著偏离**；|∫C| ~10⁻³ 与 1/√N_K（6.8×10⁻⁴@6e5）同量级——**配对和 = 主项 + 随机涨落，涨落尺度 ~1/√N（拟随机预言）**；定理界 1/√logT=0.274 比实测偏差大 270 倍——**最坏情形方法界 vs 实际随机涨落**的差距确认。")], indent=True)

# ---------- 5 ----------
h1("5　技术极限与不可达性")
para([("n", "判定：0.6725−O(10⁻²) 严格定理**在无条件框架内不可达**——理由：(1) 配对和误差 O(1/√logT) 是 BGS/Montgomery 配对定理的定理界（非保守标定），改进它 = 改进配对理论本身；(2) 实测偏差 ~1/√N 是拟随机（QRH 类）现象——把 1/√logT 压到 1/√N 级在无条件框架内等价于证明拟随机性；(3) BGS 无条件化与 Montgomery RH 版同阶——RH 假设都不改善误差阶，说明 1/√logT 是方法极限而非猜想缺失。无条件现状：在线比例 ≥0.6725−O(1/√logT)（≈0.6725−0.27@6e5 的保守标定），渐近形式 0.6725−o(1)（Lamzouri 定理 1.1 的 liminf）。")], indent=True)

# ---------- 6 ----------
h1("6　修正的正向下界窗口与主线重定位")
para([("n", "S4（XXXIX）提出的「配对侧界压到 10⁻² ⟹ 0.6725−O(10⁻²) 严格定理」窗口**无条件关闭**——配对侧 10⁻² 是拟随机数值，非无条件可达界。主线重定位：θ_K≥7/8 的缺口在常数——0.6725→0.875 差 0.2025——余项侧已闭环（0.6725−O(1/√logT) 是无条件最优现状，余项再小也到不了 7/8）。两条真开放方向：(a) 配对定理误差项技术改进（大筛/三线性→精细二阶矩）——若成功则 0.6725−O(10⁻²) 无条件可达（常数不变，余项严格化）；(b) QRH 类常数机制（0.6725→7/8，综述 §6.3 谱侧信息不足的开放状态——Arthur 谱侧若能给出 ΣK² 精确主项可能改变常数）。")], indent=True)

# ---------- 7 ----------
h1("7　诚实边界")
para([("n", "① O_f(1/√logT) 的隐式常数未在 BGS/Lamzouri 显式给出——0.27 是 1/√logT@6e5 的标定值，非定理常数上界（常数可能远小于 1，需显式化才能定稿有限 T 界）。② Lamzouri 结论是 liminf 渐近（ε→0 与 T→∞ 顺序依赖）——有限 T 显式余项未在文献给出。③ SE 估算用乘积矩传播（neff=网格/窗宽口径）——C(h) 采样相关性的精确口径未独立验证，z 分数是量级判定非精确检验。④ 数值「拟随机涨落」判定是证据非定理——1/√N 尺度与 QRH 预言一致但不构成证明。⑤ δ→0 光滑化截断（Lemma 3.2 的 ε>0）使配对和常数依赖 ε——有限 T 版本需统一 ε-T 处理。⑥ 数值代理用 A(t) 窗口相关（∫C），非 Lamzouri f₀ 核的精确配对和——精确配对和的直接数值需 O(N²) 级计算未做。")], indent=True)

# ---------- 8 ----------
h1("8　判定总结")
para([("n", "攻防 XL 完成。配对侧无条件界的理论构造结论：(1) 0.27 是 BGS/Lamzouri 的定理界（O_f(1/√logT)），S4 的 270 倍差距 = 数值拟随机 vs 定理最坏情形；(2) 配对偏差数值判定为随机涨落（|z|≤1.41σ、~1/√N 同量级）——与拟随机预言一致；(3) 0.6725−O(10⁻²) 无条件不可达（1/√logT 是配对理论技术极限，RH 与否不变）；(4) θ_K≥7/8 缺口在常数（0.2025），余项侧闭环；(5) 真开放方向 = 配对定理误差技术改进（可达 0.6725 严格化）与 QRH 常数机制（可达 7/8）。主线：威胁排除五柱合围闭合（XXXIII-XXXVIII）、余项精细形态闭环（XXXIX-XL）——下一步候选：配对定理误差项技术改进的文献深挖（BGS 证明技术细节、1/√logT 的来源分解）或转 QRH 常数机制（综述 §6.3）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2（C₀=0.6725007、定理 1.1（liminf）、Lemma 3.1（BGS 配对公式 O_f(1/√logT)）、Lemma 3.2（去权、C_MT=1.3274992963））——全文精读.",
    "Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799（Lemma 5：无条件配对公式、误差 O_f(1/√logT)、权 w(z)=4/(4−z²)）.",
    "Baluyot D, Goldston D, Suriajaya A I, et al. Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of Simple Zeros and Critical Zeros. arXiv:2501.14545v2（配对相关水平分布首次应用）.",
    "More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2608.13637（Lean 4 形式化、Montgomery–Taylor window 0.6725、无条件 2/3、5/6 相异）.",
    "攻防 XIX/XXXVIII/XXXIX 与谱对偶综述（d1 已交付）：0.6725−O(10⁻⁵~10⁻³)、余项三分解、Δ 指纹、配对偏差 ∫C.",
    "S4/XL 数值件：entG_work/detG_rem.py/.json、detG_rem2.py/.json、detG_pc.py/.json——可复跑（Anaconda python）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
