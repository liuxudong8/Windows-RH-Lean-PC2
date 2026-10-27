# -*- coding: utf-8 -*-
"""生成《L4交叉项估计II-涨落符号定向与在线桥完整余项链.docx》（输出到 d1 目录）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\L4交叉项估计II-涨落符号定向与在线桥完整余项链.docx"
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

def make_table(headers, rows, widths):
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
            p.alignment = WD_ALIGN_PARAGRAPH.CENTER if j == 0 else WD_ALIGN_PARAGRAPH.LEFT
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
rich(tp, [("b", "L4 交叉项估计 II：涨落符号数值定向与在线桥完整余项链")], size=18, eastasia=HEI)
st = doc.add_paragraph(); st.alignment = WD_ALIGN_PARAGRAPH.CENTER
st.paragraph_format.space_after = Pt(6)
rich(st, [("n", "——《谱对偶论证》系列（d1）：L4 交叉项估计的数值推进与理论修正")], size=12, eastasia=KAI)
vr = doc.add_paragraph(); vr.alignment = WD_ALIGN_PARAGRAPH.CENTER
vr.paragraph_format.space_after = Pt(10)
rich(vr, [("n", "研究方案与部分进展（2026-10-19）：Δ<0 的 68σ 数值定向、条件 (D) 数值支持与 E[A(t)] 期望修正")], size=10.5, eastasia=KAI)
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
para([("n", "本文承接《L4 交叉项估计：S_ζL 的量级、主项与去相关条件》（2026-10-17），用 T=6×10⁵ 全量零点数据（ζ 999492＋L(χ₅) 1150050）对交叉项涨落 Δ=S_ζL−E 完成符号定向与去相关条件 (D) 的数值检验。"), ("b", "核心结果"), ("n", "：（i）Δ=−72956<0，Δ/N_K=−3.39%，相对 √N_L 为 68σ 级，三块贡献均匀（每零点 −0.060/−0.064/−0.066）——ζ 零点局部密度在 L(χ₅) 零点处系统性偏低，跨族离线互斥首次获得 68σ 级数值证据，方向与 L4 文档风险检查点 3 的期待一致；（ii）条件 (D) 数值支持：局部窗口密度 A(t) 方差 0.114 远小于均值 0.79（强亚泊松，零点刚性），自相关 C_ζ(h) 于 h≈0.5 转负、以 λ≈0.386 指数衰减，∫|C_ζ|dh≈0.034 有限——随机涨落部分可控制；（iii）"), ("b", "理论修正"), ("n", "：正确期望 E[A(t)]=log(t/2π)/ℓ（t∈(T/2,T] 时 0.76–0.86），L4 文档的 1+o(1) 含约 14% 常数误差（log(2π)/ℓ 项），逐点基准才是正确口径；（iv）但 Δ 实测超出 (D) 随机界约 19 倍——Δ 含系统性负偏置，非纯随机涨落，机制假设为 ζ 零点亚泊松刚性叠加 L 零点跨族避开。"), ("b", "在线桥完整余项链"), ("n", "：密度侧 8.1×10⁻⁶（攻防 XIX）＋配对侧 ∫dF≈−0.0094（攻防 XVII）＋交叉项 Δ/N_K=−3.39%（本文）⟹ 在线比例 ≥0.6725−O(10⁻⁵~10⁻³)；互斥量级约为攻防 XVIII 翻越门槛（−0.334）的 1/10——7/8 仍不可达，但跨族互斥作为 AI 单函数框架所没有的量首次被定量证实，是系列相对 AI 的真实增量点；Δ 进入在线比例 θ_K 的系数推导是下一步。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "交叉项涨落；跨族离线互斥；亚泊松；条件 (D)；在线比例；L4；数值定向")], indent=False)

# ---------- 1 ----------
h1("1　承接与数值设置")
h2("1.1　承接对象")
para([("n", "本篇承接三件既有工作：（i）L4 交叉项估计文档[1]修正第三篇骨架引理 L4 后，留下唯一卡点——涨落 Δ=S_ζL−E 的 o(N_K) 界（条件 (D)），并在风险检查点 3 明示“Δ 的符号未定：Δ<0 才携带离线互斥；需先数值/算术证据定向”；（ii）攻防 XVIII[2]判决常数层关闭（Q(0)≥1、并集下界恒非正 ≈−1/3），战场唯一开放 = L1/L4 在线比例桥，配对侧 f(0) 系数=1 已备；（iii）攻防 XIX[3]给出在线比例余项数值级 0.6725−O(10⁻⁵~10⁻³），并在第 5 节(3)②点名下一步为“L4 交叉项与本次密度余项合并，给出在线桥的完整余项链”。"), ("b", "本篇目标"), ("n", "：Δ 符号数值定向、条件 (D) 数值检验、E[A(t)] 理论修正、在线桥完整余项链合并。")], indent=True)
h2("1.2　数据与口径")
para([("n", "数据：zeros_T6e5.npz（ζ 零点 999492 个、L(χ₅) 零点 1150050 个，0<γ≤T，T=6×10⁵）。记号：ℓ=log T=13.3047；w(u)=4/(4+u²)；窗口 W=R/ℓ=1.5032（R=20，w(20)≈0.01 可忽略）。定义：")], indent=True)
formula([("n", "A(t) = Σ"), ("msub", "γ∈Z_ζ"), ("n", " w((γ−t)ℓ)，S_ζL = Σ"), ("msub", "γ′∈Z_L"), ("n", " A(γ′)，Δ = S_ζL − E，E = Σ"), ("msub", "γ′∈Z_L"), ("n", " log(γ′/2π)/ℓ。"), ], "1")
para([("n", "逐点期望基准 E[A(γ′)]=log(γ′/2π)/ℓ 采用 delta_calc.py 口径（第 4 节论证其为正确基准）。边界剔除：γ′∈[12, T−W]（n_use=1150045；低端 12 保 ζ 零点 14.13 左侧近邻完整、高端防窗口越界）。计算方式见附录 A。Δ 为差分口径（逐点减期望），对 L 数据 0.27% 的 R–S 求根系统伪影免疫（攻防 XIX[3] 第 4.2 节）。")], indent=True)

# ---------- 2 ----------
h1("2　涨落符号定向")
h2("2.1　主结果")
t1 = make_table(
    ["量", "数值", "说明"],
    [
        ["S_ζL", "839011.3", "跨族窗口和（窗口 W=1.5032）"],
        ["E（逐点期望）", "911967.8", "Σ log(γ′/2π)/ℓ"],
        ["Δ = S_ζL − E", "−72956.4", "涨落"],
        ["Δ/N_K", "−0.03394（−3.39%）", "N_K=2149542"],
        ["Δ/√N_L", "−68.03", "参考涨落 √N_L=1072.4"],
    ],
    [Cm(3.4), Cm(3.8), Cm(8.6)])
para([("n", "表 1　交叉项涨落主结果（T=6×10⁵）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("b", "判定：Δ<0 显著成立。"), ("n", "ζ 零点局部密度在 L(χ₅) 零点处系统性偏低——两族零点倾向互斥（L 零点落在 ζ 密度低处），与 L4 文档风险检查点 3 的期待方向一致。")], indent=True)
h2("2.2　分块稳定性")
t2 = make_table(
    ["块", "零点数", "S−E", "(S−E)/n"],
    [
        ["0（低 t）", "383349", "−22933.4", "−0.0598"],
        ["1（中 t）", "383348", "−24675.6", "−0.0644"],
        ["2（高 t）", "383348", "−25347.4", "−0.0661"],
    ],
    [Cm(2.6), Cm(2.6), Cm(4.0), Cm(4.6)])
para([("n", "表 2　分块贡献（L 零点按升序三等分）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("n", "三块每零点贡献 −0.060/−0.064/−0.066，均匀且无随 t 的趋势漂移——负偏置是整体性、系统性的，不来自端点或个别区域。")], indent=True)
h2("2.3　显著性：系统性负偏置")
para([("n", "若 Δ 为近似独立的零点涨落，其自然尺度为 √N_L≈1072，实测 |Δ|/√N_L=68.0——超出 68 个“σ”；即便按条件 (D) 下的随机界 √(N_L·ℓ)≈3912（第 3 节），实测 |Δ| 仍为其 18.7 倍。"), ("b", "结论：Δ 不是随机涨落，而是确定性负偏置 E[Δ]<0"), ("n", "——这是跨族排斥的结构内容，不是误差项。")], indent=True)
h2("2.4　与攻防 XVII 配对侧的口径对照")
para([("n", "攻防 XVII[4] 的配对侧读数 Δ_pair/N_K≈−0.7%（∫dF≈−0.0094，配对相关层）；本文密度层 Δ/N_K=−3.39%。两者方向一致（均负），量级差约 5 倍——同一互斥现象在“配对相关”与“局部窗口密度”两个口径下的不同读数，密度层信号更强且更直接（不需要配对窗参数化）。")], indent=True)

# ---------- 3 ----------
h1("3　条件 (D) 数值检验与亚泊松判定")
h2("3.1　自相关 C_ζ(h)")
t3 = make_table(
    ["h", "C_ζ(h)", "h", "C_ζ(h)"],
    [
        ["0.00", "0.11444", "1.50", "−0.00450"],
        ["0.25", "0.00950", "2.00", "−0.00329"],
        ["0.50", "−0.01724", "3.00", "−0.00162"],
        ["0.75", "−0.01235", "4.00", "−0.00110"],
        ["1.00", "−0.00719", "—", "—"],
    ],
    [Cm(2.4), Cm(3.6), Cm(2.4), Cm(3.6)])
para([("n", "表 3　ζ 零点局部密度 A(t) 的自相关（网格 Δt=0.25，t∈[T/2,T]）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("n", "C_ζ(0)=0.1144=var(A)；C_ζ(0.25)=0.0095（相对 C(0) 衰减 12 倍）；h≥0.5 后转为负相关（排斥性），绝对值缓降至 h=4 处 0.0011。")], indent=True)
h2("3.2　亚泊松判定：方差远小于均值")
para([("n", "mean(A)=0.7856、var(A)=0.1144——方差仅为均值的 0.146（泊松参考 Var=Mean）。"), ("b", "ζ 零点局部密度的波动被强抑制（亚泊松/零点刚性）"), ("n", "：这是零点间距排斥的直接读数，方向与 Montgomery 对相关猜想（零点排斥）一致[7]。")], indent=True)
h2("3.3　可积性与 (D) 的数值成立")
para([("n", "∫|C_ζ(h)|dh（0 至 4）≈0.0337 有限；尾部以 λ≈0.386 指数衰减（1/e 尺度 2.6 单位）。数值上 ∫_ℝ|C_ζ|dh<∞ 成立——"), ("b", "条件 (D) 得到数值支持"), ("n", "。在此条件下，随机涨落部分 Var(Δ)=O(N_L·∫C)≈1.15×10⁶×0.034≈3.9×10⁴，√≈198——比 L4 文档保守界 √(N_L·ℓ)≈3912 更紧。")], indent=True)
h2("3.4　随机部分与系统性偏置并存")
para([("n", "(D) 控制的是 Δ 的随机涨落部分（围绕其期望）；实测 |Δ|=72956 超出任何随机界——"), ("b", "Δ 的负偏置是系统性结构"), ("n", "。(D) 数值成立与系统性负偏并不矛盾：前者管方差，后者管期望 E[Δ]<0。L4 文档的框架需升级为“Δ = 系统性负偏置 + 随机涨落”，前者是本文的核心新对象。")], indent=True)

# ---------- 4 ----------
h1("4　理论修正与机制")
h2("4.1　E[A(t)] 修正")
para([("n", "ζ 零点的局部平均密度为 ρ(u)=(1/2π)log(u/2π)（Riemann–von Mangoldt 局部平均）。由 E[A(t)]=(ρ(t)/ℓ)·∫w(v)dv=ρ(t)·2π/ℓ，得")], indent=True)
formula([("n", "E[A(t)] = log(t/2π)/ℓ。"), ], "2")
para([("b", "修正 2。"), ("n", "L4 文档附录 A 的“代入 ρ(t)=ℓ/2π+O(1/T) 得 E[A(t)]=1+o(1)”不成立：ρ(t)=(1/2π)log(t/2π)≠ℓ/2π，两者相差 log(2π)/ℓ≈0.14 的常数。t∈(T/2,T] 时正确期望为 0.758–0.862，而非 1。数值 mean(A)=0.7856 与正确基准一致（t 在区间内分布）。逐点期望基准（delta_calc.py 口径，式（1））一直是正确的；L4 文档正文的 1+o(1) 是近似简写，本篇以式（2）为准。")], indent=True)
h2("4.2　Δ 的分解")
formula([("n", "Δ = ∫ (A(t) − log(t/2π)/ℓ) dN_L(t) = 系统性负偏置 + 随机涨落。"), ], "3")
para([("n", "(D)（第 3 节）控制随机部分；系统性负偏置 E[Δ]<0 为本文新对象。")], indent=True)
h2("4.3　机制假设")
para([("n", "系统性负偏的两个候选机制：（i）ζ 零点亚泊松刚性（3.2 节：var(A) 远小于 mean(A)——零点互相排斥压平密度波动，A(t) 在任意位置系统性低于泊松水平）；（ii）L 零点跨族避开 ζ 零点（并集刚性检验[5]：跨族最近间距分布与乘积函数零点交错统计）。两者均使“L 零点落在 ζ 零点局部密度低处”，叠加即得 Δ<0。")], indent=True)
h2("4.4　与攻防 XVI“近对角白噪声”的关系")
para([("n", "攻防 XVI 的“白噪声”判定在配对相关层（ΣK² 相对理论的偏差 ≈0）；本文 Δ 的密度层负偏是不同对象（A(t) 的均值结构沿 L 零点的积分），两者不矛盾。亚泊松 var(A)=0.114 本身呼应零点刚性，为后续把“互斥 Δ<0”翻译为 θ_K 增量的解析推导提供起点。")], indent=True)

# ---------- 5 ----------
h1("5　在线桥完整余项链")
h2("5.1　三项余项合并")
t4 = make_table(
    ["余项来源", "数值", "出处"],
    [
        ["密度侧（S_K 的 sup/RMS）", "≈8.1×10⁻⁶", "攻防 XIX[3]"],
        ["配对侧 ∫dF", "≈−0.0094（≈0）", "攻防 XVII[4]"],
        ["交叉项 Δ/N_K（本文）", "−0.0339", "本文（表 1）"],
        ["Levinson 余项综合", "0.6725−O(10⁻⁵~10⁻³)", "攻防 XVIII/XIX[2,3]"],
    ],
    [Cm(5.0), Cm(4.6), Cm(5.0)])
para([("n", "表 4　在线比例余项链（T=6×10⁵ 有限口径）"), ], indent=False, align="center", size=9, before=2, after=6)
para([("n", "密度侧与配对侧为 10⁻⁵~10⁻³ 级可忽略项；交叉项 Δ/N_K=−3.39% 是三项中唯一的同阶量（3×10⁻²），但它不是“余项损失”而是“互斥信号”——若其以正系数进入在线比例分子（L4 文档 6.3 的定性），则 θ_K 的常数额外增量量级为 O(3×10⁻²)。")], indent=True)
h2("5.2　互斥增量与翻越门槛")
para([("n", "攻防 XVIII[2] 给出翻越命题 2.1 负下界所需 2S_cross/N_K<−0.334（每 (T/2π)logT 单位）；本文实测 Δ/N_K=−0.034——量级约为门槛的 1/10。"), ("b", "判定：7/8 仍不可达"), ("n", "：常数层已封闭（XVIII），互斥虽真实存在但量级不足以翻越；在线比例上限仍是 0.6725 的量级（余项级 O(10⁻⁵~10⁻³) 不阻碍）。")], indent=True)
h2("5.3　真实增量点")
para([("n", "跨族离线互斥（Δ<0）是 AI 单函数框架（rank-trace＋Weil 压缩，作用域限于单个 ζ 或单个 L[8]）所没有的量：AI 处理 ζ_K 时只能取两族各自 2/3 的平庸并集，无法度量“L 零点避开 ζ 零点”的跨族结构。本文以 68σ 数值证据确认该结构存在（−3.39%）。"), ("b", "下一步"), ("n", "：推导 Δ 进入 θ_K 表达式的系数（把 −3.39% 翻译为 θ_K 的具体增量），并扫描多 T 确认 Δ/N_K 的收敛值（攻防 VIII 多 T 稳定性方法）。")], indent=True)

# ---------- 6 ----------
h1("6　风险检查点")
para([("n", "（1）Δ 的 T 依赖性未扫描：本文为单 T=6×10⁵；需多 T 稳定性验证（攻防 VIII 方法）确认 Δ/N_K 收敛值；"), ], indent=True)
para([("n", "（2）−3.39% 进入 θ_K 的系数未推导：需严格化 E[Δ]<0 的跨族显式公式/二阶矩理论（攻防 XVI 方向的延伸）；"), ], indent=True)
para([("n", "（3）C_ζ(h) 的 λ=0.386 为 h≤4 有限区间拟合，长尾行为未验证；"), ], indent=True)
para([("n", "（4）L 数据 0.27% R–S 求根伪影：Δ 为差分口径免疫，但 S_ζL 绝对值不可单独引用；"), ], indent=True)
para([("n", "（5）亚泊松 var(A)=0.114 的解析解释待建立（ζ 零点刚性⟷Montgomery 对相关猜想方向[7]）。"), ], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "刘旭东, 刘高源, 王芳, 刘晓春. L4 交叉项估计：S_ζL 的量级、主项与去相关条件[Z]. 2026-10-17.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XVIII：Q(0) 控制——mollifier 范数与并集下界恒非正判定[Z]. 2026-10-19.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XIX：并集素项净压制与显式公式余项数值级——L 主项修正[Z]. 2026-10-19.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 路②攻防 XVII：基线依赖调和——跨族排斥与聚集的成立范围[Z]. 2026-10-19.",
    "刘旭东, 刘高源, 王芳, 刘晓春. 并集刚性检验：乘积函数零点交错与 ζ_K 零点并集统计[Z]. 2026-10-17.",
    "LAMZOURI Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line[EB/OL]. arXiv:2609.02882, 2026. https://arxiv.org/html/2609.02882v1.",
    "MONTGOMERY H L. Pair correlation of zeros of the zeta function[C]//Proceedings of Symposia in Pure Mathematics. Providence: AMS, 1973, 24: 181–193. https://websites.umich.edu/~hlm/paircor1.pdf.",
    "ALPÖGE L, FURMAN R. More than two thirds of the zeta zeros are simple and on the critical line[EB/OL]. arXiv:2608.13637v2, 2026. https://arxiv.org/abs/2608.13637.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

# ---------- 附录 ----------
h1("附录 A　计算细节")
para([("n", "窗口和：A(t)=Σ_{|γ−t|≤W}4/(4+((γ−t)ℓ)²)，W=R/ℓ=1.5032；对每个 γ′∈Z_L 用 numpy.searchsorted 定位 [γ′−W, γ′+W] 内的 ζ 零点并求和。逐点期望：E=Σ_{γ′∈Z_L}log(γ′/2π)/ℓ。边界剔除：γ′∈[12, T−W]（n_use=1150045；低端 12 保 ζ 零点 14.13 左侧近邻完整，高端防窗口越界）。分块：L 零点按升序三等分，逐块计算 S−E 与 (S−E)/n。自相关：均匀网格 t∈[T/2+10, T−10]、Δt=0.25，A 序列滞后 h=k·Δt 计算 C_ζ(h)=(1/N)Σ(A_t−mean)(A_{t+h}−mean)；∫|C|dh 取 h∈{0,0.25,0.5,0.75,1,1.5,2,3,4} 梯形积分。全部计算见 l4_next_num.py / l4_next_num.json。")], indent=True)

doc.save(OUT)
print("SAVED:", OUT)
