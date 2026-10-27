# -*- coding: utf-8 -*-
"""生成《路2攻防XXXI-离线且简单目标定量-C₂^K严格域上界与入口C闭合判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXI-离线且简单目标定量-C₂^K严格域上界与入口C闭合判定.docx"
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
    # 表头行跨页重复
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
rich(tp, [("b", "路2攻防XXXI—离线且简单目标定量：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(10)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "C₂^K 严格域上界与入口 C 闭合判定")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：攻防 XIII 审计、核 (a) 越线对象误读与“离线且简单”目标的入口 C 闭合")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 23 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行用户指令「攻防 XIII 审计逐条核 → 核 (a) → “离线且简单”理论结构审计 → 入口 C」，把 S1 谱对偶恢复（攻防 XXX：λ*=0.7397、C₀^K=0.8751 越线）之后的“常数→θ_K 推进”最后一公里钉成精确目标。四步产出：（i）攻防 XIII 审计逐条核验：0.874957=B_new=(1507−2√921)/1653（代数验证 0.874957069799，7/8−B_new=4.293×10⁻⁵）是零无区域边界（QRH 输入）而非在线比例起点——真实战场是在线比例 0.6725→0.875（缺口 0.2）；关键发现：我们的 C₀=2−C_MT=0.672501 与 C₂_ζ=0.88762 就是 Lamzouri 的在线比例常数（67.25% 与 88.76%）——同族 Bridge（配对常数→在线比例）已被文献同构确认。（ii）核 (a) 反转：同族链与跨族链结构同构（命题 2.1 纯组合无条件、常数合成公式逐位相同），但越线对象被误读——S1 越线的是 C₂^K=0.8751（简单∪在线），不是 C₀^K=0.6361（简单且在线）；目标 θ_K≥7/8 是纯在线，C₂^K 越线给不了，需第三层桥“离线且简单控制”；且越线富余仅 1e-4，四个缺环全在。（iii）“离线且简单”目标等价式：θ_K≥0.875 ⟸ N_off_simple≤(C₂^K−0.875)·N_K；Δ 定律不直接挂钩——互斥是二阶配对结构，到“离线简单”（一阶+位置）需显式公式/配对和余项当桥，攻防 XIII 的“任何并置须显式建桥”警告在此兑现。（iv）入口 C 变分扫描闭合：严格域（λ₀≤1，BGST 引理 3.1 覆盖）C₂^K 上界 0.9768@λ₀=1.0，“离线且简单”目标从 λ₀=0.74 的 ~430 个零点放宽至 0.1018·N_K≈21.9 万个（×500，攻防 XXX“素项 α=1 停止”判定的直接兑现）；超支撑域（λ₀∈(1,1.08]）饱和至 1 但合法性挂在 γ(α) 高频=0 严格化上，为 +2.3 个百分点攻 Montgomery 难度不值；λ₀>1.08 公式失效。入口 C 没有消灭目标：“离线且简单≤0.1018·N_K”仍等价于“在线比例≥7/8”的弱化，剩余杠杆只剩入口 A（显式公式余项定量，攻防 XIX 数值级 10⁻⁵~10⁻³）。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "跨族 Bridge 继承；C₂^K 越线对象；离线且简单；显式公式余项；变分上界；θ_K 在线比例")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXX[8] 判定：素项在 α=1 停止、c(η) 取截断版、S1 越线 λ*=0.7397 恢复（C₀^K=0.8751≥0.6357）、攻防 XXIX 作废、跨族定理 3.1′/3.1″ 不受影响。随后用户问“S1 λ*=0.7397 恢复是不是主线又回来了”，我们判定：回来的是 S1 支线（谱对偶不等式不幻影，方法论翻案），Δ 常数定律线从未断（65 域普适、攻防 XXV/XXVI 骨架闭合），但真正推 7/8 的 Levinson–Conrey 桥判死未翻案；“常数→θ_K 推进”的最后一公里（在线比例桥 L1/L4 + BCHB c_main 实数化）是唯一被承认的增量来源，那条线不在 S1 里。")], indent=True)
para([("n", "用户指令：先想“这最后一公里”怎么弄，随后依次执行：①攻防 XIII 审计结论逐条核；②核 (a)——跨族 C₀^K 的定义（2−c(η)−Q_eff）与同族 C₀（2−C_MT）的 Hilbert 空间结构是否同构；③“离线且简单”的理论结构审计（与 Δ 定律的跨族互斥怎么挂钩）；④入口 C——变分优化 c(η)+Q_eff 扫 C₂^K 上界。本攻防按此顺序落档。")], indent=True)

# ---------- 2 ----------
h1("2　攻防 XIII 审计结论逐条核验")
h2("2.1　审计表")
caption("表 1　攻防 XIII 审计结论逐条核验（B_new 代数经计算器复核）", before=4, after=2)
t1 = make_table(
    ["#", "审计结论", "核验", "对最后一公里的影响"],
    [
        ["1", "0.874957 = B_new=(1507−2√921)/1653", "代数验证通过（0.874957069799…，7/8−B_new=4.293×10⁻⁵）", "起点语义钉死：是零无区域边界，不是在线比例"],
        ["2", "语义：零无区域边界（σ 坐标），非比例、非密度常数", "判定逻辑成立", "0.874957 不能作为 θ_K 在线比例的起点——“起点缺口”判断作废一半"],
        ["3", "7/8 在 2026-10 语境 = OpenAI QRH 边界（Re s>7/8 无零点）", "成立", "“推 7/8”有两个互斥语义：QRH（缩边界，已被 arXiv:2610.15291 超越到 0.8748867，经 XIII 审计转述）vs 在线比例（我们的战场）"],
        ["4", "在线比例（ζ）记录 = 67.25%（Lamzouri 2/3）", "关键发现：= 我们的 C₀=2−C_MT=0.672501，同一数值", "攻防 XI 的“引理 3.2 权重移除常数”就是 Lamzouri 的在线比例下界常数——同族 Bridge 已被文献确认存在"],
        ["5", "简单∪在线（ζ）= 88.762%（Lamzouri C₂）", "= 我们的 C₂_ζ=0.88762，同一数值", "我们的 C₂ 链就是 Lamzouri 的“在线∪简单”比例链——跨族 S1 的 C₂^K=0.8751 若同构翻译，直接 >7/8"],
        ["6", "判定(1)(2)(3)(4)：0.874957 是竖线位置、7/8 是 QRH 边界、B_new 更强但距 1/2 仍远、来源=QRH θ 值", "成立", "战场必须转 L1/L4（在线比例），QRH 线增量有限"],
        ["7", "影响：方向 A（QRH）已被超越；方向 B（在线比例）是真正战场；QRH 边界可作显式公式 σ 约束输入（收紧 T^{α(β−β′)}）", "成立", "QRH 的角色 = 余项/密度输入（β≤0.874957），不是比例输入"],
        ["8", "诚实边界：QRH 依赖 OpenAI 稿件分析输入（评审中）；0.874957 与 67.25% 无直接换算", "成立（防御性声明）", "任何“C₀^K → θ_K”的并置都须显式建桥——这正是我们的 Bridge 任务"],
    ],
    [Cm(0.9), Cm(4.4), Cm(4.6), Cm(4.6)])

h2("2.2　两个硬结论")
para([("n", "① 0.874957 不是在线比例起点（攻防 XIII 已钉死）——“把 0.874957 推过 0.875”是 QRH 方向（已被 0.8748867 超越，增量归零）。真实战场：在线比例 θ_K 从 0.6725（记录）推到 ≥0.875，缺口 0.2——比 QRH 的 4.3×10⁻⁵ 大四个量级。")], indent=True)
para([("n", "② 但桥可能已经在我们手里：第 4/5 条核验暴露，我们的 C₀=0.672501 与 C₂_ζ=0.88762 就是 Lamzouri 的在线比例常数——攻防 XI 的“引理 3.1（C_MT=1.3275）→ 引理 3.2 权重移除（C₀=0.6725）→ 在线比例 θ≥C₀”这条链已被 Lamzouri 文献同构确认。那么跨族版（定理 3.1′/3.1″ + S1）若继承同一 Bridge，C₀^K=0.8751 ⟹ θ_K≥0.8751>7/8。")], indent=True)
para([("b", "最后一个待核点（就是“最后一公里”的全部内容）"), ("n", "：攻防 XI 的“配对常数 C₀ → 在线比例 θ≥C₀”翻译在跨族版本是否合法继承——三处验证：(a) 跨族 C₀^K 的定义与同族 C₀ 的 Hilbert 空间结构是否同构；(b) 数值紧性（zeros_T6e5 直接测 θ_K^num vs C₀^K 的 gap）；(c) S1 的 λ₀=0.74 超支撑无条件化。用户指令“现在就核 (a)”。")], indent=True)

# ---------- 3 ----------
h1("3　核 (a)：同族链与跨族链的结构同构与越线对象误读")
h2("3.1　逐项对照")
t2 = make_table(
    ["环节", "同族（Lamzouri/攻防 XI）", "跨族（攻防 XII/XXVII/S1）", "同构？"],
    [
        ["基础不等式", "命题 2.1：N₀ˢ ≥ 2N−ΣK²（纯组合）", "对 Z_K 无条件适用（攻防 XI §3.1）", "✓"],
        ["配对和主项", "引理 3.2：ΣK²=C_MT·N，C_MT=1.3275", "C_MT(η)=c(η)=∫η²+2∫₀¹α(η*η)，λ₀ 依赖", "✓（同一引理 5 口径）"],
        ["跨族项", "—", "Q_eff=c_cross∫|η̂|⁴（定理 3.1′ f(0)）", "附加项，数值 0.703 已验"],
        ["常数合成", "C₀=2−C_MT=0.6725；C₂=(1+2√2+2C₀)/(3+2√2)=0.8876", "C₀^K=2−c(η)−Q_eff=0.6361；C₂^K=0.8751", "✓（公式相同）"],
        ["翻译目标", "简单且在线 ≥C₀；简单∪在线 ≥C₂", "同（命题 2.1 组合论证通用）", "✓"],
    ],
    [Cm(2.4), Cm(4.4), Cm(5.0), Cm(2.6)])
caption("表 2　( a ) 同族链 vs 跨族链逐项对照（攻防 XI/XXVII/XXX 推导链逐行核对）")

h2("3.2　三个硬结论")
para([("n", "① S1 越线的是 C₂^K（简单∪在线）=0.8751，不是 C₀^K（简单且在线）=0.6361。后者离 7/8 差 0.24——“ζ_K 简单且在线 ≥0.875”不成立。把 S1 越线说成“在线比例越线”是误读。")], indent=True)
para([("n", "② 目标 θ_K≥7/8 是“纯在线”，C₂^K 越线给不了它：简单∪在线 ≥0.8751 只约束“离线且非简单 ≤0.1249”——离线且简单的零点不受约束，纯在线下界仍是 0.6361。这就是攻防 XI §4/§5(5) 已声明的缺口：“Lamzouri 框架不直接给纯在线比例，需额外桥”。")], indent=True)
para([("n", "③ 厚度致命：越线富余 1e-4（C₂^K=0.8751 vs 7/8=0.875），且四个缺环全在：(i) L(χ₅) 同族引理 3.1 未核对；(ii) 同族侧权重移除在 λ₀=0.74 核支撑 0.32 下 w 偏差 ~2.5%（跨族 w 惰性 0.3% 只覆盖跨族侧）；(iii) λ₀>1/2 超支撑（素项 α=1 停止的严格化开放）；(iv) c(η) 有限 T 检验偏 19%。任何一项误差都足以翻转 1e-4 的越线。")], indent=True)
h2("3.3　修正后的“最后一公里”——三层")
para([("n", "1. C₂^K 越线（简单∪在线 ≥0.8751）——已有，但薄；")], indent=True)
para([("n", "2. 离线且简单控制（纯在线 ≥ 简单且在线 + 离线简单界）——缺的新桥，攻防 XI §6(4) 点名过；")], indent=True)
para([("n", "3. 纯在线 ≥0.875——目标。")], indent=True)
para([("n", "第 2 层正是 Δ 定律（跨族互斥）可能介入的位置：互斥 ⟹ 两族零点不重叠，若还能压制“离线且简单”零点的并集计数，就能把 C₂^K 的越线转化为纯在线。这是攻防 XIII 警告之外我们自己的增量点。")], indent=True)

# ---------- 4 ----------
h1("4　“离线且简单”目标等价式与 Δ 定律挂钩审计")
h2("4.1　目标等价式")
para([("n", "设 N_off_simple=离线（Re ρ≠1/2）且简单（m_ρ=1）零点数。已有 C₂^K=0.8751 ⟹ N_off_nonsimple≤(1−C₂^K)·N_K。目标 θ_K≥7/8=0.875 ⟺ N_off≤0.125·N_K，于是目标等价式为：")], indent=True)
formula([("n", "θ_K ≥ 0.875 ⟸ N_off_simple ≤ (C₂^K − 0.875)·N_K。")], "1")
t3 = make_table(
    ["λ₀", "C₂^K", "C₂^K−0.875", "N_off_simple 目标（N_K≈2.15×10⁶）", "判定"],
    [
        ["0.74（门槛外）", "0.8751（审计口径）／0.8752（入口 C 复算）", "1×10⁻⁴ ／ 2×10⁻⁴", "≈200 个 ／ ≈430 个零点", "极强，无现成工具"],
        ["1.0（素项 α=1 停止后合法）", "0.9768", "0.1018", "≈21.9 万个零点（0.1018·N_K）", "宽松 ~1000 倍，可讨论"],
    ],
    [Cm(2.4), Cm(3.9), Cm(2.3), Cm(4.0), Cm(2.4)])
caption("表 3　目标等价式的两个口径（λ₀=1.0 合法性来自攻防 XXX 的素项停止判定）")
para([("n", "这就是攻防 XXX 判定的深层价值：素项停止 ⟹ λ₀ 可推大 ⟹ C₂^K 从 0.8751 升到 0.9768 ⟹“离线且简单”目标从不可达变成可讨论。")], indent=True)
h2("4.2　与 Δ 定律的挂钩——四个候选，逐一判定")
t4 = make_table(
    ["挂钩候选", "判定", "理由"],
    [
        ["直接：互斥 ⟹ 离线简单少", "不成立", "互斥是二阶（配对相关），离线简单是一阶+位置；互斥只保证两族零点不重叠"],
        ["间接①：并集离线 = 两族离线之和（无公共）", "无增量", "N_off^K=N_off^ζ+N_off^L 只把问题还原为单族离线，不压总量"],
        ["间接②：并集加权在线比例 θ_K=(N_ζθ_ζ+N_Lθ_L)/N_K", "走不通", "0.465×0.6725+0.535×1=0.8477<0.875——θ_ζ=0.6725 拖累，即使 θ_L=1 也到不了"],
        ["间接③：互斥 ⟹ 跨族配对和余项干净 ⟹ 离线零点配对缺失可量化", "唯一有理论增量", "定理 3.1′ 主项无条件（f(0)+O(1/√logT)）；每个离线简单零点的配对贡献偏离在线模型 δ²λ² 级；N_off·δ²λ²≤O(1/√logT)·NORM 可反推 N_off 上界"],
    ],
    [Cm(4.8), Cm(2.6), Cm(7.0)])
caption("表 4　Δ 定律挂钩候选判定（0.8477 经计算器复核）")
para([("b", "结论："), ("n", "Δ 定律不直接控制“离线且简单”。它给的互斥是配对结构，到“离线简单”（一阶+位置）需要显式公式/配对和余项当桥。攻防 XIII 警告的“任何并置须显式建桥”在此兑现——桥不在互斥里，在余项里。")], indent=True)
h2("4.3　真正可操作的入口（按理论增量排序）")
para([("b", "入口 A："), ("n", "显式公式余项桥（攻防 XIX 类型）——离线简单零点在显式公式中贡献 e^{(σ−1/2+it)x}（σ<1/2 衰减），其偏离全在线模型的累积 ≤ 余项上界 ⟹ N_off_simple 上界。攻防 XIX 已给数值级 0.6725−O(10⁻⁵~10⁻³)——理论化后正好落在 1e-4~1e-3 目标带。")], indent=True)
para([("b", "入口 B："), ("n", "L(χ₅) 无 Siegel 零点（小判别式 D=5 可无条件验证）⟹ 离线零点全在 σ<1/2 侧（对称成对）⟹ 离线简单 ≤N(1/2−δ,T)（密度剖面）——攻防 L1 密度数值已有，理论化需临界线附近精细密度。")], indent=True)
para([("b", "入口 C："), ("n", "C₂^K 继续做大（变分优化 c(η)+Q_eff）——C₂^K→0.99 ⟹ 离线简单目标→0.115·N_K——比攻“离线简单”本身更便宜。用户指令“做入口 C”。")], indent=True)

# ---------- 5 ----------
h1("5　入口 C 变分扫描")
h2("5.1　口径")
para([("n", "攻防 XXVII 口径（素项停止截断）：uniform 族 C_MT(λ₀)=1/λ₀−1/(6λ₀²)（引理 5 结构，λ₀ 依赖）；Q_eff=0.703/(3λ₀)；C₀^K=2−C_MT−Q_eff；C₂^K=(1+2√2+2C₀^K)/(3+2√2)。5 个 XXVII 表点全部复现（差 ≤4×10⁻⁴），门槛 λ*=0.7396（XXVII 0.7397 ✓）。")], indent=True)
h2("5.2　扫描结果（uniform 族，素项停止口径）")
t5 = make_table(
    ["λ₀", "C_MT", "Q_eff", "C₀^K", "C₂^K", "离线且简单目标 (C₂^K−7/8)·N_K"],
    [
        ["0.74（门槛外）", "1.0470", "0.3167", "0.6363", "0.8752", "≈430 个零点"],
        ["0.9", "0.9132", "0.2633", "0.8235", "0.9394", "13.9 万"],
        ["1.0（严格域 max）", "0.8333", "0.2343", "0.9323", "0.9768", "21.9 万个零点"],
        ["1.07", "0.7890", "0.2190", "0.9920", "0.9973", "26.3 万"],
        ["1.08（饱和点）", "0.7770", "0.2160", "1.0000", "1.0000", "26.9 万（最大富余）"],
        [">1.09", "—", "—", ">1", "截断 1", "公式失效（C₀^K>1 无意义）"],
    ],
    [Cm(2.3), Cm(1.9), Cm(1.9), Cm(2.0), Cm(2.0), Cm(4.0)])
caption("表 5　入口 C 变分扫描（解析公式：C_MT=1/λ₀−1/(6λ₀²)、Q_eff=0.703/(3λ₀)）")
h2("5.3　三条线判定")
para([("n", "① 严格域（λ₀≤1，BGST 引理 3.1 覆盖 0≤α≤1）：C₂^K max=0.9768@λ₀=1.0。“离线且简单”目标从 λ₀=0.74 的 ~430 个零点放宽到 21.9 万个（×500）。这是攻防 XXX“素项 α=1 停止”判定的直接兑现——不越支撑界也能拿到。")], indent=True)
para([("n", "② 超支撑域（λ₀∈(1,1.08]）：C₂^K→1（λ₀=1.08 饱和），目标→26.9 万。但 λ₀>1 越过 BGST 支撑上界，合法性挂在 γ(α) 高频=0 的严格化上（攻防 XXX 数值支持，未证）——为这 +2.3 个百分点去攻 Montgomery 难度的问题，不值。")], indent=True)
para([("n", "③ λ₀>1.08：C₀^K>1，配对和估计低估真实值，公式失效。变分已到顶。")], indent=True)
h2("5.4　入口 C 闭合结论")
para([("n", "入口 C 闭合：严格域内 C₂^K 上界 0.9768 不可再推（λ₀≤1 是硬边界；cosine 更差——λ₀=1.0→0.8322、1.25→0.9070；形状变分在 C_MT≤uniform 约束下无显著空间）。它把“离线且简单”的厚度从 1e-4 放宽到 0.1018·N_K，但没有消灭目标——“离线且简单≤21.9 万”仍等价于“在线比例≥7/8”的弱化，这一步本身还是无条件缺口。")], indent=True)
h2("5.5　剩余杠杆与诚实边界")
para([("n", "剩余杠杆只剩入口 A：显式公式余项定量（每个离线简单零点的偏离 × 计数 ≤ 余项上界，攻防 XIX 数值级 10⁻⁵~10⁻³）。入口 B（L(χ₅) 无 Siegel 零点）是旁支验证。诚实边界：λ₀=1.0 截断公式数值验证 −1.6%（攻防 XXX）；λ₀>1 无决定性数值（有限 T 误差与截断差同量级，需 T≥6×10⁷）。")], indent=True)

# ---------- 6 ----------
h1("6　判定与主线状态")
para([("n", "① Δ 常数定律线（跨族互斥→θ_K）：从未断——65 域普适、攻防 XXV/XXVI 骨架闭合，独立于 S1。")], indent=True)
para([("n", "② S1 谱对偶线：恢复且越线——λ*=0.7397、C₂^K=0.8751（简单∪在线）在纯无条件常数链（BGST 截断 + Q_eff）内成立；但越线对象是简单∪在线，非纯在线；λ₀=0.74 超支撑与 λ₀=0.5 的 31% 检验偏差两个边界仍未闭合。")], indent=True)
para([("n", "③ Levinson–Conrey 桥：判死未翻案。“常数→θ_K 推进”最后一公里=三层：C₂^K 越线（已有但薄）→ 离线且简单控制（缺的新桥）→ 纯在线 ≥0.875（目标）。")], indent=True)
para([("n", "④ 入口 C 闭合：严格域 C₂^K 上界 0.9768@λ₀=1.0；“离线且简单”目标定量化（≤0.1018·N_K≈21.9 万）；Δ 定律不直接挂钩（桥在余项不在互斥）；剩余杠杆=入口 A（显式公式余项桥）。")], indent=True)
para([("b", "下一步"), ("n", "：(1) 入口 A 理论化——攻防 XIX 的 10⁻⁵~10⁻³ 数值级理论化后落在 1e-4~1e-3 目标带；(2) 更大 T（T≥6×10⁷）把 λ₀=1.0 截断公式验证（−1.6%）升级为决定性；(3) L(χ₅) 无 Siegel 零点验证（D=5 可无条件）作旁支；(4) 四个缺环逐项闭合（L(χ₅) 引理 3.1、w 偏差 ~2.5%、超支撑严格化、c(η) 检验偏 19%）。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XIII：路2攻防XIII-0.874957语义澄清-QRH代数边界B_new.docx（B_new=(1507−2√921)/1653 原始陈述；本攻防审计对象）.",
    "攻防 XI：路2攻防XI-Lamzouri机制链与跨族接入判定-0.874957语义存疑.docx（引理 3.1/3.2 权重移除链、§4/§5(5) 纯在线缺口、§6(4) 离线简单点名）.",
    "攻防 XII：路2攻防XII-跨族引理-BGST配对相关的zeta_K版本.docx（定理 3.1′：f(0)+O(1/√logT)，素项 χ₅ 振荡消除）.",
    "攻防 XVII：路2攻防XVII-基线依赖调和-跨族排斥与聚集的成立范围.docx（配对层 Δ_pair/N_K≈−0.7%）.",
    "攻防 XIX：路2攻防XIX-并集素项净压制与余项数值级-L主项修正.docx（显式公式余项桥数值级 10⁻⁵~10⁻³）.",
    "攻防 XXVII：路2攻防XXVII-引理3.2跨族权重移除-配对常数NζNL与Q(0)口径修正.docx（c(η) 截断口径、Q_eff=0.703/(3λ₀)、C₂^K 合成、λ*=0.7397）.",
    "攻防 XXVIII：路2攻防XXVIII-定理3.1′支撑放宽-跨族无素项与λ大于1-2无条件化.docx（跨族支撑放宽，不受本轮勘误影响）.",
    "攻防 XXX：路2攻防XXX-BGST口径勘误-素项在alpha等于1停止与S1越线判定恢复.docx（素项 α=1 停止、S1 λ*=0.7397 恢复、λ₀=1.0 截断公式验证 −1.6%）.",
    "LAMZOURI Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line[EB/OL]. arXiv:2609.02882, 2026. https://arxiv.org/abs/2609.02882（在线比例 67.25%、简单或在线 88.76%）.",
    "MONTGOMERY H L. The pair correlation of zeros of the zeta function[C]//Proceedings of Symposia in Pure Mathematics. Providence: AMS, 1973, 24: 181–193（γ(α) 配对猜想）.",
    "BALUYOT D, GOLDSTON D, SURIAJAYA A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function[EB/OL]. arXiv:2306.04799; Acta Arith. 214 (2024) 357–376（引理 5、定理 1、含对角双侧口径）.",
    "数值数据：l4_multit.json（N_K=2149542，T=6×10⁵）；入口 C 变分扫描（uniform 族、素项停止口径，5 个 XXVII 表点复现差 ≤4×10⁻⁴；本轮落档）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
