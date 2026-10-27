# -*- coding: utf-8 -*-
"""生成《路2攻防XXXII-入口A显式公式余项桥数值定向-离线且简单在虚部统计口径中的可见性判定.docx》（d1 惯例）"""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_TAB_ALIGNMENT
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXII-入口A显式公式余项桥数值定向-离线且简单在虚部统计口径中的可见性判定.docx"
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
rich(tp, [("b", "路2攻防XXXII—入口A显式公式余项桥数值定向：")], size=18, eastasia=HEI)
tp2 = doc.add_paragraph()
tp2.alignment = WD_ALIGN_PARAGRAPH.CENTER
tp2.paragraph_format.space_after = Pt(10)
tp2.paragraph_format.line_spacing = 1.5
rich(tp2, [("b", "离线且简单在虚部统计口径中的可见性判定")], size=18, eastasia=HEI)
para([("n", "——《谱对偶论证》系列（d1）：ψ 均方口径空桥、对数导数 SNR 受限与入口 A 证伪")],
     indent=False, align="center", size=12, eastasia=KAI, after=2)
para([("n", "2026 年 10 月 23 日")], indent=False, align="center", size=9, after=12)

# ---------- 摘要 ----------
para([("b", "摘要：")], indent=False)
para([("n", "本攻防执行用户指令「直接进入口 A」，把攻防 XXXI 闭合入口 C 之后的唯一剩余杠杆——显式公式余项桥——钉成精确的数值判定：离线且简单零点（Re ρ≠1/2、m_ρ=1）在一切虚部统计口径中的可见性。三组实验给出判定性结果：（i）ψ 显式公式均方口径（M_on 扰动扫描，9 个深度 δ×7 个数量 K）是空桥——离线零点贡献被 1/|1/2+iγ|² 权重稀释到 wbar~10⁻¹¹~10⁻⁹，K=21.9 万（λ₀=1.0 目标带）相对自然余项仅 0.06%~0.7%，反推 N_off_max(c=1)=(C_R·√N/(δλ))² 在 δ≤0.4 全为 40~15900 倍 N_K，无约束。（ii）对数导数实部峰口径（Re[1/(s−ρ)]=δ/(δ²+(t−γ)²)，每离线零点积分面积 π 与 δ 无关）机制存在，但素数项背景 rms=13.45（X=10⁶）限单峰分辨 δ≥~0.074；细峰测试 5γ×4δ 仅 δ=0.02 全可辨、δ=0.05 2/5、δ=0.1 起全不可辨。（iii）ε 正则化（σ=1/2+ε）后背景真收敛（rms 3~8）但峰高 1/(ε+δ) 同步下降，SNR 恒 1.7~3.5，且 σ>1/2 处在线零点同样贡献峰——峰宽分辨需 δ>dt，深度分辨率限制未解除。理论核查确认：定理 3.1′ 配对和、S_K(t) 跳跃、Levinson ΣK² 全是纯虚部差口径，离线零点一阶不可见。综合判定：入口 A 单独作 N_off_simple 控制器证伪——离线零点的唯一干净签名在 σ 方向密度剖面（入口 B）；入口 A 仅保留为与入口 B 联动的“已知深度界→余项桥反推数量”的合并形式。")], indent=True)
para([("b", "关键词：")], indent=False)
para([("n", "显式公式余项桥；离线且简单；ψ 均方口径；对数导数实部峰；SNR 分辨限；密度剖面")], indent=False)

# ---------- 1 ----------
h1("1　承接与任务")
para([("n", "攻防 XXXI[1] 闭合入口 C：严格域（λ₀≤1，BGST 引理 3.1 覆盖）内 C₂^K 上界 0.9768@λ₀=1.0，“离线且简单”目标 N_off_simple≤(C₂^K−0.875)·N_K 从 λ₀=0.74 口径的 ~430 个零点放宽至 0.1018·N_K≈21.9 万个。但入口 C 没有消灭目标——“离线且简单≤0.1018·N_K”仍等价于“在线比例≥7/8”的弱化，剩余杠杆只剩入口 A（显式公式余项定量，攻防 XIX[2] 数值级 10⁻⁵~10⁻³）。用户指令“直接进入口 A”。")], indent=True)
para([("n", "入口 A 的定义：把离线且简单零点（Re ρ=1/2−δ<1/2、重数 1）在显式公式中的贡献/偏离定量化，反推 N_off_simple 上界。偏离载体有三条候选口径：(a) ψ 显式公式均方口径（离线零点相对全在线模型的偏离在 ψ(x)=x−Σx^ρ/ρ 中的功率）；（b）对数导数实部峰口径（−(ζ_K′/ζ_K)(1/2+it) 的实部中每个离线零点贡献一个正峰，积分面积 π）；（c）ε 正则化（σ=1/2+ε 处求值，压背景）。本攻防对三条口径逐一数值定向。数值基线：zeros_T6e5.npz（T=6×10⁵，ζ 族 999492 根、L(χ₅) 族 1150050 根、N_K=2149542、λ=log T=13.30）；L 族含 0.27% R-S 求根系统伪影（趋势 −0.0052/单位），差分口径免疫、绝对值口径需重建零点。")], indent=True)

# ---------- 2 ----------
h1("2　实验一：ψ 显式公式均方口径——空桥判定")
h2("2.1　框架与数据")
para([("n", "全在线模型 M_on(u)=Σ_γ e^{iuγ}/(1/2+iγ)（u=log x，u∈[3,λ+2]，200 网格，γ 遍历全部 2149542 个并集零点）；扰动 B(u)=Σ_off e^{iuγ}[e^{−δu}/(1/2−δ+iγ)−1/(1/2+iγ)]（离线零点深度 δ 的偏离）；相位随机近似 E|B|²≈K·wbar（K=离线零点数，wbar=单零点系数差模方均值）。扫描 9 个 δ（0.005~0.4）×7 个 K（含 219000 目标带、430000）。M_on 统计量：sup=0.8683、rms=0.3272、C_R=sup/√N_K=5.922×10⁻⁴。")], indent=True)
h2("2.2　反推上界与判定")
caption("表 1　ψ 均方口径反推 N_off_max(δ)（单位：×N_K；自然余项带 c=1 与半带 c=0.5）", before=4, after=2)
t1 = make_table(
    ["δ", "wbar（单零点系数差模方）", "N_off_max(c=1)（×N_K）", "N_off_max(c=0.5)（×N_K）", "相对目标带 0.1018·N_K"],
    [
        ["0.005", "2.206×10⁻¹¹", "15900.1", "3974.0", "156200 倍"],
        ["0.01", "8.339×10⁻¹¹", "4205.7", "1051.4", "41300 倍"],
        ["0.02", "2.987×10⁻¹⁰", "1174.2", "293.6", "11500 倍"],
        ["0.03", "6.036×10⁻¹⁰", "581.1", "145.3", "5710 倍"],
        ["0.05", "1.365×10⁻⁹", "257.0", "64.3", "2520 倍"],
        ["0.08", "2.619×10⁻⁹", "133.9", "33.5", "1320 倍"],
        ["0.1", "3.422×10⁻⁹", "102.5", "25.6", "1010 倍"],
        ["0.2", "6.381×10⁻⁹", "55.0", "13.7", "540 倍"],
        ["0.4", "8.723×10⁻⁹", "40.2", "10.1", "395 倍"],
    ],
    [Cm(1.4), Cm(3.4), Cm(3.2), Cm(3.2), Cm(3.2)])
para([("n", "反推公式：N_off_max(c)=（c·rms_M/√wbar）² =（C_R·√N_K/(δλ) 标度）×（c/√wbar 项），c 为自然余项带宽系数。判定：c=1 时全行 40~15900 倍 N_K；即使压缩到半带 c=0.5，δ=0.4 时仍有 10.1·N_K——全部远超目标带 0.1018·N_K≈21.9 万（λ₀=0.74 的 430 个更是差五个量级）。")], indent=True)
para([("b", "机制判明（空桥根因）："), ("n", "M_on 的零点权重 1/(1/2+iγ)~1/γ 把离线贡献压到 δ/γ 量级——ψ 层面对 σ 的敏感度被 γ 稀释到 ~10⁻⁴ 相对量级。定量：K=21.9 万时 E|B|²/(K·wbar) 的实测/预测比 ratio 在 0.046~15.06 剧烈波动（随机子集敏感，K=219000 时 1.35~15.06），均方口径无稳定标度；相对自然余项 rms_M²=0.1070，K·wbar 仅占 0.06%（δ=0.02）~0.7%（δ=0.1）。ψ 均方口径对“离线且简单”是空桥——这正解释了攻防 XIX 的在线比例 0.6725 级下界只靠 1/γ 权重就能成立的对称原因：σ 方向的偏离在 ψ 层不可见。")], indent=True)

# ---------- 3 ----------
h1("3　实验二：对数导数实部峰口径")
h2("3.1　恒等式与峰值机制")
para([("n", "对数导数实部恒等式：−(ζ_K′/ζ_K)(1/2+it)=Σ_ρ 1/(s−ρ)−解析项；对在线零点（σ=1/2）Re[1/(i(t−γ))]=0（t≠γ），无实部贡献；对离线零点（σ=1/2−δ）Re[1/(δ+i(t−γ))]=δ/(δ²+(t−γ)²)>0——每个离线零点一个正峰，全区间积分面积 π 与 δ 无关。这是对 σ 一阶敏感、且天然免疫在线零点的计数器。素数项背景 F₀(t)=Re Σ_{p≤X}(1+χ₅(p))log p·p^{−1/2−it}。")], indent=True)
formula([("n", "Re[1/(δ+i(t−γ))] = δ/(δ²+(t−γ)²)，  ∫_{−∞}^{+∞} dt = π（与 δ 无关）。")], "1")
h2("3.2　背景与单峰分辨")
para([("n", "X=10⁶ 素数表（Np=78498）：Σa²=181.03、背景 rms=13.4548；峰面积解析验证 area/π≈K（K=430→233.999π、5000→2598π，边界截断使略小于 K）；单峰高 1/δ vs 背景 rms 决定可分辨性。")], indent=True)
caption("表 2　对数导数单峰分辨率（背景 rms=13.4548，X=10⁶；细峰测试 5 个 γ×4 个 δ）", before=4, after=2)
t2 = make_table(
    ["δ", "峰高 1/δ", "SNR_h=峰高/背景rms", "细峰可辨（5γ）", "判定"],
    [
        ["0.02", "50.0", "3.716", "5/5", "可分辨"],
        ["0.05", "20.0", "1.486", "2/5", "临界（分辨限 δ≈0.074）"],
        ["0.1", "10.0", "0.743", "0/5", "不可分辨"],
        ["0.2", "5.0", "0.372", "0/5", "不可分辨"],
        ["0.4", "2.5", "0.186", "—", "不可分辨"],
    ],
    [Cm(1.3), Cm(1.8), Cm(3.6), Cm(3.0), Cm(4.4)])
para([("n", "细峰测试（局部细网格 dt 扫描，数值面积与理论 π 吻合 2.811~2.815）：δ=0.02 全部可分辨（峰高 50≫局部背景 rms 2.2~19.8）；δ=0.05 仅 2/5（峰高 20 vs 背景 6.8~15.0）；δ=0.1 起全不可分辨。可分辨深度下界 δ_c≈0.03~0.05。目标带 21.9 万离线零点（若来自 2-下降机制）绝大多数深度 δ 远小于此——单峰口径测不出。")], indent=True)
h2("3.3　背景积分口径的数学障碍")
para([("n", "全区间背景积分实测 int_bg=Σa_p[sin(T·log p)−sin((T/2)·log p)]/log p≈−0.94（X=10⁶ 截断瞬时值，边界振荡项对消）——若以此为准，K=430 峰面积 735 vs 背景积分 0.94 的积分口径 SNR≈778，K=21.9 万时 ≈3.9×10⁵，积分口径在随机噪声意义下信噪比极高。但数学上背景积分不收敛：Σ_{p≤X}(1+χ₅(p))/√p 的部分和随 X 无界增长（(1+χ₅) 非字符，无 χ 振荡消除），int_bg=−0.94 只是 X=10⁶ 截断的幸运对消，X→∞ 时背景积分发散，峰面积 K·π 淹没其中。需 σ>1/2 正则化（实验三）。")], indent=True)

# ---------- 4 ----------
h1("4　实验三：ε 正则化（σ=1/2+ε）")
para([("n", "改在 s=1/2+ε+it 求 Re 对数导数：素项背景功率 Σa²p^{−2ε} 真收敛（ε=0.05→rms 8.05、0.1→5.52、0.2→2.94），但峰高从 1/δ 变为 1/(ε+δ)——ε=0.05→20、0.1→10、0.2→5——SNR 恒 ~1.7~3.5，无本质改善。38 零点的 t 窗口峰检测（阈值 2σ）只检出 14~26 个，不可靠。")], indent=True)
caption("表 3　ε 正则化背景扫描（X=3×10⁵，38 零点窗口，窗口宽 22）", before=4, after=2)
t3 = make_table(
    ["ε", "背景功率 Σa²p^{−2ε}", "背景 rms", "在线峰高 1/ε", "sup|F|", "阈值 2σ", "检出峰数/窗口"],
    [
        ["0.05", "64.793", "8.049", "20.0", "27.83", "16.10", "19/38"],
        ["0.1", "30.506", "5.523", "10.0", "15.79", "11.05", "14/38"],
        ["0.2", "8.622", "2.936", "5.0", "9.93", "5.87", "26/38"],
    ],
    [Cm(1.3), Cm(3.0), Cm(2.0), Cm(2.2), Cm(2.0), Cm(2.0), Cm(3.0)])
para([("b", "更深一层的障碍："), ("n", "σ>1/2 处在线零点同样贡献峰（Re[1/(ε+i(t−γ))]=ε/(ε²+(t−γ)²)，面积 π）——积分口径把在线与离线混在一起，无法分离。唯一分离通道是峰宽：在线峰宽 ε、离线峰宽 ε+δ；分辨 δ 需要数值积分步长 dt<δ——回到深度分辨率限制（δ≥~0.05~0.1 且计算成本随 1/δ 爆炸：T=6×10⁵ 全区间 dt=0.05 需 ~10¹¹ 次素数项求值）。ε 正则化是换汤不换药。")], indent=True)

# ---------- 5 ----------
h1("5　理论核查：虚部统计口径对 σ 一阶盲")
para([("n", "三条既有统计口径全部是纯虚部差口径：(a) 定理 3.1′ 配对和 Σ_{γ≠γ′} f(i(γ−γ′)λ)——核只依赖虚部差，离线零点（σ 偏离）在配对结构中的签名是 δ²λ² 级二阶量；(b) S_K(t)=arg ζ_K(1/2+it)/π 的跳跃——离线零点的跳跃形状与在线零点相同（都是 1/π 阶跃），跳跃计数不区分位置；(c) Levinson ΣK²（简单性）——重数统计同样与 σ 位置无关。结论：离线零点在所有虚部统计中一阶不可见。")], indent=True)
para([("n", "唯一干净签名在 σ 方向：N(σ,T)=#{ρ：Re ρ≥σ} 密度剖面。若离线零点全在 σ<1/2 侧（L(χ₅) 无 Siegel 零点可无条件验证，D=5），则离线且简单 ≤N(1/2−δ,T)——这是入口 B 的领域。入口 A 在“合并形式”下保留：若入口 B 给出深度界 δ_max（离线零点全在 Re ρ≤1/2−δ_max），则对数导数峰宽测量（δ≥δ_max 时峰宽 ε+δ 偏离 ε 可测）或 ψ 均方口径（δ_max 代入 wbar(δ)）可反推数量——两者联动的理论增量在，但单独作 N_off_simple 控制器已证伪。")], indent=True)

# ---------- 6 ----------
h1("6　判定与主线状态")
caption("表 4　入口 A 三口径判定总表（T=6×10⁵、N_K=2149542、X=10⁶/3×10⁵ 素数表）", before=4, after=2)
t4 = make_table(
    ["口径", "信号", "背景/噪声", "SNR 或约束力", "判定"],
    [
        ["ψ 均方（实验一）", "E|B|²≈K·wbar，wbar~10⁻¹¹~10⁻⁹", "自然余项 rms 0.327", "K=21.9 万相对效应 ≤0.7%", "空桥（无约束）"],
        ["对数导数单峰（实验二）", "峰高 1/δ、面积 π", "素数项 rms 13.45", "SNR_h=1/(δ·rms)：δ≥0.074 才可辨", "浅离线测不出"],
        ["对数导数积分（实验二）", "Σ峰面积=π·N_off", "背景积分 X→∞ 发散", "截断瞬时 SNR 极高但数学失效", "需正则化"],
        ["ε 正则化（实验三）", "峰高 1/(ε+δ)", "背景真收敛 rms 3~8", "SNR 恒 1.7~3.5，检出 14~26/38", "换汤不换药"],
        ["虚部统计（理论核查）", "配对/S(t)/ΣK²", "—", "纯虚部差口径", "对 σ 一阶盲"],
    ],
    [Cm(3.0), Cm(3.3), Cm(2.9), Cm(3.4), Cm(2.3)])
para([("n", "① 入口 A 单独作 N_off_simple 控制器：证伪。三条数值路线均未给出可用的 N_off_simple 上界——ψ 均方口径空桥（稀释到不可见）、对数导数单峰受背景 rms=13.45 限（分辨限 δ≈0.074，浅离线零点全在 δ≪0.03）、ε 正则化 SNR 不提升且在线零点污染积分口径。")], indent=True)
para([("n", "② 攻防 XXXI 把入口 A 列为“唯一剩余杠杆”的口径需修正：它只有在“已知深度界 δ_max（入口 B 输入）→ 余项桥反推数量”的合并形式下才有理论增量；独立作为“离线且简单”的控制器，数值上被证伪。")], indent=True)
para([("n", "③ 主线剩余杠杆重排：(1) 入口 B——N(1/2−δ,T) 密度剖面理论化 + L(χ₅) 无 Siegel 零点无条件验证（D=5），离线零点的唯一干净签名；(2) λ₀=0.74 目标带的更严 C₂^K 口径复核（若回到 430 个的极严口径，任何离线计数都必须无条件）；(3) 更大 T（T≥6×10⁷）把 λ₀=1.0 截断公式验证（−1.6%）升级为决定性，同时压背景 rms（∝√log log T 增长极慢，收益有限，须诚实标注）。")], indent=True)
para([("b", "下一步"), ("n", "：入口 B 密度剖面数值定向（攻防 L1 密度已有，需临界线附近精细剖面 N(1/2−δ,T)），或直接落“攻防 XXXI 剩余杠杆口径修正”到主线。")], indent=True)

# ---------- 参考文献 ----------
h1("参考文献")
refs = [
    "攻防 XXXI：路2攻防XXXI-离线且简单目标定量-C₂^K严格域上界与入口C闭合判定.docx（入口 C 闭合：0.9768@λ₀=1.0、目标放宽至 0.1018·N_K≈21.9 万；本攻防的承接对象）.",
    "攻防 XIX：路2攻防XIX-并集素项净压制与余项数值级-L主项修正.docx（显式公式余项桥数值级 10⁻⁵~10⁻³、在线比例 0.6725−O(10⁻⁵~10⁻³)；L 主项与相位）.",
    "攻防 XII：路2攻防XII-跨族引理-BGST配对相关的zeta_K版本.docx（定理 3.1′：f(0)+O(1/√logT)，素项 χ₅ 振荡消除）.",
    "攻防 XXVII：路2攻防XXVII-引理3.2跨族权重移除-配对常数NζNL与Q(0)口径修正.docx（c(η) 截断口径、Q_eff=0.703/(3λ₀)、C₂^K 合成、λ*=0.7397）.",
    "攻防 XXVIII：路2攻防XXVIII-定理3.1′支撑放宽-跨族无素项与λ大于1-2无条件化.docx（跨族支撑放宽）.",
    "攻防 XXX：路2攻防XXX-BGST口径勘误-素项在alpha等于1停止与S1越线判定恢复.docx（素项 α=1 停止、S1 λ*=0.7397 恢复、λ₀=1.0 截断公式验证 −1.6%）.",
    "LAMZOURI Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line[EB/OL]. arXiv:2609.02882, 2026. https://arxiv.org/abs/2609.02882（在线比例 67.25%、简单或在线 88.76%）.",
    "BALUYOT D, GOLDSTON D, SURIAJAYA A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function[EB/OL]. arXiv:2306.04799; Acta Arith. 214 (2024) 357–376（引理 5、定理 1，λ₀≤1 支撑）.",
    "数值数据：zeros_T6e5.npz（ζ 999492 根、L(χ₅) 1150050 根、N_K=2149542、T=6×10⁵）；entA_bridge.json / entA_ld.json / entA_eps.json（本轮三组实验，脚本 entA_bridge.py / entA_ld.py / entA_eps.py 可复跑）.",
]
for i, r in enumerate(refs, 1):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Pt(0)
    p.paragraph_format.space_after = Pt(2)
    p.paragraph_format.line_spacing = 1.15
    rich(p, [("n", "[" + str(i) + "] " + r)], size=9)

doc.save(OUT)
print("SAVED:", OUT)
