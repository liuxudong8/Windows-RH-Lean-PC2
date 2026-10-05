# -*- coding: utf-8 -*-
"""编辑骨架A讨论稿 5.4 节：degree-2 数值延拓结果（i 已闭合，保留 ii/iii 待补）"""
import shutil
from docx import Document
from docx.shared import Pt
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.oxml.ns import qn

SRC = r'D:\F\有名公司同事文档\刘旭东文集\3new\关于引力的思考和黎曼猜想\Arthur 迹公式\BSD\弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx'
TMP = r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_v2_work.docx'
shutil.copy2(SRC, TMP)

doc = Document(TMP)

def set_font(run, east, latin, size, bold=False):
    run.font.name = latin
    run.font.size = Pt(size)
    run.font.bold = bold
    rPr = run._element.get_or_add_rPr()
    rFonts = rPr.rFonts
    if rFonts is None:
        rFonts = rPr.makeelement(qn('w:rFonts'), {})
        rPr.append(rFonts)
    rFonts.set(qn('w:eastAsia'), east)

def clone_para(src_para):
    """深拷贝段落元素，返回新 Paragraph 对象（插入在 src 之后，保持顺序）"""
    import copy
    from docx.text.paragraph import Paragraph
    new_el = copy.deepcopy(src_para._element)
    src_para._element.addnext(new_el)
    return Paragraph(new_el, src_para._parent)

# 定位 5.4 标题与后续正文
h2 = None
body = None
paras = doc.paragraphs
for i, p in enumerate(paras):
    t = p.text.strip()
    if t.startswith('5.4') and p.style.name == 'Heading 2':
        h2 = p
        body = paras[i + 1]
        break
assert h2 is not None and body is not None, '未定位到 5.4 节: ' + str([p.text for p in doc.paragraphs if '5.4' in p.text])

# 改标题文本（保留样式：直接重写 runs）
for r in list(h2.runs):
    r.text = ''
h2.runs[0].text = '5.4  degree-2 数值延拓与待补'

# 新正文段落（模板 = 旧正文段样式）
new_texts = [
    ('（i）degree-2 数值延拓已闭合。', 'Dokchitser 型反射公式取 Λ(s) = Σ_n a_n[ε·b^(s−2)·Γ(2−s, b) + b^(−s)·Γ(s, b)]，其中 b = 2πn/√N，ε 为根数。此形态含早期版本遗漏的 b 幂次因子；Fricke 反射常数即 ε，不另含 N 因子。'),
    ('ℚ 端 37a1（N = 37，ε = −1）：', 'L(1) = 0 自动成立；L′(1) = 0.30599964（中心差分 h = 10⁻³），与 LMFDB 值 0.30599977 相差 1.4 × 10⁻⁷；收敛域 s = 3 处直接 Dirichlet 级数与反射公式之比 1.00000028，管线闭合。'),
    ('K = ℚ(√5) 端（N_K = 37² = 1369，ε_K = −1 由 L_K(1) = 0 自动确认）：', '局部因子按分裂（1 − a_pX + pX²）⁻²、惰性（1 − (a_p² − 2p)X + p²X²）⁻¹（Nm = p² 变量，奇数幂系数为 0）、分歧 5（1 − a₅X + 5X²）⁻¹、37 惰性乘性（1 − X）⁻¹ 构造；抽样核对 b₄ = 0、b₉ = 3、b₁₁ = −10、b₅ = −2、b₄₉ = −13 全部吻合。数值结果 L_K(1) = 0、L_K′(1) = 2.433224 ≠ 0。'),
    ('结论：', '结合 2.1 节代数秩 ≥ 1（有理点 (0,0) 无限阶），L_K′(1) ≠ 0 给出弱 BSD 未证方向“代数秩 ≥ 1 ⟹ 解析秩 ≥ 1”在 E = 37a1/ℚ(√5) 上的数值证据。s = 3 处直接级数与反射公式之比 1.00337 为 L_K 直接级数的截断尾（随 s 增大趋 1：s = 5 时 1.0000042），非管线系统误差。'),
    ('（ii）4.1 显式公式精确形态按标准 Weil 公式核对；（iii）4.3 全消矛盾的严格化。', None),
]

# 第一个新段：改旧正文段文本
r0 = body.runs[0]
r0.text = new_texts[0][0]
run1 = body.add_run(new_texts[0][1])
set_font(run1, '宋体', 'Times New Roman', 10.5)

# 后续段落：依次插在上一段之后（锚点推进）
last = body
for lead, rest in new_texts[1:]:
    np = clone_para(last)
    # 清空原 runs，重新写
    for r in list(np.runs):
        r._element.getparent().remove(r._element)
    if lead:
        rl = np.add_run(lead)
        set_font(rl, '宋体', 'Times New Roman', 10.5, bold=True)
    if rest:
        rr = np.add_run(rest)
        set_font(rr, '宋体', 'Times New Roman', 10.5)
    last = np

# 关联更新 1：1.3 节"判秩所需的完整 L 函数数值延拓留待补" → 已闭合
for p in doc.paragraphs:
    if '判秩所需的完整 L 函数数值延拓留待补' in p.text:
        for r in p.runs:
            if '判秩所需的完整 L 函数数值延拓留待补' in r.text:
                r.text = r.text.replace('判秩所需的完整 L 函数数值延拓留待补', '判秩所需的完整 L 函数数值延拓已闭合（见 5.4）')

# 关联更新 2：6 节结论末句
for p in doc.paragraphs:
    if '判秩数值延拓与显式公式精确系数是下一步的两条闭合路径' in p.text:
        for r in p.runs:
            if '判秩数值延拓与显式公式精确系数是下一步的两条闭合路径' in r.text:
                r.text = r.text.replace('判秩数值延拓与显式公式精确系数是下一步的两条闭合路径', '显式公式精确系数与全消矛盾的严格化是下一步的两条闭合路径')

doc.save(TMP)
print('OK saved:', TMP)
