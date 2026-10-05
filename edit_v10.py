# -*- coding: utf-8 -*-
"""Apply K-GRH consistency edits to v10 docx (target working copy).

Text edits: 15 spots. OMML edits: wrap ζ/ρ/Λ in m:sSub with K subscript
at paras 12, 29, 162, 205, 206.
"""
import docx
from docx.oxml.ns import qn

PATH = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(PATH)
paras = d.paragraphs

# ---------- helpers ----------
def set_run_text(p_idx, r_idx, new_text):
    p = paras[p_idx]
    runs = p._p.findall(qn('w:r'))
    t = runs[r_idx].find(qn('w:t'))
    assert t is not None, 'no w:t in run %d of para %d' % (r_idx, p_idx)
    old = t.text or ''
    t.text = new_text
    print('TXT p%d r%d: %r -> %r' % (p_idx, r_idx, old, new_text))

def replace_in_run(p_idx, r_idx, old, new):
    p = paras[p_idx]
    runs = p._p.findall(qn('w:r'))
    t = runs[r_idx].find(qn('w:t'))
    assert t is not None, 'no w:t in run %d of para %d' % (r_idx, p_idx)
    cur = t.text or ''
    assert old in cur, 'pattern %r not in p%d r%d: %r' % (old, p_idx, r_idx, cur)
    t.text = cur.replace(old, new)
    print('RPL p%d r%d: %r -> %r' % (p_idx, r_idx, old, new))

def wrap_subscript(m_r, sub_text='K'):
    """Wrap an <m:r> element inside <m:sSub>(<m:e>run</m:e>, <m:sub>K</m:sub>).

    Order matters: insert ssub before m_r while m_r is still a child, then
    move m_r into m:e (which detaches it from its old parent).
    """
    parent = m_r.getparent()
    ssub = parent.makeelement(qn('m:sSub'), {})
    ssubPr = parent.makeelement(qn('m:sSubPr'), {})
    ctrlPr = parent.makeelement(qn('m:ctrlPr'), {})
    wrpr = parent.makeelement(qn('w:rPr'), {})
    rfonts = parent.makeelement(qn('w:rFonts'),
        {qn('w:ascii'): 'Cambria Math', qn('w:hAnsi'): 'Cambria Math'})
    wrpr.append(rfonts); ctrlPr.append(wrpr); ssubPr.append(ctrlPr); ssub.append(ssubPr)
    e = parent.makeelement(qn('m:e'), {})
    ssub.append(e)
    sub = parent.makeelement(qn('m:sub'), {})
    sr = parent.makeelement(qn('m:r'), {})
    srpr = parent.makeelement(qn('w:rPr'), {})
    srfonts = parent.makeelement(qn('w:rFonts'),
        {qn('w:ascii'): 'Cambria Math', qn('w:hAnsi'): 'Cambria Math'})
    srpr.append(srfonts); sr.append(srpr)
    st = parent.makeelement(qn('m:t'), {}); st.text = sub_text
    sr.append(st); sub.append(sr); ssub.append(sub)
    m_r.addprevious(ssub)   # m_r still under parent
    e.append(m_r)           # detach m_r into m:e

def math_runs(container, txt):
    """All <m:r> under container whose <m:t> text == txt."""
    out = []
    for r in container.iter(qn('m:r')):
        for t in r.iter(qn('m:t')):
            if (t.text or '') == txt:
                out.append(r)
                break
    return out

def omath_at(p_idx):
    """Return first m:oMath (inline) or oMathPara>oMath at paragraph."""
    p = paras[p_idx]
    om = p._p.find(qn('m:oMath'))
    if om is not None:
        return om
    omp = p._p.find(qn('m:oMathPara'))
    if omp is not None:
        return omp.find(qn('m:oMath'))
    return None

# ---------- 1. text edits ----------
ZETA_K = 'ζ\u2096'  # ζₖ (U+03B6 + U+2096)

# T1 p10 Chinese title
replace_in_run(10, 1, '黎曼 ζ 非平凡零点临界线说明',
               '实二次域 Dedekind %s 非平凡零点临界线说明' % ZETA_K)

# T2/T3 p21 keywords
replace_in_run(21, 1, '黎曼猜想；紧支磨光测试函数；黎曼',
               '局部广义黎曼假设；紧支磨光测试函数；Dedekind %s' % ZETA_K)
set_run_text(21, 2, '')
set_run_text(21, 3, '显式公式')

# T4 p29 abstract item 5 (text part)
replace_in_run(29, 0, '约化为黎曼', '约化为 Dedekind %s(s) 的' % ZETA_K)
set_run_text(29, 1, '')
set_run_text(29, 2, '有限截断显式公式；推导出')

# T5 p34 sec 1.1
set_run_text(34, 7, '实二次域 K=Q(√5) 的局部广义黎曼假设（K-GRH）')

# T6 p47 sec 1.3 item 5
replace_in_run(47, 2, '约化为黎曼', '约化为 Dedekind %s(s) 的' % ZETA_K)
set_run_text(47, 3, '')
set_run_text(47, 4, '有限截断显式公式，导出实二次域 K=Q(√5) 的局部广义黎曼假设（K-GRH）；')

# T7 p53 sec 1.4
replace_in_run(53, 0, '迹等式约化为有限截断显式公式；零点临界线推论',
               '迹等式约化为 Dedekind %s(s) 的有限截断显式公式；%s 零点临界线推论' % (ZETA_K, ZETA_K))

# T8 p122 sec 5 heading
replace_in_run(122, 0, '5 测试函数选取与黎曼 ζ 零点临界推论',
               '5 测试函数选取与 Dedekind %s 零点临界推论' % ZETA_K)

# T9 p128 sec 5.2
replace_in_run(128, 1, '，定义 ζ 非平凡零点 ', '，定义 Dedekind %s 非平凡零点 ' % ZETA_K)

# T10 p145 conclusion 4
replace_in_run(145, 0, '约化为有限截断黎曼', '约化为有限截断 Dedekind %s(s)' % ZETA_K)
set_run_text(145, 1, '')
set_run_text(145, 2, '显式公式，得到实二次域 K=Q(√5) 的局部广义黎曼假设（K-GRH）。')

# T11 p193 appendix B step 5 heading
replace_in_run(193, 0, '步骤 5：衔接黎曼–冯', '步骤 5：衔接 Dedekind %s(s)' % ZETA_K)
set_run_text(193, 1, '')
set_run_text(193, 2, '显式公式的匹配推导')

# T12 p199 appendix B 5.1
replace_in_run(199, 1, '，定义黎曼 ζ 非平凡零点 ', '，定义 Dedekind %s 非平凡零点 ' % ZETA_K)

# T13 p204 appendix B 5.2 text
replace_in_run(204, 2,
    '，把素理想求和改写为按有理素分类的求和，再借助磨光测试函数取极限手续，匹配黎曼',
    '，把素理想求和改写为按分裂、惯性、分歧分类的加权求和（附录 D 结论，不可合并为有理素单层求和），再借助磨光测试函数取极限手续，匹配 Dedekind %s(s) 的' % ZETA_K)
set_run_text(204, 3, '')
set_run_text(204, 4, '显式公式标准结构：')

# T14 p206
replace_in_run(206, 1, ' 为冯', ' 为 K 的冯')

# T15 p212 appendix C
replace_in_run(212, 0, '进而约化至黎曼–冯', '进而约化至 Dedekind %s(s)' % ZETA_K)
set_run_text(212, 1, '')
set_run_text(212, 2, '显式公式的核心代数桥梁，所有步骤仅使用双曲函数初等恒等式与轨道')

# ---------- 2. OMML edits ----------
# M1 p12 English title: ζ(s) -> ζ_K(s)
om = omath_at(12)
zs = math_runs(om, 'ζ')
assert len(zs) == 1, 'p12 ζ runs: %d' % len(zs)
wrap_subscript(zs[0])
print('OMML p12: ζ -> ζ_K')

# M2 p29 abstract: ζ(s) -> ζ_K(s)
om = omath_at(29)
zs = math_runs(om, 'ζ')
assert len(zs) == 1, 'p29 ζ runs: %d' % len(zs)
wrap_subscript(zs[0])
print('OMML p29: ζ -> ζ_K')

# M3 p162 explicit formula: ρ -> ρ_K (x2), Λ -> Λ_K
om = omath_at(162)
for r in math_runs(om, 'ρ'):
    wrap_subscript(r)
for r in math_runs(om, 'Λ'):
    wrap_subscript(r)
print('OMML p162: ρ->ρ_K x2, Λ->Λ_K')

# M4 p205 explicit formula
om = omath_at(205)
for r in math_runs(om, 'ρ'):
    wrap_subscript(r)
for r in math_runs(om, 'Λ'):
    wrap_subscript(r)
print('OMML p205: ρ->ρ_K x2, Λ->Λ_K')

# M5 p206 Λ(n) -> Λ_K(n)
om = omath_at(206)
ls = math_runs(om, 'Λ')
assert len(ls) == 1, 'p206 Λ runs: %d' % len(ls)
wrap_subscript(ls[0])
print('OMML p206: Λ -> Λ_K')

d.save(PATH)
print('SAVED', PATH)
