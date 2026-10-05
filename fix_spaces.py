# -*- coding: utf-8 -*-
"""Fix 4 missing spaces at run joints; then verify oMath content."""
import docx
from docx.oxml.ns import qn

PATH = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(PATH)
paras = d.paragraphs

def set_run_text(p_idx, r_idx, new_text):
    p = paras[p_idx]
    runs = p._p.findall(qn('w:r'))
    t = runs[r_idx].find(qn('w:t'))
    t.text = new_text
    print('TXT p%d r%d -> %r' % (p_idx, r_idx, new_text))

# keyword: "Dedekind ζₖ 显式公式"
set_run_text(21, 3, ' 显式公式')
# conclusion 4
set_run_text(145, 2, ' 显式公式，得到实二次域 K=Q(√5) 的局部广义黎曼假设（K-GRH）。')
# appendix B step 5 heading
set_run_text(193, 2, ' 显式公式的匹配推导')
# appendix C
set_run_text(212, 2, ' 显式公式的核心代数桥梁，所有步骤仅使用双曲函数初等恒等式与轨道')

d.save(PATH)
print('SAVED')

# ---- verify OMML content ----
def omath_text(p_idx):
    p = paras[p_idx]
    om = p._p.find(qn('m:oMath'))
    if om is None:
        omp = p._p.find(qn('m:oMathPara'))
        if omp is not None:
            om = omp.find(qn('m:oMath'))
    if om is None:
        return '<none>'
    return ''.join(t.text or '' for t in om.iter(qn('m:t')))

for idx in (12, 29, 162, 205, 206):
    print('para %d oMath text: %s' % (idx, omath_text(idx)))
