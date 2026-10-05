# -*- coding: utf-8 -*-
"""Find m:oMathPara blocks and their paragraph indices."""
import docx
from docx.oxml.ns import qn

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)

for i, p in enumerate(d.paragraphs):
    omps = p._p.findall(qn('m:oMathPara'))
    if omps:
        for omp in omps:
            mtext = ''.join(t.text or '' for t in omp.iter(qn('m:t')))
            print('para %d oMathPara: %r' % (i, mtext))
# also scan any element tag with m:oMathPara at body level between paragraphs
body = d.element.body
for child in body.iterchildren():
    if child.tag == qn('m:oMathPara'):
        mtext = ''.join(t.text or '' for t in child.iter(qn('m:t')))
        print('BODY-LEVEL oMathPara: %r' % mtext)
