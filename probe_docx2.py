# -*- coding: utf-8 -*-
"""Inspect run-level structure of target paragraphs and oMath XML."""
import docx
from docx.oxml.ns import qn
from lxml import etree

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)

def para_text_full(p):
    parts = []
    for child in p._p.iterchildren():
        tag = child.tag
        if tag == qn('w:r'):
            t = child.find(qn('w:t'))
            if t is not None and t.text:
                parts.append(t.text)
        elif tag == qn('m:oMath'):
            mtext = ''.join(t.text or '' for t in child.iter(qn('m:t')))
            parts.append('[MATH:' + mtext + ']')
        elif tag == qn('w:hyperlink'):
            for r in child.iter(qn('w:t')):
                if r.text:
                    parts.append(r.text)
    return ''.join(parts)

targets = [10, 12, 21, 29, 34, 47, 53, 122, 128, 129, 145, 193, 199, 204, 205, 206, 212]
for i, p in enumerate(d.paragraphs):
    if i in targets:
        print('==== para', i, '====')
        print(para_text_full(p))
        # count oMath and show XML of first oMath
        om = p._p.findall(qn('m:oMath'))
        print('  oMath count:', len(om))
        for j, o in enumerate(om):
            mtext = ''.join(t.text or '' for t in o.iter(qn('m:t')))
            print('  oMath[%d] text: %r' % (j, mtext))
        # show w:r texts
        for j, r in enumerate(p._p.findall(qn('w:r'))):
            t = r.find(qn('w:t'))
            print('  run[%d]: %r' % (j, t.text if t is not None and t.text else ''))
