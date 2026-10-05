# -*- coding: utf-8 -*-
"""Probe docx paragraph structure: index + text + oMath presence, for locating edit targets."""
import docx
from docx.oxml.ns import qn

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)

def para_text(p):
    # text of normal runs + oMath placeholder markers
    parts = []
    for child in p._p.iterchildren():
        tag = child.tag
        if tag == qn('w:r'):
            t = child.find(qn('w:t'))
            if t is not None and t.text:
                parts.append(t.text)
        elif tag == qn('m:oMath'):
            # extract text content inside oMath
            mtext = ''.join(t.text or '' for t in child.iter(qn('m:t')))
            parts.append('[MATH:' + mtext + ']')
        elif tag == qn('w:hyperlink'):
            for r in child.iter(qn('w:t')):
                if r.text:
                    parts.append(r.text)
    return ''.join(parts)

for i, p in enumerate(d.paragraphs):
    txt = para_text(p)
    if txt.strip():
        print(i, '|', txt[:120])
