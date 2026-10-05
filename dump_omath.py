# -*- coding: utf-8 -*-
"""Dump full XML of target oMath elements."""
import docx
from docx.oxml.ns import qn
from lxml import etree

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)

targets = {12: [0], 29: [0], 205: [0], 206: [0]}
for i, p in enumerate(d.paragraphs):
    if i in targets:
        om = p._p.findall(qn('m:oMath'))
        for j in targets[i]:
            if j < len(om):
                print('==== para %d oMath[%d] ====' % (i, j))
                print(etree.tostring(om[j], pretty_print=True).decode('utf-8'))
