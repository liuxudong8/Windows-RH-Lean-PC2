# -*- coding: utf-8 -*-
"""Dump p162 oMathPara XML to confirm structure."""
import docx
from docx.oxml.ns import qn
from lxml import etree

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)
p = d.paragraphs[162]
omps = p._p.findall(qn('m:oMathPara'))
for omp in omps:
    print(etree.tostring(omp, pretty_print=True).decode('utf-8'))
