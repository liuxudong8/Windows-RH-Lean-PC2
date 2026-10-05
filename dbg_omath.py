# -*- coding: utf-8 -*-
import docx
from docx.oxml.ns import qn

path = r"c:\proj2\spectral_duality_v10_修改版.docx"
d = docx.Document(path)
p = d.paragraphs[12]
om = p._p.find(qn('m:oMath'))
print('om tag:', om.tag)
print('om children:', [c.tag for c in om])
zs = []
for r in om.iter(qn('m:r')):
    for t in r.iter(qn('m:t')):
        if (t.text or '') == 'ζ':
            zs.append(r)
            break
print('zs count:', len(zs))
for r in zs:
    print('m:r tag:', r.tag, 'parent tag:', r.getparent().tag, 'parent is om:', r.getparent() is om)
    print('m:r children:', [c.tag for c in r])
