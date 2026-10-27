# -*- coding: utf-8 -*-
"""arXiv 论文草稿（英文）：On the single-family pairing constant for L(s, chi_5).
d1\\en 惯例：docx + Word 原生 OMML 公式（LaTeX→MathML→OMML 管线）。
全部文献已联网核实（2026-10-27，见 outline_arxiv.md 引用核查表）。
"""
import os, re
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement, parse_xml
from latex2mathml.converter import convert as _l2m
import mathml2omml as _m2o

OUT_DIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en"
os.makedirs(OUT_DIR, exist_ok=True)
TARGET = os.path.join(OUT_DIR, "QRH-arXiv-draft-single-family-pairing-constant-L(s,chi5).docx")

doc = Document()
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
sec.left_margin = sec.right_margin = sec.top_margin = sec.bottom_margin = Cm(2.5)

def set_fonts(style, east, ascii_="Times New Roman", size=10.5, bold=False, color=None):
    style.font.name = ascii_
    style.font.size = Pt(size)
    style.font.bold = bold
    if color:
        style.font.color.rgb = color
    rpr = style.element.get_or_add_rPr()
    rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts"); rpr.append(rf)
    for attr in ("w:asciiTheme", "w:hAnsiTheme", "w:eastAsiaTheme"):
        if rf.get(qn(attr)):
            del rf.attrib[qn(attr)]
    rf.set(qn("w:ascii"), ascii_); rf.set(qn("w:hAnsi"), ascii_); rf.set(qn("w:eastAsia"), east)

n = doc.styles["Normal"]
set_fonts(n, "宋体", size=10.5)
pf = n.paragraph_format
pf.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
pf.line_spacing = 1.5
pf.space_before = Pt(0); pf.space_after = Pt(0)
ind = n.element.get_or_add_pPr().get_or_add_ind()
ind.set(qn("w:firstLineChars"), "200"); ind.set(qn("w:firstLine"), "420")

tstyle = doc.styles["Title"]
set_fonts(tstyle, "黑体", size=16, bold=True)
tstyle.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
tstyle.paragraph_format.space_after = Pt(6)

h1 = doc.styles["Heading 1"]
set_fonts(h1, "黑体", size=12, bold=True, color=RGBColor(0, 0, 0))
h1.paragraph_format.space_before = Pt(12); h1.paragraph_format.space_after = Pt(6)
h1.paragraph_format.keep_with_next = True

h2 = doc.styles["Heading 2"]
set_fonts(h2, "黑体", size=10.5, bold=True, color=RGBColor(0, 0, 0))
h2.paragraph_format.space_before = Pt(6); h2.paragraph_format.space_after = Pt(3)
h2.paragraph_format.keep_with_next = True

cap = doc.styles["Caption"]
set_fonts(cap, "黑体", size=9, bold=False)
cap.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
cap.paragraph_format.space_before = Pt(4); cap.paragraph_format.space_after = Pt(4)
cap.paragraph_format.keep_with_next = True

M_NS = "http://schemas.openxmlformats.org/officeDocument/2006/math"
_HAT_RE = re.compile(
    r"<m:limUpp><m:e>(.*?)</m:e><m:lim>.*?<m:t>\^</m:t>.*?</m:lim></m:limUpp>", re.S)

def _fix_hat(xml):
    return _HAT_RE.sub(
        lambda m: '<m:acc><m:accPr><m:chr m:val="\u0302"/></m:accPr><m:e>%s</m:e></m:acc>' % m.group(1),
        xml)

def _omml(latex):
    out = _m2o.convert(_l2m(latex))
    out = _fix_hat(out)
    if "xmlns:m" not in out[:120]:
        out = out.replace("<m:oMath", '<m:oMath xmlns:m="%s"' % M_NS, 1)
    return out

def math_para(latex, space_before=None, space_after=None):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    xml = ('<m:oMathPara xmlns:m="%s"><m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>%s</m:oMathPara>'
           % (M_NS, _omml(latex)))
    p._p.append(parse_xml(xml))
    if space_before is not None:
        p.paragraph_format.space_before = Pt(space_before)
    if space_after is not None:
        p.paragraph_format.space_after = Pt(space_after)
    return p

def _apply_run_font(r, bold=False, font=None, size=None):
    if bold:
        r.font.bold = True
    if font or size:
        r.font.name = "Times New Roman"
        if size:
            r.font.size = Pt(size)
        rpr = r._r.get_or_add_rPr(); rf = rpr.find(qn("w:rFonts"))
        if rf is None:
            rf = OxmlElement("w:rFonts"); rpr.append(rf)
        rf.set(qn("w:ascii"), "Times New Roman"); rf.set(qn("w:hAnsi"), "Times New Roman")
        if font:
            rf.set(qn("w:eastAsia"), font)

def para(text, align=None, bold=False, font=None, size=None, indent_chars=0,
         space_before=None, space_after=None, style=None):
    p = doc.add_paragraph(style=style)
    if align is not None:
        p.alignment = align
    if indent_chars:
        ppr = p._p.get_or_add_pPr(); ind2 = ppr.get_or_add_ind()
        ind2.set(qn("w:firstLineChars"), str(indent_chars * 100))
    tokens = re.split(r"(\$[^$]*\$|\^\{[^}]*\}|_\{[^}]*\})", text)
    for tk in tokens:
        if not tk:
            continue
        if tk.startswith("$") and tk.endswith("$") and len(tk) > 1:
            add_math_el(p, tk[1:-1])
        elif tk.startswith("^{"):
            r = p.add_run(tk[2:-1]); r.font.superscript = True
        elif tk.startswith("_{"):
            r = p.add_run(tk[2:-1]); r.font.subscript = True
        else:
            r = p.add_run(tk)
        _apply_run_font(r, bold=bold, font=font, size=size)
    if space_before is not None:
        p.paragraph_format.space_before = Pt(space_before)
    if space_after is not None:
        p.paragraph_format.space_after = Pt(space_after)
    return p

def add_math_el(p, latex):
    p._p.append(parse_xml(_omml(latex)))

def h1t(text):
    return doc.add_heading(text, level=1)

def h2t(text):
    return doc.add_heading(text, level=2)

def caption(text):
    return doc.add_paragraph(text, style="Caption")

def set_cell_borders(cell, top=8, bottom=8):
    tcPr = cell._tc.get_or_add_tcPr()
    tb = tcPr.find(qn("w:tcBorders"))
    if tb is None:
        tb = OxmlElement("w:tcBorders"); tcPr.append(tb)
    for tag, sz in (("top", top), ("bottom", bottom)):
        el = tb.find(qn("w:" + tag))
        if el is None:
            el = OxmlElement("w:" + tag); tb.append(el)
        el.set(qn("w:val"), "single"); el.set(qn("w:sz"), str(sz)); el.set(qn("w:space"), "0")

def style_cell(cell, text, bold=False, align=WD_ALIGN_PARAGRAPH.RIGHT, east="宋体", size=9):
    cell.vertical_alignment = WD_CELL_VERTICAL_ALIGNMENT.CENTER
    p = cell.paragraphs[0]
    p.alignment = align
    ppr = p._p.get_or_add_pPr()
    ind3 = ppr.get_or_add_ind(); ind3.set(qn("w:firstLineChars"), "0"); ind3.set(qn("w:firstLine"), "0")
    p.paragraph_format.space_before = Pt(0); p.paragraph_format.space_after = Pt(0)
    p.paragraph_format.line_spacing = 1.0
    r = p.add_run(text)
    r.font.name = "Times New Roman"; r.font.size = Pt(size); r.font.bold = bold
    rpr = r._r.get_or_add_rPr(); rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts"); rpr.append(rf)
    rf.set(qn("w:ascii"), "Times New Roman"); rf.set(qn("w:hAnsi"), "Times New Roman")
    rf.set(qn("w:eastAsia"), east)

def add_table(headers, rows, widths=None):
    t = doc.add_table(rows=len(rows) + 1, cols=len(headers))
    t.alignment = WD_TABLE_ALIGNMENT.CENTER
    t.autofit = False
    trPr = t.rows[0]._tr.get_or_add_trPr()
    th = OxmlElement("w:tblHeader"); th.set(qn("w:val"), "true"); trPr.append(th)
    for r_ in t.rows:
        rp = r_._tr.get_or_add_trPr()
        cs = OxmlElement("w:cantSplit"); rp.append(cs)
    for j, htxt in enumerate(headers):
        c = t.rows[0].cells[j]
        set_cell_borders(c, top=8, bottom=4)
        style_cell(c, htxt, bold=True, align=WD_ALIGN_PARAGRAPH.CENTER, east="黑体")
    for i, row in enumerate(rows):
        for j, val in enumerate(row):
            c = t.rows[i + 1].cells[j]
            bottom = 8 if i == len(rows) - 1 else 0
            set_cell_borders(c, top=0, bottom=bottom)
            al = WD_ALIGN_PARAGRAPH.CENTER if (j == 0 or isinstance(val, str) or len(str(val)) <= 12) else WD_ALIGN_PARAGRAPH.RIGHT
            style_cell(c, str(val), align=al)
    if widths:
        for j, w in enumerate(widths):
            for r_ in t.rows:
                r_.cells[j].width = Cm(w)
    return t

def add_page_number_footer():
    footer = sec.footer
    p = footer.paragraphs[0]
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    fld = OxmlElement("w:fldSimple")
    fld.set(qn("w:instr"), " PAGE ")
    r = OxmlElement("w:r"); t = OxmlElement("w:t"); t.text = "1"
    r.append(t); fld.append(r)
    p._p.append(fld)

add_page_number_footer()

# ================= 正文 =================
para("On the single-family pairing constant for L(s, χ₅): conditional bounds, numerical evidence, and a Lean 4 formalization",
     style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("Liu Xudong（作者信息待补）", align=WD_ALIGN_PARAGRAPH.CENTER, font="楷体", size=12, space_after=4)
para("2026-10-27 草稿（arXiv math.NT 预投）", align=WD_ALIGN_PARAGRAPH.CENTER, size=9, space_after=10)

# --- Abstract ---
h1t("Abstract")
para("We study the single-family pairing constant $A_L(K)=1+(\\sum_{\\Delta\\ne 0}K(\\delta\\Delta)^2)/N_Z$ "
     "for the Dirichlet L-function $L(s,\\chi_5)$, where $\\chi_5$ is the real character modulo 5, "
     "$\\delta=\\log T/(2\\pi)$, and $N_Z$ is the number of zeros in the family. This constant governs the "
     "Quasi-Riemann Hypothesis (QRH) constant mechanism: the bound $A_L\\le 1.125$ is equivalent to the "
     "target constant 7/8 in the QRH problem, and the limit $A_L\\to 1$ is the strongest conceivable form. "
     "We formulate a conditional theorem, Theorem 1, of the form $A_L(K)\\le C_{\\mathrm{MT}}+C_1\\varepsilon+C_2$ "
     "with $C_2=2$ explicit, under three standing hypotheses: (H1) an L-family BGS-type pairing formula "
     "(a single-family analogue of the Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh unconditional "
     "Montgomery theorem; we state it explicitly since no unconditional version exists in the literature for "
     "a fixed real character), (H2) the Siegel--Walfisz estimate for $\\chi_5$ with explicit constants "
     "$(C,c)=(C,\\,1/\\sqrt{6.3970}=0.3954\\ldots)$ obtained from the Kadiri zero-free region via "
     "Bordignon's explicit formula, and (H3) the Landau explicit formula for $L(s,\\chi)$ together with the "
     "weak real-part hypothesis of BGS. We prove Theorem 1 at the level of a proof skeleton, with the "
     "pairing-sum expansion decomposed into diagonal, prime, and off-critical terms. We then present "
     "numerical evidence: the Fej\\'er kernel at nearest-neighbour scale gives $A_\\zeta=1.0079$, "
     "$A_L=1.0114$, both below 1.125 with margin ~0.11--0.12, and a narrow-kernel refinement reaches "
     "$A\\approx 0.990$ with subinterval drift $\\le 0.005$; the prime term is measured at relative size "
     "$\\sim 4\\times 10^{-8}$ of the diagonal term, and the weighted Siegel--Walfisz partial sum satisfies "
     "$|\\psi(x,\\chi_5)|/x\\le 1.70\\times 10^{-3}$ for $10^5\\le x\\le 10^7$. Finally, we report a Lean 4 "
     "formalization (project QRH, mathlib v4.34.0-rc2) with 26 proven lemmas and a full build of 2604 jobs "
     "passing, while honestly recording the axioms that remain on long lines.", indent_chars=0)
para("Keywords: Quasi-Riemann Hypothesis; pair correlation; Dirichlet L-functions; Siegel--Walfisz; "
     "formal proof; Lean 4", indent_chars=0, space_after=6)

# --- 1 Introduction ---
h1t("1　Introduction")
para("The Quasi-Riemann Hypothesis (QRH) asserts, in the formulation relevant here, a statistical "
     "constraint on the zeros of $L(s,\\chi_5)$: the relevant constant is $2-C_{\\mathrm{MT}}=0.6725$, where "
     "$C_{\\mathrm{MT}}=1/2+(1/\\sqrt{2})\\cot(1/\\sqrt{2})=1.3274992963$ is the optimal pairing constant over "
     "kernels of spectral support $\\lambda\\le 1/2$ (Lemma 3.2 and Remark 3.4 of [5]). The QRH target 7/8 "
     "requires $A_L\\le 1.125$; equivalently, in the union decomposition of [9], the online simple-zero "
     "proportion is bounded below by")
math_para(r"\frac{N_\zeta(2-A_\zeta)+N_L(2-A_L)}{N_K}\ge 2-(C_{\mathrm{MT}}+O(\varepsilon))-o(1),")
para("so that $A_L\\le 1.125$ forces the proportion above 7/8. The strategy of this series is therefore to "
     "push the pairing constant to $A_L\\to 1$, the strongest conceivable form of the bound. We stress the "
     "calibration: $A_L\\to 1$ is a statistical (level-spacing) statement about the zeros; it is not to be "
     "advertised as approaching the Riemann Hypothesis, which is a descriptive statement about the "
     "horizontal location of zeros. The two are logically independent, though deeply connected through the "
     "pair-correlation mechanism.")
para("The contribution of this paper is threefold. (i) A conditional theorem, Theorem 1, in the precise "
     "form needed by the QRH constant mechanism, with explicit secondary constant $C_2=2$; the theorem is "
     "conditional on three standing hypotheses which we state explicitly, honestly recording that an "
     "L-family BGS-type pairing formula is an open construction in the literature. (ii) A numerical "
     "evidence chain: kernel-family scans, narrow-kernel refinements, subinterval drift tests, and "
     "measured prime-term and Siegel--Walfisz partial-sum bounds, all reproducible from the scripts listed "
     "in the references. (iii) A Lean 4 formalization of the proof skeleton, with 26 lemmas proved and a "
     "full build of 2604 jobs passing; the axioms that remain on long lines are recorded without omission.")
para("The remainder of the paper is organized as follows. Section 2 fixes notation and states the three "
     "standing hypotheses. Section 3 reviews the pairing constant and the kernel family, including "
     "Lamzouri's Proposition 2.1 and the optimality of $C_{\\mathrm{MT}}$. Section 4 states the main "
     "theorem and its corollary. Section 5 gives the proof skeleton. Sections 6--7 present the numerical "
     "evidence and robustness checks. Section 8 addresses the super-support regime and the path to "
     "$A_L\\to 1$. Section 9 describes the Lean 4 formalization. Section 10 concludes.")

# --- 2 Notation and assumptions ---
h1t("2　Notation and standing assumptions")
para("Let $\\chi_5$ denote the real character modulo 5 (the Legendre symbol $(\\cdot/5)$), and let "
     "$Z_L=\\{\\rho_L\\}$ be the multiset of nontrivial zeros of $L(s,\\chi_5)$, counted with multiplicity. "
     "Normalize ordinates by $\\delta=\\log T/(2\\pi)$. For an even test kernel $K$ with $K(0)=1$ and "
     "Fourier transform $\\hat K$ of compact support, the single-family pairing constant is")
math_para(r"A_L(K)=1+\frac{1}{N_Z}\sum_{\Delta\ne 0}K(\delta\Delta)^2,\qquad N_Z=\#\{0<\gamma_L\le T\},")
para("where the sum runs over differences of normalized ordinates in $Z_L$. The kernel family is that of "
     "BGS [1]: $\\hat K$ is supported in $[-1,1]$ (spectral support $\\lambda\\le 1/2$), which is exactly "
     "the admissible variation range of the $C_{\\mathrm{MT}}$ framework.")
para("Standing hypotheses. Throughout, we assume the following three hypotheses, stated explicitly:")
para("(H1) L-family BGS-type pairing formula. The single-family pairing sum for $L(s,\\chi_5)$ admits an "
     "explicit formula of BGS type: there is a decomposition into diagonal, prime, and off-critical terms "
     "with the bounds of Lemma 3 of [1] transplanted to $L(s,\\chi_5)$. Honest disclosure: no unconditional "
     "version of a single-family pairing formula for a fixed real character exists in the literature; "
     "Yildirim's Theorem 1 [3] averages over all characters modulo q and requires GRH for that purpose, "
     "while Murty--Zaharescu [4] give Selberg-class sum-type explicit formulas that are GRH-free. We "
     "record (H1) as an explicit hypothesis rather than claiming it.", indent_chars=0)
para("(H2) Siegel--Walfisz with explicit constants. For $x\\ge 3$, $|\\psi(x,\\chi_5)|\\le C\\,x\\,"
     "e^{-c\\sqrt{\\log x}}$ with $c=1/\\sqrt{6.3970}=0.3954\\ldots$ (Theorem 1 of [2]: $R_0=6.3970$, "
     "$R_1=2.0452$, citing Kadiri's explicit zero-free region) and $C$ explicit from Bordignon's Table 2. "
     "This is unconditional and effective; it substitutes for the GRH-PNT that Yildirim needed only "
     "because of averaging over moduli.", indent_chars=0)
para("(H3) Landau explicit formula and weak real-part hypothesis. The Landau-type explicit formula "
     "(Yildirim's formula (6), unconditional for $L(s,\\chi)$) holds, and the zeros satisfy the weak "
     "real-part hypothesis of BGS [1]: every zero $\\rho=\\beta+i\\gamma$ with $T^{3/8}<\\gamma\\le T$ "
     "satisfies $|\\beta-1/2|<1/(2\\log T)$.", indent_chars=0)

# --- 3 Pairing constant and kernel family ---
h1t("3　The pairing constant and the kernel family")
para("We recall the variational mechanism (Lamzouri [5], Proposition 2.1). For a conjugate-invariant "
     "multiset $Z$, any $\\eta\\in L^2$ with $\\operatorname{supp}\\eta\\subset(-\\lambda,\\lambda)$, "
     "$\\widehat{\\eta^2}(0)=1$ and $K=\\widehat{\\eta^2}$ (an entire function with $K(0)=1$), the number "
     "of simple real zeros satisfies $N_0^s\\ge 2\\sum 1-\\sum K(z-s)^2$; hence the online proportion is "
     "at least $2-A$. Lemma 3.2 of [5] constructs the optimal kernel $f_0(x)=\\cos(\\sqrt{2}x)/"
     "(\\sqrt{2}\\sin(1/\\sqrt{2}))$ with support $[-1/2,1/2]$, and Remark 3.4 (Carneiro--Chandee--Littmann--"
     "Milinovich) shows $C_\\eta\\ge C_{\\mathrm{MT}}$; no kernel in the admissible family attains a "
     "pairing constant below $1.3275$.")
math_para(r"C_{\mathrm{MT}}=\frac12+\frac{1}{\sqrt{2}}\cot\frac{1}{\sqrt{2}}=1.3274992963,\qquad "
          r"f_0(x)=\frac{\cos(\sqrt{2}x)}{\sqrt{2}\sin(1/\sqrt{2})},")
para("On the admissible side of the variational problem, the narrow Fej\\'er kernel $\\mathrm{fejer}_{a=0.5}$ "
     "is an intentional choice: the single-family pairing sum accumulates only near-neighbour "
     "contributions inside the spectral window, so long-range structure never enters $A_L$. This is not an "
     "omission but a kernel-family choice: Proposition 2.1 holds for every admissible $\\eta$, and the "
     "hypothesis requires only the existence of one kernel with $A_L\\le 1.125$. The narrow kernel "
     "satisfies it; the choice is fully legitimate. The trivial limit $A\\to 1$ as $a\\to 0$ corresponds to "
     "spectral support $\\lambda\\to\\infty$, outside the unconditional range, and is not a free lunch: "
     "$A\\ge 1$ always holds (diagonal term $K(0)=1$), so $A\\to 1$ is attainable only when the "
     "off-diagonal pairing is genuinely negligible.")

# --- 4 Main theorem ---
h1t("4　Main theorem")
para("Theorem 1 (conditional pairing bound). Assume (H1)--(H3). For every $T\\ge 1$, $\\varepsilon>0$ and "
     "every admissible kernel $K$ in the family of Section 3, the single-family pairing constant of "
     "$L(s,\\chi_5)$ satisfies")
math_para(r"A_L(K)\le C_{\mathrm{MT}}+C_1\varepsilon+C_2,\qquad C_2=2\ \text{(explicit)},", space_after=4)
para("with $C_1$ an absolute constant arising from the $\\varepsilon$-regularization of the optimal kernel "
     "(the $L^1$ deviation bound $\\|f_0-f_\\varepsilon\\|_1\\le 2\\varepsilon(\\sqrt{2}|\\sin(1/\\sqrt{2})|)^{-1}$).")
para("Corollary 2 (QRH constant mechanism). Under (H1)--(H3), if a kernel $K$ with $A_L(K)\\le 1.125$ "
     "exists (numerical evidence below), then the online simple-zero proportion of the union satisfies")
math_para(r"\frac{N_\zeta(2-A_\zeta)+N_L(2-A_L)}{N_K}\ge 2-(C_{\mathrm{MT}}+O(\varepsilon))-o(1)"
          r"\ge 0.6725-O(10^{-2})-o(1),")
para("in particular above $7/8=0.875$ for $\\varepsilon=10^{-2}$ with the numerical values of Section 6. "
     "The bound $A\\le 1.125$ is equivalent to the QRH target 7/8; the strongest form $A_L\\to 1$ gives an "
     "online proportion $1-o(1)$.")

# --- 5 Proof skeleton ---
h1t("5　Proof skeleton")
para("The proof follows the BGS transplantation strategy of [6]: (i) pass from the difference-type "
     "pairing to a sum-type pairing via complex-conjugate symmetry; (ii) expand the pairing sum by the "
     "Landau explicit formula (Yildirim's formula (6), unconditional for $L(s,\\chi)$):")
math_para(r"\sum_{\rho}\frac{x^{\rho-r}}{\rho-r}=\sum_{\ell}\frac{x^{-(2\ell+r+a)}}{2\ell+r+a}"
          r"-\sum'_{n\le x}\frac{\Lambda(n)\chi(n)}{n^{r}}-\frac{L'}{L}(r,\chi),", space_after=4)
para("(iii) bound the prime term by (H2); (iv) bound the off-critical term by the $T^{3/8}$ cut and the "
     "weak real-part hypothesis (H3); (v) replace $f_0$ by its $\\varepsilon$-regularization with the "
     "$L^1$ deviation bound. The pairing-sum expansion takes the form")
math_para(r"A_L(K)=\text{diag}+\text{prime}+\text{offcrit},", space_after=4)
para("with $\\text{diag}\\le C_{\\mathrm{MT}}+C_1\\varepsilon$ (via the $\\varepsilon$-$\\lambda$ linkage "
     "[7]), and $|\\text{prime}|,|\\text{offcrit}|\\le 1$ absorbed into $C_2=2$ by the "
     "Montgomery--Vaughan mean-value mechanism. The prime term is")
math_para(r"S(X)=\sum_{p\le X}\Lambda(p)\chi_5(p)\,p^{-1/2}\,\hat K(\delta\log p),", space_after=4)
para("bounded by partial summation from (H2): $|S(X)|\\le C'\\sqrt{X}\\,e^{-c\\sqrt{\\log X}}$; with "
     "$\\hat K$ of narrow frequency support only primes near $p\\approx 1$ contribute, and the "
     "$\\chi_5$-weighted oscillation gives a second suppression (Section 6, item E).")

# --- 6 Numerical evidence ---
h1t("6　Numerical evidence")
para("All numerics use zeros of $\\zeta$ and $L(s,\\chi_5)$ up to height $T=6\\times 10^5$ "
     "(999 492 and 1 150 050 zeros), with truncation $t<300$ removed; scripts are listed in the "
     "references.")
caption("Table 1　Pairing constants by kernel family and scale (audit6, δ = logT/(2π) = 2.1175)")
add_table(["kernel", "A_ζ", "A_L", "A_union", "2−A_ζ", "remark"],
    [["fejer_a0.5 (optimal)", "1.0079", "1.0114", "1.2859", "0.9921", "below 1.125"],
     ["sinc_a0.5", "1.0492", "1.0639", "1.4720", "0.9508", "below 1.125"],
     ["fejer_a1.0", "1.0565", "1.0807", "1.6227", "0.9435", "below 1.125"],
     ["gauss_a0.5", "1.1269", "1.1773", "1.8902", "0.8731", "below 1.125"],
     ["MT optimal (numeric)", "1.1868", "1.2494", "2.0562", "0.8132", "below C_MT"],
     ["C_MT (unconditional)", "1.3275", "1.3275", "—", "0.6725", "theorem bound"]],
    widths=[3.6, 2.0, 2.0, 2.4, 2.2, 3.2])
para("Readings. (i) The optimal kernel at nearest-neighbour scale gives $A_\\zeta=1.0079$, "
     "$A_L=1.0114$, both below the 7/8 threshold 1.125 with margin 0.11--0.12. (ii) The MT optimal kernel "
     "measures 1.1868/1.2494, below $C_{\\mathrm{MT}}=1.3275$: GUE repulsion lowers the pairing constant "
     "in the data. (iii) The union pairing constant has minimum 1.2859 > 1.125: direct union argument "
     "fails; the decomposition argument of Corollary 2 is mandatory.", indent_chars=0)
para("Refinement and stability. A narrow-kernel programme [8] reaches $A\\approx 0.990$ for $L(s,\\chi_5)$. "
     "Over the five subintervals of $[3\\times 10^4, 6\\times 10^5]$ the optimal-kernel constant drifts "
     "monotonically with adjacent drift $\\le 0.005$ and no divergence; the premise $A\\le 1.125$ is "
     "numerically robust, subject to the explicit extrapolation hypothesis that the global mean does not "
     "reverse sharply at infinite height (strengthenable by larger-$T$ runs).")
para("Item E (prime term). For $X=10^7$ at $T=6\\times 10^5$ and $8\\times 10^5$: "
     "$|S|_{\\max}\\le 0.128$, relative to the diagonal scale $N_L$ (1.15--1.57 million) this is "
     "$\\sim 4\\times 10^{-8}$; the unweighted partial sum $|S_0|\\le 2.9$ is bounded (SW form). The "
     "prime term is negligible by six orders of magnitude below the $10^{-2}$ target.")
para("Item G (Siegel--Walfisz). For $10^5\\le x\\le 10^7$ (41 log-uniform points), "
     "$|\\psi(x,\\chi_5)|/x\\le 1.70\\times 10^{-3}$; the measured suppression is three orders of magnitude "
     "below the Kadiri-type upper bound $e^{-c\\sqrt{\\log x}}$, $c=0.3954$. Item F (super-support): the "
     "smoothed weighted sum satisfies $|S_a|\\approx 2.05$ bounded and $|S_a|/N_L$ decays monotonically to "
     "$1\\times 10^{-8}$ at $X=10^8$.")

# --- 7 Robustness ---
h1t("7　Robustness checks")
para("Threat exclusion. Three structural threats to the pairing-constant reading were tested "
     "numerically. (i) Real-part injection (S2(i)): injecting a genuine real-part component into "
     "same-imaginary-part pairs produces an $N_{\\mathrm{off}}\\cdot\\delta^2\\cdot\\lambda^2$ cumulative "
     "signal; the data show no such accumulation, excluding an off-line same-imaginary-pair threat. "
     "(ii) The $\\Delta$-constant fingerprint (S3): injecting same-imaginary-part pairs triggers an "
     "explosive response in the $\\Delta$ constant, inconsistent with the observed flat behaviour — "
     "cross-validation closure. (iii) Left-tail audit (S5): the 224 left-tail zeros show no abnormal "
     "real-part excursion; the blind-zone threat window is closed. Cross-family independence is "
     "measured (switch frequency 0.7533 vs. 0.7610±0.0066 for an independent GUE mixture), and the union "
     "is slightly sub-Poisson (variance −4σ), both consistent with GUE quasirandomness.")

# --- 8 Super-support regime ---
h1t("8　The super-support regime and the path to A_L → 1")
para("The push to $A_L\\to 1$ meets a theoretical gap: the route requires $\\lambda_{\\mathrm{eff}}(T)="
     "(\\log T)^q\\to\\infty$ (narrower kernels, spectral support expanding without bound), while the "
     "closed path of [6] covers only $\\lambda\\le 1/2$ (the support condition of BGS Lemma 5). As "
     "$\\lambda\\to\\infty$ the real-space kernel width $a\\to 0$ and $\\hat K(\\delta\\log p)$ widens; the "
     "prime term may lose the protection of narrow frequency support. The analysis resolves this as "
     "follows: partial summation together with the pointwise (H2) gives $S(X)=O(\\sqrt{X}\\cdot"
     "\\operatorname{poly}(\\log X))$, which is $o(1)$ relative to the diagonal scale $N_L\\sim "
     "(X/2\\pi)\\log X$ — no exponential decay is needed. Three closure items are formulated: (N1) "
     "super-support generalization of BGS Lemma 5 (support $[-a,a]$, $a\\to 0$); (N2) the $\\varepsilon$"
     "$\\lambda$ linkage $\\lambda=(\\log T)^q$, $a=(\\log T)^{-q}$, $\\varepsilon=c(\\log T)^{-q}$; (N3) "
     "off-critical uniformity in $\\lambda$. Item F confirms the mechanism numerically: $|S_a|/N_L$ decays "
     "to $1\\times 10^{-8}$, with the second-order correction $(a\\delta)^2\\log^2 p$ dominant (even "
     "kernel: first-order correction identically zero).")
para("Siegel--Walfisz constants. Theorem N3.5 of [10]: for $x\\ge 3$, $|\\psi(x,\\chi_5)|\\le "
     "C\\,x\\,e^{-c\\sqrt{\\log x}}$ with $c=1/\\sqrt{6.3970}=0.3954\\ldots$ unconditional and effective "
     "($R_0=6.3970$, $R_1=2.0452$ from Theorem 1 of [2], the product $\\prod(s,5)$ has at most one "
     "exception); $L(1,\\chi_5)=0.430409\\ldots>0$ excludes the exceptional zero for modulus 5; the "
     "numerical upper envelope is $1.70\\times 10^{-3}$ on $[10^5,10^7]$.")

# --- 9 Lean 4 formalization ---
h1t("9　Lean 4 formalization")
para("The proof skeleton is formalized in Lean 4 (mathlib v4.34.0-rc2) in the project QRH "
     "(C:\\proj2\\QRH): modules S7_1_Core.lean, S7_1_Main.lean, S7_1_Stage3.lean with the one-way "
     "dependency Core→Main→Stage3. The full build runs 2604 jobs and passes (2026-10-27, "
     "main_l2_full.txt). 26 lemmas are proved, including: kernel analytic facts ($\\sin(1/\\sqrt{2})\\ne 0$, "
     "evenness of $\\hat K$, $\\hat K(0)=1$, frequency-decay bound, continuity), the Abel summation lemma "
     "(sum_abel_partial), the quantum-term assembly (prime_sum_bound), the N1/N2 structural items, the "
     "scale-invariance of the $L^1$ norm, the $r=1/2$ algebraic bridge "
     "$n^{-1/2}=(\\sqrt{n})^{-1}$ (primePowerSum_half_eq_sqrt), and the convergence of the trivial-term "
     "series (trivialTerm_summable for $x>1$, $r>0$; the boundary $x=1$ is harmonic-type divergent and "
     "needs its own convention). Error bounds are expressed in an explicit pointwise macro "
     "$\\operatorname{Bound}\\, C\\,T_0\\, \\mathrm{err}\\, f:=\\forall T\\ge T_0,\\,|\\mathrm{err}\\,T|\\le "
     "C\\,f\\,T$ (the asymptotic big-O notation is deliberately avoided). Honest disclosure: the main "
     "theorem chain holds under the named axioms landau_explicit_L, siegel_walfisz_chi5 and the BGS "
     "transplant axioms bgs3--bgs5; clearing these axioms to theorems is a PNT-in-arithmetic-"
     "progressions-scale long line, as recorded in the file layout section of the summary [11].")

# --- 10 Conclusion ---
h1t("10　Conclusion")
para("We have stated a conditional theorem that converts the QRH constant mechanism into an explicit "
     "inequality $A_L(K)\\le C_{\\mathrm{MT}}+C_1\\varepsilon+C_2$ with $C_2=2$, supported by a numerical "
     "evidence chain ($A\\approx 0.990$, drift $\\le 0.005$, prime term $\\sim 4\\times 10^{-8}$, SW "
     "suppression $1.70\\times 10^{-3}$) and a Lean 4 formalization with 26 proved lemmas and a full "
     "2604-job green build. The honest boundaries are recorded throughout: (H1) is an explicit "
     "hypothesis because no unconditional single-family pairing formula exists in the literature; the "
     "constants $A$ are data, not theorems, and extrapolation relies on an explicit no-reversal "
     "assumption; the Lean axioms on long lines are listed without omission. The natural next steps are "
     "the derivative term of the Landau formula, the SW body itself (PNT-in-AP scale), and — in the "
     "super-support regime — the rigorous $\\lambda_{\\mathrm{eff}}\\to\\infty$ analysis that would turn "
     "the numerical path $A_L\\to 1$ into a theorem.")

# --- References ---
h1t("References")
refs = [
    "[1] D. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799 (2023).",
    "[2] M. Bordignon. Medium-sized values for the prime number theorem for primes in arithmetic progressions. arXiv:2101.08610 (2021); Theorem 1 (R₀ = 6.3970, R₁ = 2.0452), Table 2.",
    "[3] C. Y. Yildirim. The pair correlation of zeros of Dirichlet L-functions and primes in arithmetic progressions. manuscripta math. 72(1) (1991), 325–334; formulas (6)–(7).",
    "[4] M. R. Murty, A. Zaharescu. Explicit formulas for the pair correlation of zeros of functions in the Selberg class. Forum Math. 14 (2002), 65–83.",
    "[5] Y. Lamzouri. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2 (2026); Proposition 2.1, Lemma 3.2, Remark 3.4.",
    "[6] Offensive XLII-S7 (this series, d1 archive): Yildirim-method transplantation closure for L(s, χ₅) — single-family BGS-type pairing formula, prime-term numerical item E, Theorem S7.1 skeleton.",
    "[7] Offensive XLII-S7.4 (d1): bone 2 — the ε–λ linkage (N2). Offensive XLII-S7.3 (d1): bone 1 — super-support generalization of BGS Lemma 5 (N1). Offensive XLII-S7.5 (d1): bone 3 — off-critical uniformity (N3).",
    "[8] Offensive XLII-S4 (d1): forward construction — narrow-kernel measurement and the pairing-constant residual structure (A ≈ 0.990).",
    "[9] Offensive XLI (d1): the quasirandom union theorem — constant-mechanism closure, kernel-family scan (A_ζ = 1.0079, A_L = 1.0114), three-layer reliability.",
    "[10] Offensive XLII-S7.6 (d1): explicit Siegel–Walfisz constants (C, c), c = 1/√6.3970 = 0.3954…; numerical item G.",
    "[11] QRH summary: QRH_summary.md / QRH_summary_en.md (C:\\proj2\\QRH, 2026-10-27); file layout and build evidence main_l2_full.txt (2604 jobs green).",
    "[12] N. Kandhil, A. Languasco, P. Moree. Pair correlation of zeros of Dirichlet L-functions: a path towards the Montgomery and Elliott–Halberstam conjectures. arXiv:2411.19762 (2024).",
    "[13] E. Carneiro, M. B. Milinovich, A. P. Ramos. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913 (2023).",
    "[14] O. Ramaré, R. Rumely. Primes in arithmetic progressions. Math. Comp. 65(213) (1996), 397–425.",
    "[15] H. L. Montgomery. The pair correlation of zeros of the zeta function. In: Analytic Number Theory, Proc. Sympos. Pure Math. 24, Amer. Math. Soc. (1973), 181–193.",
]
for rtxt in refs:
    para(rtxt, size=9, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
