# -*- coding: utf-8 -*-
"""攻防 XLII S0 数值定向落档——英文版（d1\\en）。忠实翻译中文版。"""
import json
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
WORK = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xlii_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\en\路2攻防XLII-全尺度GUE配对与在线比例1-o(1)-S0数值定向-口径修正与超GUE排斥-EN.docx"

v3 = json.load(open(QRH + r"\xlii_s0_v3.json", encoding="utf-8"))
gue = json.load(open(QRH + r"\xlii_s0_gue_sim.json", encoding="utf-8"))

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
set_fonts(cap, "黑体", size=9)
cap.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
cap.paragraph_format.space_before = Pt(4); cap.paragraph_format.space_after = Pt(4)
cap.paragraph_format.keep_with_next = True

def para(text, style=None, align=None, bold=False, font=None, size=None, indent_chars=0,
         space_before=None, space_after=None):
    p = doc.add_paragraph(text, style=style)
    if align is not None:
        p.alignment = align
    if indent_chars:
        ppr = p._p.get_or_add_pPr(); ind2 = ppr.get_or_add_ind()
        ind2.set(qn("w:firstLineChars"), str(indent_chars * 100))
    for r in p.runs:
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
    if space_before is not None:
        p.paragraph_format.space_before = Pt(space_before)
    if space_after is not None:
        p.paragraph_format.space_after = Pt(space_after)
    return p

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

def add_table(headers, rows):
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
        style_cell(c, htxt, bold=True, align=WD_ALIGN_PARAGRAPH.CENTER)
    for i, row in enumerate(rows):
        for j, val in enumerate(row):
            c = t.rows[i + 1].cells[j]
            bottom = 8 if i == len(rows) - 1 else 0
            set_cell_borders(c, top=0, bottom=bottom)
            al = WD_ALIGN_PARAGRAPH.CENTER if (j == 0 or isinstance(val, str) or len(str(val)) <= 12) else WD_ALIGN_PARAGRAPH.RIGHT
            style_cell(c, str(val), align=al)
    return t

def add_picture_centered(path, width_cm):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    p.add_run().add_picture(path, width=Cm(width_cm))
    return p

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

# ---------- Title block ----------
para("Route-2 Defense XLII — Full-scale GUE Pair Correlation and the Online Simple-Zero Proportion 1−o(1): S0 Numerical Orientation",
     style="Title", align=WD_ALIGN_PARAGRAPH.CENTER)
para("(Calibration Fixes, Super-GUE Repulsion, and Theoretical Correspondence)", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="黑体", size=14, bold=True, space_after=4)
para("—《Spectral Duality Arguments》series (d1): the S0 gate verdict", align=WD_ALIGN_PARAGRAPH.CENTER,
     font="楷体", size=12, space_after=4)
para("October 24, 2026", align=WD_ALIGN_PARAGRAPH.CENTER, space_after=10)

# ---------- Abstract ----------
para("Abstract:", font="黑体", size=10.5, bold=True, indent_chars=0, space_after=0)
para("Defense XLII continues the XLI main line, \u201cdrive to 1\u201d: upgrade the hypothesis (H2) to full-scale GUE pair correlation as λ(T)→∞ (a strong Montgomery-type statement for the fixed-modulus real character L(s,χ₅)), so that Lamzouri\u2019s Proposition 2.1 directly yields A→1 and the union online simple-zero proportion →1−o(1). This note completes the S0 numerical orientation (gate verdict). Method: T=6×10⁵ zero data (999354 ζ-zeros, 1149836 L(χ₅)-zeros); kernel family K_a(u)=sinc²(πu/a) with spectral support λ_eff=π/a; pair constant A=1+ΣK²/N (ordered pairs); local normalization u=|Δ|·ρ(t_mid); two-sided GUE/Poisson comparison. Results: the full A(λ) curve (λ_eff∈[0.39,31.4]) tracks the two-sided GUE prediction closely and approaches 1 monotonically at the narrow end with no rebound (as a=0.5→0.1, A−1 falls from 1.49e-2 to 1.3e-4); no sign of a repulsion-violating gap (s_min=0.0123/0.0133; count of s<0.01 is 0); the observed values lie systematically below GUE (super-GUE repulsion), a GUE simulation excludes finite-N artifacts, and the segment drift shows the negative deviation converging with T. Three calibration fixes: the λ_eff conversion is pinned down (the XLI document\u2019s earlier assignment was inverted), the −1 term in the L-density is removed (nearest-neighbor mean 0.9197→1.0027), and the global δ vs local ρ differ by 0.7% (the XLI numerical conclusions are unchanged). Verdict: S0 passes, proceed to S1. Three-layer theoretical correspondence: the Montgomery pair-correlation conjecture (GUE universality class), β=2 level repulsion O(a³) (universal shape), and the super-GUE negative deviation attributed to finite-T arithmetic terms (the BGS error / Montgomery F(α)≥|α|, same source).", space_after=6)

para("Keywords: full-scale GUE pair correlation; online simple-zero proportion 1−o(1); pair constant; super-GUE repulsion; calibration fixes", space_after=10)

# ---------- 1 ----------
h1t("1　Background and Main Line")
h2t("1.1　XLI coordinates and the \u201cdrive to 1\u201d route")
para("Offense XLI (delivered to d1) closed the QRH constant mechanism under the pseudorandom (GUE) premise: single-family pair constants A_min=1.0079 (ζ) / 1.0114 (L) with kernel fejer_a0.5, the 7/8 threshold A≤1.125 met with margin 0.1171/0.1136; the decomposition argument gives the union online simple-zero proportion ≈0.990; the theorem takes a purely conditional (weak-premise) form whose hypotheses (H1)(H2) are directly testable numerically. XLI §8 sets the next-stage main line: upgrade (H2) to full-scale GUE pair correlation as λ(T)→∞ — a strong Montgomery-type statement for the fixed-modulus real character L(s,χ₅) (an open construction within our framework) — whence Proposition 2.1 directly gives A→1 and the online proportion →1−o(1), i.e. the framework-internal version of the literature statement \u201cstrong pair-correlation conjecture ⟹ almost all zeros are simple\u201d; the 7/8 threshold remains the current theorem coordinate. The user rejected the 31/32 threshold (7/8 is the current AI value), fixing the main-line target as \u201cdrive to 1\u201d.")
h2t("1.2　Four-stage plan and the S0 gate")
para("The \u201cdrive to 1\u201d plan has four stages S0–S3: S0 numerical orientation (gate: does A(λ) approach 1 monotonically with no rebound over long range); S1 theoretical construction (λ(T) growth scheme, derivation of A=1+O(λ^{-1}), weighted union theorem form); S2 numerical verification (Weil explicit-formula real-part injection sensitivity: measurability of N_off·δ²·(logx)² accumulation); S3 closed-loop archival. This note executes S0 and gives the verdict.")

# ---------- 2 ----------
h1t("2　Numerical Setup and Methods")
h2t("2.1　Data and zero density")
para("Zero data: T=6×10⁵ with t<300 removed; 999354 ζ-zeros and 1149836 L(s,χ₅)-zeros. Normalization density ρ_ζ(t)=log(t/2π)/2π; for the L family the constant term −1 in ρ_L=(1/2π)[log(t/(2π))−1+log5] was found by calibration to be erroneous: after removing it, the nearest-neighbor mean nn_mean rises from 0.9197 to 1.0027 (ζ is exactly 1.0000), a calibration factor ≈1.087. The global scale δ=logT/2π=2.1175 (used in XLI) gives u-average ≈1.74≠1 over the wide-band data, and wide kernels amplify the normalization error — S0 therefore adopts the local normalization u=|Δ|·ρ(t_mid).")
h2t("2.2　Kernel family and spectral-support conversion")
para("Kernel K_a(u)=sinc²(πu/a). The spectral support is λ_eff(a)=π/a (Fourier convention e^{-2πiξu}); see Table 1. The XLI document\u2019s statement \u201cfejer_a0.5 has spectral support ≈0.5\u201d is an inverted erroneous assignment — fejer_a0.5 actually has λ_eff=π/0.5=6.28≫1/2, far beyond the λ≤1/2 allowed in the unconditional framework (that freedom is precisely what the pseudorandom relaxation provides).")
caption("Table 1　Kernel width a and spectral support λ_eff=π/a (selection)")
add_table(["a", "0.1", "0.25", "0.5", "1.0", "2.0", "4.0", "8.0"],
          [["λ_eff=π/a", "31.42", "12.57", "6.28", "3.14", "1.57", "0.79", "0.39"]])
para("", indent_chars=0, space_after=2)
h2t("2.3　Pair constant, normalization, and two-sided comparison")
para("A(K)=1+Σ_{ordered pairs}K(δΔ)²/N (ordered pairs count both sides i≠j; this is the ΣK² in Proposition 2.1). The two-sided GUE prediction is GUE2(a)=1+2∫₀^∞(1−sinc²πu)sinc⁴(πu/a)du (two-point correlation ρ₂=1−sinc²πu); the Poisson baseline is Poi2(a)=1+2a/3. The initial one-sided comparison (missing the factor 2) counted the ordered-pair sum at half strength and produced the false alarm of \u201csuper-Poisson deviation\u201d; a minimal geometric check (constant-intensity Poisson narrow band, uniform ρ≡1 points, analytic ∫sinc⁴=1/3) identified a convention problem rather than a code bug — the final version uses the two-sided comparison.")
h2t("2.4　Three calibration fixes")
para("(1) λ_eff conversion: fejer_a0.5 is 6.28, not 0.5 (inversion fixed); (2) the L-density −1 term: after removal nn_mean=1.0027; (3) global δ vs local ρ: ζ a0.5 reads 1.00789 (reproducing audit6 exactly) in the global convention against 1.01494 locally, a 0.7% difference that does not overturn the XLI conclusions (margin 0.11–0.12) — nevertheless the XLI numerical statements (Table 1/Table 3, the ρ_L formula, the λ_eff annotation) must be disclosed in the next XLI revision.")

# ---------- 3 ----------
h1t("3　S0 Results")
h2t("3.1　The full A(λ) curve (Table 2, Fig. 1)")
AG = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
rows2 = []
for a in AG:
    s = str(a)
    rows2.append([a, v3["lambda_eff"][s], v3["A_zeta_fine"][s], v3["A_L_fine"][s],
                  v3["A_GUE2"][s], v3["A_Poisson2"][s], v3["verdict"]["zeta_dev_vs_GUE2"][s]])
caption("Table 2　Pair constant A(λ), full curve (T=6×10⁵, local normalization, ordered pairs; ζ−GUE2 = deviation of the observed from the two-sided GUE prediction)")
add_table(["a", "λ_eff=π/a", "A_ζ", "A_L", "GUE2", "Poi2", "ζ−GUE2"], rows2)
para("", indent_chars=0, space_after=2)
para("Reading: (i) the three-layer structure Poisson>GUE>observed — repulsion suppresses the pair sum; (ii) the observed values track GUE2 closely (wide-end plateau −0.020~−0.022), with no rebound at any scale; (iii) the narrow end is monotone to 1: as a=0.5→0.1, A_ζ−1 falls monotonically from 0.01494 to 0.00013, and A_L−1 from 0.01440 to 0.00017 — monotonicity verdict True.")
add_picture_centered(WORK + r"\xlii_s0_fig1_300.png", 14.5)
caption("Fig. 1　Full A(λ) curve vs two-sided GUE/Poisson (T=6×10⁵, local normalization): observed (ζ black, L red) hugging the GUE prediction (blue); three-layer structure, 7/8 threshold and C_MT reference lines; monotone approach to 1 with no rebound at the narrow end")
h2t("3.2　Minimal gaps and the repulsion-violation search (Table 3)")
mz, ml = v3["min_gap"]["zeta"], v3["min_gap"]["L"]
rows3 = [
    ["ζ", mz["n"], round(mz["s_min"], 5), mz["counts"]["0.05"], mz["counts"]["0.01"],
     mz["counts"]["0.005"], mz["counts"]["0.001"], mz["gue_pred"]["0.01"]],
    ["L", ml["n"], round(ml["s_min"], 5), ml["counts"]["0.05"], ml["counts"]["0.01"],
     ml["counts"]["0.005"], ml["counts"]["0.001"], ml["gue_pred"]["0.01"]],
]
caption("Table 3　Minimal gaps and repulsion-violation counts (s<ε = number of normalized nearest-neighbor gaps below ε; GUE column = theoretical prediction)")
add_table(["family", "n", "s_min", "s<0.05", "s<0.01", "s<0.005", "s<0.001", "GUE(s<0.01)"], rows3)
para("", indent_chars=0, space_after=2)
para("The count of s<0.01 is 0 (GUE prediction 1.1/1.2) — no sign of a repulsion-violating gap. Structural multiple zeros (their pair term K(0)=1 does not vanish as the kernel narrows) would block A→1; this obstacle is excluded here.")
h2t("3.3　Finite-T fluctuation calibration (Table 4)")
rows4 = []
for fam in ("zeta", "L"):
    for a in ("0.3", "0.5", "1.0", "2.0"):
        d = v3["drift"][fam][a]
        rows4.append([a, "ζ" if fam == "zeta" else "L"] + [round(x, 6) for x in d["vals"]] +
                     [d["max_adj"], d["range"]])
caption("Table 4　Segment drift of A (5 segments, 300–6×10⁵, local normalization; adj = maximal adjacent-segment difference, range = full-span difference)")
add_table(["a", "family", "seg1", "seg2", "seg3", "seg4", "seg5", "adj max", "range"], rows4)
para("", indent_chars=0, space_after=2)
para("Verdict: the narrow-end signal far exceeds the drift (ζ a0.5: adj ≤0.00092, range 0.00184; L: ≤0.00074 / 0.0014); the wide-end negative deviation (a −0.02 plateau) exceeds the drift by a factor ≈3 — a systematic signal. The negative deviation converges with height: ζ a0.5 across five segments moves 1.0138→1.0154 toward GUE2=1.0177, L similarly — the signature of a finite-T arithmetic term.")
h2t("3.4　GUE simulation comparison")
para("GUE matrix simulation (N=4000×12, calibrated so that nn_mean=1.0000): A_sim essentially coincides with the GUE2 theory (positive bias +0.001~+0.006: a0.5 1.01863 vs 1.01771, a8 5.39678 vs 5.39162); the observed values lie systematically below GUE with the deviation exceeding the segment drift by a factor ≈3 — the negative deviation is a genuine super-GUE repulsion signal, not a finite-N artifact. Its direction (stronger repulsion → fewer pairs → smaller A → proportion closer to 1) supports \u201cdrive to 1\u201d.")
add_picture_centered(WORK + r"\xlii_s0_fig2_300.png", 14.5)
caption("Fig. 2　A−1 convergence (log-log): observed (ζ black, L red) descending parallel to the GUE2 theory (blue) and slightly below it — super-GUE repulsion; the GUE simulation (purple triangles) ≈ theory, excluding finite-N artifacts; O(a³) slope at the narrow end")

# ---------- 4 ----------
h1t("4　Verdict and Theoretical Correspondence")
h2t("4.1　The S0 gate verdict")
para("The four conditions are checked item by item: A(λ) monotone to 1 with no rebound (passed); full curve hugging GUE (passed); no repulsion-violating gap (passed); finite-T fluctuation under control (passed). Verdict: S0 passes; the main line proceeds to S1.")
h2t("4.2　Three-layer theoretical correspondence")
para("(i) The full curve hugging GUE ⟺ the Montgomery pair-correlation conjecture / GUE universality class: for ζ this is a conjecture (strong numerical verification by Odlyzko at height 10²²); for the fixed-modulus real character L(s,χ₅) there is no unconditional version in the literature — precisely (H2)/(H2′). The data exhibit GUE structure already at low height (T=6×10⁵), consistent with the known experience that universality shows up at low height.")
para("(ii) The narrow-end A−1~O(a³) ⟺ the GUE β=2 level-repulsion universal shape: 1−sinc²πu~π²u²/3 as u→0 (quadratic zero of the two-point correlation), sinc⁴≈1 inside the window, ∫₀^a u²du~a³; for the GUE class Dyson\u2019s log-gas result is a theorem, for ζ a conjecture. The data independently reproduce the β=2 slope (Fig. 2: observed parallel to GUE2), excluding Poisson β=0 (A−1~a) and the symplectic β=4 (A−1~a⁵) — the strongest anchor.")
para("(iii) The super-GUE negative deviation ⟺ finite-T arithmetic terms: the BGS Lemma 5 error O_f(1/√logT) carries a kernel-dependent constant; Montgomery\u2019s F(α)≥|α| (|α|<1, nontrivial lower bound from the prime terms, with equality predicted by GUE) is the same-source structure, translated by Parseval into a deviation of the real-space pair sum (sign and shape to be derived strictly in S1a). Decisive evidence: the segment drift shows the negative deviation converging with T (low-t segments deviate more; high-t segments approach GUE) — the direct signature of \u201cdeviation = arithmetic term decaying with T\u201d; the GUE simulation excludes the finite-N correction direction.")
h2t("4.3　Honest boundaries")
para("(1) The data reach only T=6×10⁵ and λ_eff≤31.4; \u201cfull scale as λ(T)→∞ at infinite height\u201d remains hypothesis (H2′), not a theorem. (2) The super-GUE repulsion is marginally significant (ζ a0.5 deviation −0.00277, ≈3 times the adjacent segment drift 0.00092); it is not used as a theorem hypothesis, only recorded as directionally favorable. (3) The XLI old-convention numbers (global δ, the ρ_L with −1, the λ_eff≈0.5 annotation) differ from this note; conclusions do not flip but must be disclosed in the XLI revision. (4) The kernel scan is finite (fejer family), not an exhaustive search of the variational space.")

# ---------- 5 ----------
h1t("5　Next Steps: the S1 Split")
h2t("5.1　S1a: arithmetic-term attribution (quantifying layer (iii))")
para("(1) Parseval: translate A(a)−GUE2(a) into F(α,T)−|α| for α∈(0,1), compare with the excess above Montgomery\u2019s lower bound, and verify sign and shape; (2) decay law: fit Δ(a;T)~c(a)/logT or c(a)/√logT over the five segments to distinguish the BGS error structure; (3) kernel-dependent constants: order the deviations of the fejer/sinc/gauss families by the smoothness of their Fourier support (audit6 data already available).")
h2t("5.2　S1b: construction of the λ(T) scheme")
para("Make (H2′) explicit (a strong Montgomery-type statement as λ(T)→∞, with growth rate and error shape); derive A=1+O(λ^{-1}); incorporate the structural-multiple-zero term (s<0.01 already excluded); weighted union → the theorem form with online proportion 1−o(1).")

# ---------- References ----------
h1t("References")
refs = [
    "[1] Lamzouri Y. A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line. arXiv:2609.02882v2 (Proposition 2.1 (N₀ˢ≥2Σ1−ΣK²), Lemma 3.2 (optimal kernel f₀(x)=cos(√2x)/(√2sin(1/√2)), C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963), Remark 3.4 (C_η≥C_MT optimality)) — read in full.",
    "[2] Baluyot D, Goldston D, Suriajaya A I, et al. An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function. arXiv:2306.04799 (Lemma 5: unconditional pair-correlation formula, error O_f(1/√logT), weight w(z)=4/(4−z²); the BGS generalization to fixed-modulus L(χ) is an open construction).",
    "[3] Özlük A E. On the pair correlation of zeros of Dirichlet L-functions (1982; at least 11/12 simple under GRH, with weight) — verified via the introduction of Kandhil–Languasco–Moree.",
    "[4] Kandhil N, Languasco A, Moree P. Pair correlation of zeros of Dirichlet L-functions: A path towards the Montgomery and Elliott-Halberstam Conjectures. arXiv:2411.19762 (Yıldırım theorem / Conjecture 1: cross-character-average pair correlation, GRH premise) — read in full.",
    "[5] Carneiro E, Milinovich M B, Ramos A P. Fourier optimization and Montgomery's pair correlation conjecture. arXiv:2310.01913 (F-average 0.9303–1.3208, including Dirichlet L-function families).",
    "[6] Odlyzko A M. The 10^22-nd zero of the Riemann zeta function (10¹⁰ zeros; numerical verification of RH and GUE pair correlation — \u201cconfirmed the GUE connection\u201d).",
    "[7] Defense-XLII numerical package (this work; reproducible with Anaconda python): qrh_work/xlii_s0.py (v1 global convention), xlii_s0_v2.py (v2 local, with the erroneous L density), xlii_s0_v3.py (final: local normalization + two-sided GUE + L calibration), xlii_s0_check.py (Poisson simulation / ρ₂ debugging), xlii_s0_debug.py (minimal verification of the factor 2), xlii_s0_gue.py (GUE simulation), xlii_s0_plot.py (figures); results xlii_s0_v3.json, xlii_s0_gue_sim.json; zero data zeros_T6e5.npz (T=6×10⁵, ζ 999354 / L 1149836 roots).",
    "[8] Offense XLI (delivered to d1): conditional form of the pseudorandom union theorem — 7/8 threshold, fejer_a0.5 optimal kernel, decomposition argument, three-layer premise reliability.",
    "[9] Offense XL (delivered to d1): theoretical construction of the unconditional bound on the pairing side — the 0.6725 constant gap is of QRH-mechanism type; Offense XXXIX (S4): fine form of the online-proportion-bridge remainder.",
]
for rtext in refs:
    para(rtext, indent_chars=0, space_after=2)

doc.save(TARGET)
print("saved:", TARGET)
