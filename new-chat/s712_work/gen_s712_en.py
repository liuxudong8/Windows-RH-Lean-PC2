# -*- coding: utf-8 -*-
"""S7.12 English docx generation (no-template creation)."""
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_ALIGN_VERTICAL
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.12-fourierCos-definition-and-scale-lemma-EN.docx'
BLACK = RGBColor(0, 0, 0)
HEADER_SHADE = 'D9D9D9'


def set_style_font(st, cn='宋体', en='Times New Roman', size=12, bold=False):
    st.font.name = en
    st.font.size = Pt(size)
    st.font.bold = bold
    st.font.color.rgb = BLACK
    rPr = st.element.get_or_add_rPr()
    rFonts = rPr.get_or_add_rFonts()
    rFonts.set(qn('w:eastAsia'), cn)


def set_run_font(r, cn='宋体', en='Times New Roman', size=12, bold=False):
    r.font.name = en
    r.font.size = Pt(size)
    r.font.bold = bold
    r.font.color.rgb = BLACK
    rPr = r._element.get_or_add_rPr()
    rFonts = rPr.get_or_add_rFonts()
    rFonts.set(qn('w:eastAsia'), cn)


def set_first_line_chars(p, chars=200):
    pPr = p._p.get_or_add_pPr()
    ind = pPr.find(qn('w:ind'))
    if ind is None:
        ind = OxmlElement('w:ind')
        pPr.append(ind)
    ind.set(qn('w:firstLineChars'), str(chars))
    ind.set(qn('w:firstLine'), '480')


def shade_cell(cell, color):
    tcPr = cell._tc.get_or_add_tcPr()
    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'), 'clear')
    shd.set(qn('w:color'), 'auto')
    shd.set(qn('w:fill'), color)
    vAlign = tcPr.find(qn('w:vAlign'))
    if vAlign is not None:
        vAlign.addprevious(shd)
    else:
        tcPr.append(shd)


doc = Document()
sec = doc.sections[0]
sec.page_width = Cm(21.0)
sec.page_height = Cm(29.7)
sec.top_margin = Cm(2.5)
sec.bottom_margin = Cm(2.5)
sec.left_margin = Cm(2.5)
sec.right_margin = Cm(2.5)

fp = sec.footer.paragraphs[0]
fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
fld1 = OxmlElement('w:fldChar'); fld1.set(qn('w:fldCharType'), 'begin')
instr = OxmlElement('w:instrText'); instr.set(qn('xml:space'), 'preserve'); instr.text = 'PAGE'
fld2 = OxmlElement('w:fldChar'); fld2.set(qn('w:fldCharType'), 'end')
r0 = fp.add_run()
r0._r.append(fld1); r0._r.append(instr); r0._r.append(fld2)
set_run_font(r0, size=9)

set_style_font(doc.styles['Normal'], '宋体', 'Times New Roman', 12, False)
doc.styles['Normal'].paragraph_format.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
doc.styles['Normal'].paragraph_format.line_spacing = 1.5
doc.styles['Normal'].paragraph_format.space_before = Pt(0)
doc.styles['Normal'].paragraph_format.space_after = Pt(0)

set_style_font(doc.styles['Title'], '黑体', 'Times New Roman', 18, True)
doc.styles['Title'].paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
doc.styles['Title'].paragraph_format.space_after = Pt(18)

set_style_font(doc.styles['Heading 1'], '黑体', 'Times New Roman', 16, True)
doc.styles['Heading 1'].paragraph_format.space_before = Pt(14)
doc.styles['Heading 1'].paragraph_format.space_after = Pt(6)
set_style_font(doc.styles['Heading 2'], '黑体', 'Times New Roman', 14, True)
doc.styles['Heading 2'].paragraph_format.space_before = Pt(11)
doc.styles['Heading 2'].paragraph_format.space_after = Pt(5)
set_style_font(doc.styles['Heading 3'], '黑体', 'Times New Roman', 12, True)
doc.styles['Heading 3'].paragraph_format.space_before = Pt(9)
doc.styles['Heading 3'].paragraph_format.space_after = Pt(4)


def add_heading(text, level):
    p = doc.add_heading(level=level)
    r = p.add_run(text)
    sizes = {1: 16, 2: 14, 3: 12}
    set_run_font(r, '黑体', 'Times New Roman', sizes[level], True)
    p.paragraph_format.keep_with_next = True
    return p


def add_body(text, indent=True):
    p = doc.add_paragraph()
    r = p.add_run(text)
    set_run_font(r, '宋体', 'Times New Roman', 12, False)
    p.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
    p.paragraph_format.line_spacing = 1.5
    p.paragraph_format.space_before = Pt(0)
    p.paragraph_format.space_after = Pt(0)
    if indent:
        set_first_line_chars(p, 200)
    return p


# ============ body ============
p = doc.add_paragraph(style='Title')
r = p.add_run('Assault XLII-S7.12: fourierCos as a True Definition and the Scale Lemma fourierCos_scale as a True Proof')
set_run_font(r, '黑体', 'Times New Roman', 18, True)

p = doc.add_paragraph()
r = p.add_run('(Integral/analytic-layer component · 2026-10-29 · archived to d1 by convention)')
set_run_font(r, '楷体', 'Times New Roman', 12, False)
p.alignment = WD_ALIGN_PARAGRAPH.CENTER
p.paragraph_format.space_after = Pt(12)

add_heading('1  Summary of Conclusions', 1)
add_body('This round completes component 5 of the integral/analytic layer of the QRH Lean formalization project (C:\\proj2\\QRH): the frequency-domain operator fourierCos is demoted from axiom to a Bochner-integral true definition, and its scale law fourierCos_scale (r̂_a(z) = r̂(az)) is demoted from axiom to a fully proved lemma. The full lake build QRH passes: 2704 jobs, 0 errors, 0 warnings.')
add_body('One earlier conclusion is corrected. The S7.3 documentation and code comments claimed that "a true proof of fourierCos_scale requires an integral layer (MeasureTheory.IntervalIntegral or a Riemann integral module), to be restored after the mathlib aggregate is generated." This round refutes that judgment empirically: mathlib v4.34 has restructured Bochner integration into the Integral/Bochner/ subdirectory, and the full-space Haar change-of-variables theorem Measure.integral_comp_inv_mul_left is already usable under the existing "specific-module import" route, with no regularity assumption on the integrand. The scale law therefore closes directly, with no module aggregation needed.')
add_body('The count of remaining named axioms decreases by one (fourierCos_scale leaves); the two dependent use sites n1_diag_invariant and n1_offdiag_scale_eq are unchanged in statement and compile without modification.')

add_heading('2  Background and Positioning', 1)
add_heading('2.1  Role of fourierCos in the S7.1 Formalization', 2)
add_body('fourierCos is the frequency-domain abstract operator: for a pairing kernel K and a frequency point z it gives ∫ K(x)·cos(2πzx) dx, corresponding to the kernel Fourier transform r̂(z) in the spectral-duality framework. In the S7.1 theorem skeleton the upper-bound chain for the pairing constant A_L is carried through the L¹ bound and the frequency-decay component of the kernel Fourier transform; the N1 super-support structural components of S7.3, n1_diag_invariant (z = 0 specialization) and n1_offdiag_scale_eq (z = 2δ specialization), depend on rw [fourierCos_scale ...] as their only dependency.')
add_heading('2.2  Axiom Backlog Status', 2)
add_body('Core §4b originally carried three named axioms: fourierCos (the carrier), fourierCos_Khat (closed form of K̂), and khat_lipschitz (Lipschitz component of the band-limited entire function); Stage3 N1 region further carried fourierCos_scale (frequency scaling). This round removes fourierCos itself and fourierCos_scale from the backlog; fourierCos_Khat and khat_lipschitz remain axioms (the former needs the analytic closed-form layer, the latter the derivative component; separate assault lines).')

add_heading('3  Change 1: fourierCos as a True Definition', 1)
add_body('In Core §4b the axiom fourierCos is replaced by a noncomputable true definition:')
add_body('fourierCos K z := ∫ x : ℝ, K(x)·cos(2π·z·x) dx', indent=False)
add_body('Semantics and convention: the integral is a Bochner integral with respect to volume on ℝ; when the integrand is not integrable, the mathlib convention returns 0 (the same mechanism as the true definition of normL1). The calling signature fourierCos K z is unchanged, so all use sites — the primeSum weights, prime_weight_bounds_Khat, and others — need no modification. The comments are updated to the true-definition statement.')

add_heading('4  Change 2: The Scale Lemma fourierCos_scale as a True Proof', 1)
add_heading('4.1  Statement', 2)
add_body('For arbitrary r : ℝ → ℝ (no regularity assumption), 0 < a, z : ℝ:')
add_body('fourierCos (scaleKernel a r) z = fourierCos r (a·z)', indent=False)
add_body('where scaleKernel a r := λx, (1/a)·r(x/a).')
add_heading('4.2  Proof Chain', 2)
add_body('A four-step calc chain (same technology stack as the scaleKernel_L1_invariant proof of 2026-10-27):')
add_body('(1) Pull out the constant factor: the integrand (1/a)·r(x/a)·cos(2πzx) is rearranged by integral_congr_ae + ring into (1/a)·(r(x/a)·cos(2πzx)), then integral_const_mul extracts 1/a.')
add_body('(2) Rearrange the integrand: x/a is rewritten as a⁻¹·x (div_eq_inv_mul), and the cos argument is rewritten accordingly as 2π·z·(a·(a⁻¹·x)) — the latter requires field_simp [ne_of_gt ha] to cancel a⁻¹, the only field-operation point of this step.')
add_body('(3) Haar change of variables: call Measure.integral_comp_inv_mul_left directly, obtaining ∫ r(a⁻¹·x)·cos(2π·z·(a·(a⁻¹·x))) dx = |a|·∫ r(y)·cos(2π·z·(a·y)) dy. This theorem is the full-space version and holds for arbitrary functions with no measurability assumption.')
add_body('(4) Rewrite the cos argument and cancel the factor: z·(a·y) is rewritten as (a·z)·y (integral_congr_ae + ring), and the final term (1/a)·(|a|·X) is reduced to X by abs_of_pos ha and field_simp [ne_of_gt ha], which is exactly fourierCos r (a·z).')
add_heading('4.3  Available Components and Use Sites', 2)
add_body('Available: integral_const_mul, integral_congr_ae (filter_upwards pointwise architecture), and Measure.integral_comp_inv_mul_left (full space, no regularity assumption) — all located in Integral/Bochner/Basic.olean, inside the project\'s existing import chain. The use sites n1_diag_invariant (rw [fourierCos_scale a ha r 0]) and n1_offdiag_scale_eq (rw [fourierCos_scale a ha r (2·δ)]) are unchanged in signature and compile as before.')

add_heading('5  Correction of an Earlier Conclusion: the IntervalIntegral Dependency Judgment', 1)
add_heading('5.1  The Earlier Judgment', 2)
add_body('The S7.3 archive and code comments recorded: "a true proof of fourierCos_scale requires an integral layer (MeasureTheory.IntervalIntegral or a Riemann integral module) — to be restored after the mathlib aggregate is generated," based on probes confirming that IntervalIntegral.olean and the top-level Integral.olean are missing.')
add_heading('5.2  Empirical Refutation', 2)
add_body('(a) The missing-judgment part is correct: IntervalIntegral.olean, the top-level Integral.olean, and the legacy name Bochner.olean all do not exist.')
add_body('(b) The conclusion was wrong: v4.34 restructures Bochner integration into the Integral/Bochner/ subdirectory; the ∫ notation, integral_const_mul, integral_congr_ae, and integral_map all live in Bochner/Basic.olean (the same source as the true definition of normL1, already inside the project import chain); moreover Measure.integral_comp_inv_mul_left is a full-space Haar change of variables with no regularity assumption on the integrand. The scale-law proof therefore needs neither IntervalIntegral nor any mathlib aggregation.')
add_heading('5.3  Dead Ends (Do Not Retry)', 2)
add_body('(a) import Mathlib.MeasureTheory.Integral.Integral: the top-level olean is missing; it always fails.')
add_body('(b) A full-space pointwise integral_congr: does not exist in v4.34 (only integral_congr_ae and the L1-class versions); always use integral_congr_ae + filter_upwards / ae_of_all.')
add_body('(c) Generalizing integral_map: that theorem requires AEMeasurable φ and AEStronglyMeasurable f (the integrand), unusable for arbitrary r; the measure-layer scaling formulas volume_map_mul_left / map_mul_left do not exist in v4.34. The only reliable exit for a full-space change of variables is Measure.integral_comp_inv_mul_left.')

add_heading('6  Build Verification', 1)
add_body('Full lake build QRH: 2704 jobs, exit = 0, 0 errors, 0 warnings (log C:\\proj2\\QRH\\dbg_build_fourier.txt). The three probe versions (FourierProbe.lean: import-missing check, namespace-trap check, integral-component inventory check) completed their mission and were deleted.')

add_heading('7  Remaining Named Axiom Status', 1)
rows = [
    ('Name', 'Location', 'Status'),
    ('fourierCos_Khat', 'Core §4b', 'Named axiom (closed form of K̂, analytic layer)'),
    ('khat_lipschitz', 'Core §4b', 'Named axiom (Lipschitz of band-limited entire function)'),
    ('bgs5_khat_fourier_supp', 'Main', 'Named axiom (BGS Lemma 5 frequency support)'),
    ('siegel_walfisz_chi5', 'Main', 'Named axiom (Siegel-Walfisz for χ₅)'),
    ('landau_explicit_L', 'Main', 'Named axiom (Landau explicit formula, L version)'),
    ('f0_sub_feps_L1_bound', 'Stage3', 'Named axiom (exact statement; true proof needs integral layer)'),
    ('N_L_lower_bound', 'Stage3', 'Named axiom (structural; S6 zero count)'),
    ('n2_linkage', 'Stage3', 'Named axiom (structural; S7.4 Theorem N2)'),
    ('n3_remainder_uniform', 'Stage3', 'Named axiom (structural; S7.5 Theorem N3)'),
]
tbl = doc.add_table(rows=len(rows), cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
widths = [Cm(5.0), Cm(2.6), Cm(8.4)]
for i, row_data in enumerate(rows):
    for j, val in enumerate(row_data):
        cell = tbl.rows[i].cells[j]
        cell.width = widths[j]
        cell.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
        para = cell.paragraphs[0]
        para.alignment = WD_ALIGN_PARAGRAPH.LEFT
        para.paragraph_format.space_before = Pt(2)
        para.paragraph_format.space_after = Pt(2)
        para.paragraph_format.line_spacing = 1.0
        r = para.add_run(val)
        set_run_font(r, '宋体', 'Times New Roman', 10.5, i == 0)
        if i == 0:
            para.alignment = WD_ALIGN_PARAGRAPH.CENTER
            shade_cell(cell, HEADER_SHADE)
    if i == 0:
        trPr = tbl.rows[i]._tr.get_or_add_trPr()
        tblHeader = OxmlElement('w:tblHeader')
        tblHeader.set(qn('w:val'), 'true')
        trPr.append(tblHeader)
    trPr = tbl.rows[i]._tr.get_or_add_trPr()
    cantSplit = OxmlElement('w:cantSplit')
    trPr.append(cantSplit)

add_body('')
add_body('Note: the table is a snapshot as of 2026-10-29. fourierCos and fourierCos_scale have left the backlog; each remaining axiom belongs to its own assault line, as recorded in the respective chapters.')

doc.save(OUT)
print('saved:', OUT)
