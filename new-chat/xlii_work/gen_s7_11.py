# -*- coding: utf-8 -*-
'''生成 S7.11 攻防落档（中文 d1 + 英文 d1\\en）。Unicode 数学文本（可读纯文本+上下标，无 LaTeX）。'''
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml.ns import qn

def set_run_font(run, cn='宋体', en='Times New Roman', size=12, bold=False):
    run.font.name = en
    run.font.size = Pt(size)
    run.font.bold = bold
    run.font.color.rgb = RGBColor(0, 0, 0)
    rPr = run._element.get_or_add_rPr()
    rFonts = rPr.find(qn('w:rFonts'))
    if rFonts is None:
        rFonts = rPr.makeelement(qn('w:rFonts'), {})
        rPr.append(rFonts)
    rFonts.set(qn('w:eastAsia'), cn)
    rFonts.set(qn('w:ascii'), en)
    rFonts.set(qn('w:hAnsi'), en)

def add_title(doc, text):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    p.paragraph_format.space_after = Pt(18)
    r = p.add_run(text)
    set_run_font(r, cn='黑体', size=18, bold=True)

def add_h1(doc, text):
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(14)
    p.paragraph_format.space_after = Pt(6)
    r = p.add_run(text)
    set_run_font(r, cn='黑体', size=16, bold=True)

def add_h2(doc, text):
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(11)
    p.paragraph_format.space_after = Pt(5)
    r = p.add_run(text)
    set_run_font(r, cn='黑体', size=14, bold=True)

def add_body(doc, text, indent=True):
    p = doc.add_paragraph()
    pf = p.paragraph_format
    pf.line_spacing = 1.5
    pf.space_before = Pt(0)
    pf.space_after = Pt(0)
    if indent:
        pf.first_line_indent = Pt(24)
    r = p.add_run(text)
    set_run_font(r, size=12)
    return p

def add_math(doc, text):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    p.paragraph_format.line_spacing = 1.5
    p.paragraph_format.space_before = Pt(3)
    p.paragraph_format.space_after = Pt(3)
    r = p.add_run(text)
    set_run_font(r, size=12)
    return p

def new_doc():
    doc = Document()
    sec = doc.sections[0]
    sec.page_width = Cm(21)
    sec.page_height = Cm(29.7)
    sec.top_margin = sec.bottom_margin = sec.left_margin = sec.right_margin = Cm(2.5)
    return doc

def build_zh(path):
    doc = new_doc()
    add_title(doc, '路2攻防 XLII S7.11：x=1 边界口径（trivialTerm 调和发散与 landau_explicit_L 前提收紧）')
    add_h1(doc, '1. 任务与结论')
    add_body(doc, '本轮做 (L1) 长线的 x=1 边界口径：trivialTerm 在 x=1 处为调和型发散，landau_explicit_L 的适用前提由 1 ≤ x 收紧为 1 < x（口径决定，非深证明）。Lean 侧完成三处陈述改动与两件约定件，全量 lake build QRH 通过：2704 jobs，exit=0，无 error、无 warning（dbg_build_x1.txt）。自此 (L1) 显式公式的前提与已真证的 trivialTerm_summable（1 < x）完全对齐，x=1 处的 ∑′ 默认值不再进入任何数学断言。')
    add_h1(doc, '2. 数学口径')
    add_h2(doc, '2.1 trivialTerm 定义与收敛域')
    add_body(doc, '平凡项（Yildirim 公式 (6) 右侧第一项；模 5 实特征 χ₅ 偶特征 a=0 已代入，S7_1_Main.lean 真实级数口径）：')
    add_math(doc, 'trivialTerm(r,x) = Σ_ℓ x^{−(2ℓ+r)}/(2ℓ+r)，ℓ = 0,1,2,…')
    add_body(doc, '收敛件已真证（trivialTerm_summable，2026-10-27）：1 < x、r > 0 时级数可和（逐项非负 + 逐项上界 x^{−r}·(x^{−2})^ℓ/r + 几何级数比较）。收敛域为 x > 1；x = 1 是边界奇点。')
    add_h2(doc, '2.2 x=1 调和发散')
    add_body(doc, 'x = 1 时逐项为 1/(2ℓ+r)：')
    add_math(doc, 'trivialTerm(r,1) = Σ_ℓ 1/(2ℓ+r)')
    add_body(doc, '该级数为调和型：1/(2ℓ+r) ~ 1/(2ℓ)（ℓ → ∞），与 Σ_n 1/n 同阶，比较判别发散。故 x = 1 处 trivialTerm 不收敛、不在显式公式适用域内。')
    add_h2(doc, '2.3 约定与前提收紧（防假命题陷阱）')
    add_body(doc, '原 landau_explicit_L 前提为 1 ≤ x（Yildirim 公式 (6) 的宽松版本）。若不收紧，x = 1 时 axiom 断言 trivialTerm(1) = 0 − primePowerSum(1) − logDerivTerm(r)；而 primePowerSum/zeroWeightedSum 在 x = 1 均为 0（Finset.Icc 1 1 仅含 n = 1，Λ(1) = 0），logDerivTerm(r) 一般非零——于是 axiom 在发散点断言一个非平凡的等式，而 ∑′ 对不可和级数的 mathlib 默认值为 0，此 0 无数学意义。约定（2026-10-29）：')
    add_body(doc, '（i）landau_explicit_L 前提收紧为 1 < x（严格），x = 1 不在适用域；（ii）x = 1 处的 ∑′ 默认值 0 不作任何数学意义引用；（iii）x = 1 的调和型发散作为口径事实记录，发散性的正式形式化证明（¬ Summable）留作可选后续件——本轮只定口径，不立深证明。')
    add_h2(doc, '2.4 与 (L1b)/(L2) 的衔接')
    add_body(doc, '收紧后 landau_explicit_L 的前提 (1 < x) 与 trivialTerm_summable 的前提完全一致：显式公式的平凡项在适用域内自动可和，组装 (L2) prime_sum_bound 时无需额外边界分支。x = 1 口径只影响 (L1) 显式公式组装，不影响配对常数主链（配对常数在 T 高度层，与 x 无关）。')
    add_h1(doc, '3. Lean 实现')
    add_h2(doc, '3.1 陈述改动（S7_1_Main.lean）')
    add_body(doc, '（i）landau_explicit_L：前提 (1 : ℝ) ≤ x → (1 : ℝ) < x，axiom 注释同步说明 x=1 为调和型发散奇点、口径排除；（ii）trivialTerm_summable 注释同步：x = 1 边界见 2.1.2 小节，前提已收紧。siegel_walfisz_chi5 的 1 ≤ x 前提独立保留（SW 部分和在 x ≥ 1 良定义，与平凡项无关）。')
    add_h2(doc, '3.2 约定件（2.1.2 小节，两件真证）')
    add_body(doc, 'trivialTerm_one_term：x = 1 逐项等式，rpow 1 (...) = 1（simp 关，Real.one_rpow 为 simp 引理；直接 rw 模式为 1 ^ ?x 与目标 rpow 1 (...) 不匹配，故用 simp 而非 rw）。')
    add_math(doc, 'lemma trivialTerm_one_term (r : ℝ) (ℓ : ℕ) : rpow 1 (−(2ℓ+r)) / (2ℓ+r) = 1 / (2ℓ+r)')
    add_body(doc, 'trivialTerm_one：x = 1 时 trivialTerm 归结为调和型级数（tsum_congr 逐项代入）：')
    add_math(doc, 'lemma trivialTerm_one (r : ℝ) : trivialTerm r 1 = Σ_ℓ 1/(2ℓ+r)')
    add_h2(doc, '3.3 编译证据')
    add_body(doc, 'lake build QRH：2704 jobs，exit=0，无 error、无 warning（dbg_build_x1.txt；日志全文 grep error:/warning 计数为 0）。此前一次 rw [Real.one_rpow] 版本编译失败（模式 1 ^ ?x 未匹配目标 rpow 1 (...)，ring 亦关不掉），改 simp 后通过——记录在案，避免重踩。')
    add_h1(doc, '4. 边界与后续')
    add_body(doc, '（1）发散性正式证明（¬ Summable of Σ 1/(2ℓ+r)）留作可选件：数学论证已完整记录（与 Σ 1/n 同阶比较），mathlib 调和级数发散骨架经平移比较即可，属“深证明”范畴，按本轮口径决定不动。（2）landau_explicit_L 形式化真证仍是 (L1) 长线目标（L′/L 的 Dirichlet 级数展开 + Mellin 变换写成引理）；x=1 口径是其前提闭包的一环。（3）与 S7.1 Stage 3+ 击破清单无冲突：配对常数主链不触碰 x=1。')
    doc.save(path)
    print('saved', path)

def build_en(path):
    doc = new_doc()
    add_title(doc, 'Route-2 Assault XLII S7.11: The x=1 Boundary Convention (Harmonic Divergence of trivialTerm and Tightening of landau_explicit_L)')
    add_h1(doc, '1. Task and Conclusion')
    add_body(doc, 'This round settles the x=1 boundary convention of the (L1) long line: trivialTerm diverges harmonically at x=1, and the applicability premise of landau_explicit_L is tightened from 1 ≤ x to 1 < x (a convention decision, not a deep proof). On the Lean side, three statement changes and two convention lemmas are done; the full lake build QRH passes: 2704 jobs, exit=0, no errors, no warnings (dbg_build_x1.txt). The premise of the explicit formula now aligns exactly with the proven trivialTerm_summable (1 < x), and the ∑′ default value at x=1 no longer enters any mathematical assertion.')
    add_h1(doc, '2. Mathematical Convention')
    add_h2(doc, '2.1 Definition of trivialTerm and its convergence domain')
    add_body(doc, 'The trivial term (first term on the right of Yildirim formula (6); the even character χ₅ with a=0 already substituted; real-series convention in S7_1_Main.lean):')
    add_math(doc, 'trivialTerm(r,x) = Σ_ℓ x^{−(2ℓ+r)}/(2ℓ+r), ℓ = 0,1,2,…')
    add_body(doc, 'The summability item is proven (trivialTerm_summable, 2026-10-27): for 1 < x and r > 0 the series is summable (termwise nonnegativity + termwise bound x^{−r}·(x^{−2})^ℓ/r + geometric comparison). The convergence domain is x > 1; x = 1 is a boundary singularity.')
    add_h2(doc, '2.2 Harmonic divergence at x=1')
    add_body(doc, 'At x = 1 the terms reduce to 1/(2ℓ+r):')
    add_math(doc, 'trivialTerm(r,1) = Σ_ℓ 1/(2ℓ+r)')
    add_body(doc, 'This series is harmonic-type: 1/(2ℓ+r) ~ 1/(2ℓ) (ℓ → ∞), of the same order as Σ_n 1/n, divergent by comparison. Hence x = 1 is outside the applicability domain of the explicit formula.')
    add_h2(doc, '2.3 Convention and tightening (avoiding a false-proposition trap)')
    add_body(doc, 'The original landau_explicit_L had premise 1 ≤ x (the relaxed form of Yildirim formula (6)). Without tightening, at x = 1 the axiom would assert trivialTerm(1) = 0 − primePowerSum(1) − logDerivTerm(r); but primePowerSum/zeroWeightedSum vanish at x = 1 (Finset.Icc 1 1 contains only n = 1, Λ(1) = 0) while logDerivTerm(r) is generally nonzero — the axiom would assert a nontrivial identity at a divergent point, and the mathlib default of ∑′ for non-summable series is 0, a value with no mathematical meaning. Convention (2026-10-29):')
    add_body(doc, '(i) the premise of landau_explicit_L is tightened to 1 < x (strict); x = 1 is outside the domain; (ii) the ∑′ default value 0 at x = 1 is never used as a mathematical fact; (iii) the harmonic divergence at x = 1 is recorded as a convention fact, while a formal proof of divergence (¬ Summable) is left as an optional follow-up — this round fixes the convention only, no deep proof.')
    add_h2(doc, '2.4 Link to (L1b)/(L2)')
    add_body(doc, 'After tightening, the premise (1 < x) of landau_explicit_L matches the premise of trivialTerm_summable exactly: the trivial term is automatically summable inside the domain, and the (L2) prime_sum_bound assembly needs no extra boundary branch. The x=1 convention affects only the (L1) explicit-formula assembly, not the pairing-constant mainline (the pairing constant lives at height T, independent of x).')
    add_h1(doc, '3. Lean Implementation')
    add_h2(doc, '3.1 Statement changes (S7_1_Main.lean)')
    add_body(doc, '(i) landau_explicit_L: premise (1 : ℝ) ≤ x → (1 : ℝ) < x, axiom comment updated (x=1 is a harmonic-divergence singularity, excluded by convention); (ii) trivialTerm_summable comment updated (x=1 boundary covered in §2.1.2; premise tightened). The 1 ≤ x premise of siegel_walfisz_chi5 is kept independently (the SW partial sum is well-defined for x ≥ 1, unrelated to the trivial term).')
    add_h2(doc, '3.2 Convention lemmas (§2.1.2, two true proofs)')
    add_body(doc, 'trivialTerm_one_term: termwise identity at x = 1, rpow 1 (...) = 1 (closed by simp; Real.one_rpow is a simp lemma — a direct rw failed because the pattern 1 ^ ?x did not match the goal rpow 1 (...), so simp is used instead of rw).')
    add_math(doc, 'lemma trivialTerm_one_term (r : ℝ) (ℓ : ℕ) : rpow 1 (−(2ℓ+r)) / (2ℓ+r) = 1 / (2ℓ+r)')
    add_body(doc, 'trivialTerm_one: at x = 1 the trivial term reduces to the harmonic-type series (tsum_congr termwise substitution):')
    add_math(doc, 'lemma trivialTerm_one (r : ℝ) : trivialTerm r 1 = Σ_ℓ 1/(2ℓ+r)')
    add_h2(doc, '3.3 Build evidence')
    add_body(doc, 'lake build QRH: 2704 jobs, exit=0, no errors, no warnings (dbg_build_x1.txt; grep of the log for error:/warning returns count 0). An earlier rw [Real.one_rpow] version failed to compile (pattern 1 ^ ?x did not match the goal rpow 1 (...), and ring could not close it); switching to simp passed — logged to avoid re-treading.')
    add_h1(doc, '4. Boundary and Follow-up')
    add_body(doc, '(1) The formal divergence proof (¬ Summable of Σ 1/(2ℓ+r)) is left optional: the mathematical argument is fully recorded (comparison with Σ 1/n), and mathlib has the harmonic-divergence skeleton with a shift-comparison — this is "deep-proof" territory and untouched by the present convention decision. (2) The formal proof of landau_explicit_L remains the (L1) long-line goal (Dirichlet-series expansion of L′/L plus Mellin transform as lemmas); the x=1 convention is one step of its premise closure. (3) No conflict with the S7.1 Stage 3+ strike list: the pairing-constant mainline never touches x=1.')
    doc.save(path)
    print('saved', path)

if __name__ == '__main__':
    build_zh(r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.11-x1边界口径-trivialTerm调和发散与landau_explicit_L前提收紧.docx')
    build_en(r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.11-x1-boundary-trivialTerm-harmonic-divergence-EN.docx')
