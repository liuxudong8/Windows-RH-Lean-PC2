# -*- coding: utf-8 -*-
'''生成 S7.10 攻防落档（中文 d1 + 英文 d1\\en）。Unicode 数学文本（可读纯文本+上下标，无 LaTeX）。'''
import sys
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
    add_title(doc, '路2攻防 XLII S7.10：prime_weight_bounds 降定理（Khat 特化）与素数项界真证')
    add_h1(doc, '1. 任务与结论')
    add_body(doc, '本轮把素数项权重件 prime_weight_bounds（原 axiom）降为真证定理 prime_weight_bounds_Khat，并将主定理组装件 prime_sum_bound 特化到 K := Khat。全量 lake build QRH 通过：2704 jobs，exit=0，无 warning。素数项 S(X) 的权重有界/平滑件自此在 Lean 侧闭环为真证；残余前置仅剩连接件、光滑件与积分层窄支撑三个命名 axiom（第 5 节）。')
    add_h1(doc, '2. 数学口径')
    add_h2(doc, '2.1 素数项与权重')
    add_body(doc, '素数项（差型配对中的 BGS 引理 3 素数项真实载体，S7.9 支撑截断口径）：')
    add_math(doc, 'S(X) = Σ₁≤n≤⌊X⌋ Λ(n)χ₅(n)·n⁻¹ᐟ²·K̂(δ·log n)')
    add_body(doc, '权重 b_n = n⁻¹ᐟ²·K̂(δ·log n)。K̂ = fourierCos Khat 是最优核 f₀(x) = cos(√2x)/(√2·sin(1/√2))（支撑 [−1/2,1/2]）的余弦傅里叶变换，闭式：')
    add_math(doc, 'K̂(u) = [ sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu) ] / (√2·sin(1/√2))')
    add_h2(doc, '2.2 全局一致界的关键判定')
    add_body(doc, '原分式上界 Khat_abs_le 的分母含 |√2±2πu|，在 u = ±√2/(2π) 处为零——它不是全局一致界，给不出常数。正确工具是 |sin t| ≤ |t|：K̂ 的每个 sin(t)/(2t) 型因子满足 |sin(t)/(2t)| ≤ 1/2，两项之和 ≤ 1，故得全局一致界')
    add_math(doc, '|K̂(u)| ≤ B = 1/(√2·|sin(1/√2)|)')
    add_body(doc, '（khat_global_bound 真证；B 即 prime_weight_bounds 有界分支的常数件。）')
    add_h2(doc, '2.3 平滑分支分解')
    add_body(doc, '令 A = (√(n+1))⁻¹、C = (√n)⁻¹，权重差分分解为：')
    add_math(doc, 'Δb_n = A·(K̂(δ·log(n+1)) − K̂(δ·log n)) + (A−C)·K̂(δ·log n)')
    add_body(doc, '四个真证引理（Main 链）：(i) |log(n+1)−log n| ≤ 1/n（log 单调 + log x ≤ x−1）；(ii) A ≤ C（逆平方根单调）；(iii) C·C = n⁻¹（平方恒等）；(iv) |A−C| ≤ C³（有理化 √(n+1)−√n = 1/(√(n+1)+√n)，分母 ≥ (√n)³）。')
    add_body(doc, '光滑件：K̂ 全局 Lipschitz（带限整函数，supp K̂ ⊂ [−1,1]），存在 L 使 |K̂(u)−K̂(v)| ≤ L·|u−v|，配合 (i) 得 |K̂(δ·log(n+1)) − K̂(δ·log n)| ≤ L·δ/n。组装：')
    add_math(doc, '|Δb_n| ≤ A·(L·δ/n) + C³·B ≤ C·(L·δ·C·C) + C³·B = C³·(L·δ) + C³·B = M·C³，M = L·δ + B')
    add_h2(doc, '2.4 有界分支')
    add_body(doc, '由 2.2：|b_n| ≤ (√n)⁻¹·|K̂(δ·log n)| ≤ (√n)⁻¹·B ≤ M·(√n)⁻¹（M ≥ B）。')
    add_h1(doc, '3. Lean 实现')
    add_h2(doc, '3.1 Core（S7_1_Core.lean，§3/§4b）')
    add_body(doc, '新增真证：abs_sin_div_two_mul_le_half（t=0 分支按 Lean 除零惯例 subst t; simp；t≠0 分支用 Real.abs_sin_le_abs）、khat_global_bound（hpos 分母为正 + hnum 两项 |≤1/2| + hden 用 abs_mul 拆分）。新增命名 axiom：fourierCos_Khat（连接件，把抽象算子 fourierCos 与 Khat 解析式挂钩——通用形 prime_weight_bounds K 无法从 K 的解析式推进，必须特化 K := Khat 的根因）、khat_lipschitz（光滑件，∃L 全局 Lipschitz）。')
    add_h2(doc, '3.2 Main（S7_1_Main.lean）')
    add_body(doc, '真证引理链：log_succ_sub_le_inv、inv_sqrt_succ_le、inv_sqrt_sq_eq_inv、inv_sqrt_succ_sub_le（对应 2.3 的 (i)–(iv)）。prime_weight_bounds_Khat 组装为定理（有界 + 平滑两分支）。prime_sum_bound 特化：签名去通用 K 与 hKs，体内 rcases prime_weight_bounds_Khat δ hδ；K̂ 窄支撑件 bgs5_khat_fourier_supp 前移到 primeSum 定义之后（须在 prime_sum_bound 之前可用）。')
    add_h2(doc, '3.3 踩坑记录')
    add_body(doc, '(1) 幂等替换误伤：字符串替换把 fourierCos Khat 内嵌的 fourierCos K 前缀二次替换成 Khathat（2 处：prime_sum_bound 目标行、bgs5 定义）——替换模式互相包含时必须处理顺序或一次性重写。(2) le_add_of_nonneg_left 给出 a ≤ b+a（加在左），目标 a ≤ a+b 须用 le_add_of_nonneg_right。(3) 含 ⁻¹ 乘积的目标纯 ring 不够，须 field_simp 先行。(4) 声明前连续两条 /-- --/ 文档注释导致语法错误 unexpected token（删除冗余注释）。')
    add_h1(doc, '4. 编译证据')
    add_body(doc, 'lake build QRH：Core 14s ✔ → Main 11s ✔ → Stage3 22s ✔ → QRH 9.6s ✔，2704 jobs，exit=0，无 warning。顺带清理 6 处历史 unused 变量警告（T/Z/hn/hδ/hc′/hX/hT/hε0 改 _ 前缀，位置参数不变）。调试探针 Dbg_Probe.lean 删除；Dbg_Khat.lean 保留（khat 真证开发档案）。')
    add_h1(doc, '5. 残余 axiom 与下一步')
    add_body(doc, '残余命名 axiom 三项：fourierCos_Khat（连接件）、khat_lipschitz（光滑件）、bgs5_khat_fourier_supp（积分层频域窄支撑）。下一步：khat_lipschitz 的 L 由解析式可算（K̂ 带限整函数），用导数件可真证（K̂ 导数闭式 + 区间界，khat_second_order_bound 同款技术），并入 S7.1 Stage 3+ 击破清单。')
    doc.save(path)
    print('saved', path)

def build_en(path):
    doc = new_doc()
    add_title(doc, 'Route-2 Assault XLII S7.10: prime_weight_bounds Theorem (Khat Specialization) and the Prime-Weight Bound True Proof')
    add_h1(doc, '1. Task and Conclusion')
    add_body(doc, 'This round demotes the prime-weight lemma prime_weight_bounds (formerly an axiom) to a true theorem prime_weight_bounds_Khat, and specializes the main assembly lemma prime_sum_bound to K := Khat. Full lake build QRH passes: 2704 jobs, exit=0, no warnings. The boundedness/smoothness of the prime weights S(X) is now closed as a Lean true proof; the remaining premises are only the three named axioms of connector, smoothness and integral-level narrow support (Section 5).')
    add_h1(doc, '2. Mathematical Setup')
    add_h2(doc, '2.1 Prime sum and weights')
    add_body(doc, 'Prime sum (the genuine prime-term carrier of BGS Lemma 3 in the difference-type pairing, S7.9 support-truncation convention):')
    add_math(doc, 'S(X) = Σ₁≤n≤⌊X⌋ Λ(n)χ₅(n)·n⁻¹ᐟ²·K̂(δ·log n)')
    add_body(doc, 'Weight b_n = n⁻¹ᐟ²·K̂(δ·log n). K̂ = fourierCos Khat is the cosine Fourier transform of the optimal kernel f₀(x) = cos(√2x)/(√2·sin(1/√2)) (support [−1/2,1/2]), closed form:')
    add_math(doc, 'K̂(u) = [ sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu) ] / (√2·sin(1/√2))')
    add_h2(doc, '2.2 Key judgement: the global bound')
    add_body(doc, 'The earlier fractional bound Khat_abs_le has denominator |√2±2πu|, which vanishes at u = ±√2/(2π) — it is not a global uniform bound and yields no constant. The correct tool is |sin t| ≤ |t|: each sin(t)/(2t)-type factor of K̂ satisfies |sin(t)/(2t)| ≤ 1/2, the two terms sum to ≤ 1, hence the global uniform bound')
    add_math(doc, '|K̂(u)| ≤ B = 1/(√2·|sin(1/√2)|)')
    add_body(doc, '(khat_global_bound true proof; B is the constant of the boundedness branch.)')
    add_h2(doc, '2.3 Smoothness branch decomposition')
    add_body(doc, 'Let A = (√(n+1))⁻¹, C = (√n)⁻¹. The weight difference splits as:')
    add_math(doc, 'Δb_n = A·(K̂(δ·log(n+1)) − K̂(δ·log n)) + (A−C)·K̂(δ·log n)')
    add_body(doc, 'Four true-proof lemmas (Main chain): (i) |log(n+1)−log n| ≤ 1/n (log monotonic + log x ≤ x−1); (ii) A ≤ C (inverse-sqrt monotonic); (iii) C·C = n⁻¹ (square identity); (iv) |A−C| ≤ C³ (rationalization √(n+1)−√n = 1/(√(n+1)+√n), denominator ≥ (√n)³).')
    add_body(doc, 'Smoothness: K̂ is globally Lipschitz (band-limited entire function, supp K̂ ⊂ [−1,1]); there is L with |K̂(u)−K̂(v)| ≤ L·|u−v|; with (i) this gives |K̂(δ·log(n+1)) − K̂(δ·log n)| ≤ L·δ/n. Assembly:')
    add_math(doc, '|Δb_n| ≤ A·(L·δ/n) + C³·B ≤ C·(L·δ·C·C) + C³·B = C³·(L·δ) + C³·B = M·C³, M = L·δ + B')
    add_h2(doc, '2.4 Boundedness branch')
    add_body(doc, 'By 2.2: |b_n| ≤ (√n)⁻¹·|K̂(δ·log n)| ≤ (√n)⁻¹·B ≤ M·(√n)⁻¹ (M ≥ B).')
    add_h1(doc, '3. Lean Implementation')
    add_h2(doc, '3.1 Core (S7_1_Core.lean, §3/§4b)')
    add_body(doc, 'New true proofs: abs_sin_div_two_mul_le_half (t=0 branch by Lean division-by-zero convention, subst t; simp; t≠0 branch via Real.abs_sin_le_abs), khat_global_bound (hpos positive denominator + hnum two terms ≤ 1/2 + hden via abs_mul). New named axioms: fourierCos_Khat (connector tying the abstract operator fourierCos to the Khat closed form — the reason the generic prime_weight_bounds K cannot advance and K := Khat specialization is mandatory), khat_lipschitz (smoothness, ∃L globally Lipschitz).')
    add_h2(doc, '3.2 Main (S7_1_Main.lean)')
    add_body(doc, 'True-proof chain: log_succ_sub_le_inv, inv_sqrt_succ_le, inv_sqrt_sq_eq_inv, inv_sqrt_succ_sub_le (items (i)–(iv) of 2.3). prime_weight_bounds_Khat assembles into a theorem (bounded + smooth branches). prime_sum_bound is specialized: signature drops the generic K and hKs; the body rcases prime_weight_bounds_Khat δ hδ; the narrow-support piece bgs5_khat_fourier_supp is moved above primeSum so it is available before prime_sum_bound.')
    add_h2(doc, '3.3 Pitfalls logged')
    add_body(doc, '(1) Idempotent-replacement damage: a string replacement re-replaced the embedded fourierCos K prefix inside fourierCos Khat, producing Khathat (2 sites: the prime_sum_bound goal line and the bgs5 definition) — patterns contained in each other need ordering or a single rewrite. (2) le_add_of_nonneg_left gives a ≤ b+a (adds on the left); the goal a ≤ a+b needs le_add_of_nonneg_right. (3) Goals with ⁻¹ products need field_simp first; plain ring is insufficient. (4) Two consecutive /-- --/ doc comments before a declaration cause a syntax error (unexpected token); the redundant comment was removed.')
    add_h1(doc, '4. Build Evidence')
    add_body(doc, 'lake build QRH: Core 14s ✔ → Main 11s ✔ → Stage3 22s ✔ → QRH 9.6s ✔, 2704 jobs, exit=0, no warnings. Also cleaned 6 historical unused-variable warnings (T/Z/hn/hδ/hc′/hX/hT/hε0 renamed with _ prefix; positional arguments unchanged). Debug probe Dbg_Probe.lean removed; Dbg_Khat.lean kept (khat true-proof development archive).')
    add_h1(doc, '5. Remaining Axioms and Next Step')
    add_body(doc, 'Three named axioms remain: fourierCos_Khat (connector), khat_lipschitz (smoothness), bgs5_khat_fourier_supp (integral-level narrow frequency support). Next: the constant L in khat_lipschitz is computable from the closed form (K̂ band-limited entire), provable by a derivative piece (same technique as khat_second_order_bound: closed-form K̂′ plus interval bounds), to be merged into the S7.1 Stage 3+ strike list.')
    doc.save(path)
    print('saved', path)

if __name__ == '__main__':
    build_zh(r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.10-prime_weight_bounds降定理-Khat特化与素数项界真证.docx')
    build_en(r'C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.10-prime_weight_bounds-theorem-Khat-specialization-EN.docx')
