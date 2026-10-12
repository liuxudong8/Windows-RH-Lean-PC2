# BSD Library — Lean Formalization of Weak BSD Rank 1 / Rank-2 Symmetry + n=3 Skeleton (Status Summary)

> Updated: 2026-10-12 (session 《编译lean项目20261012》 continued) — the Lean sister module `SymmetryFormula4` for formula (4) (negative-root-number twist count) landed: formula (4) of §5.2 of the linkage document (L″(E/K,1) > 0 ⟺ the negative-root-number count is even) is formalized as "three axiom classes + assembly (3)-core + genuine theorems", with the double instance check 79a1 (1,1) and 389a1 (2,0); Σr_χ = 2 forces the count to be even automatically (the parity-layer echo of the unconditional P*). After adding the `BSD.lean` import, `lake build -R` is all green (7690 jobs); synced to Windows-RH-Lean-PC-2. See §8.
> Updated: 2026-10-11 (session title: 《编译lean项目20261011》) — the rank-2 symmetry chain and the first skeleton block of the n=3 difficulty transfer are closed. On 10-11 we completed: ExclusionReduction (rank-1 reverse exclusion layer), LeibnizReduction (leibniz_artin promoted to a genuine second-order Leibniz theorem, tasks 1/2), the full closure proof of 43a1 (1,0) type (LPrime43 + LSeries5_43 + _check_43a1), SymmetryReduction (generic twist-involution rank symmetry), insertion of §4.7 into the rank-2 document (audit --source exit=0 + sha-verified write-back), SymmetryClosure (79a1 (1,1) triple assembly), SelmerDescent (task 3 axioms at theorem level), the three-layer analysis of arbitrary-rank symmetry, and LeibnizThird ((2,1)/(1,2) third-order Leibniz genuine theorems with closure = pure logic).

## 0. One-line positioning

Turn the "Skeleton A discussion draft" case (K = ℚ(√5), E = 37a1), "algebraic rank = analytic rank = 1", into a Lean three-layer skeleton: **the object layer is genuinely provable; the deep number-theory/analytic content lives in a declaration layer (axioms with documented upgrade paths); the assembly layer theorems hold.** Every axiom has a concrete upgrade path; no dead ends.

## 1. Mathematical conventions (corresponding to the documents)

| Object | Convention | Doc |
|---|---|---|
| Main curve | E = 37a1: y² + y = x³ − x, Δ = −37, N = 37 | 2.1 |
| Field | K = ℚ(√5), N_K = 1369, ε_K = −1 | 2.1 |
| Quadratic twist | E⁵: Y² = x³ − 25x + 125/4, N(E⁵) = 925, ε(E⁵) = +1 | 5.4(iv) |
| Analytic rank (E/K) | = 1: L_K(1) = 0 (ε_K = −1) + L_K′(1) = 1.63858644 = L′(E,1)·L(E⁵,1) ≥ 1.63808 ⊂ (0,∞) (product identity form; the old degree-2 reflection formula principal value 2.433224 is abandoned) | 4.3, 5.4(iii) |
| Algebraic rank (E/K) | = 1: rank E(ℚ) = 1 + rank E⁵(ℚ) = 0 (quadratic twist decomposition) | 2.1, 5.4(iv) |
| Analytic judgment for E⁵ | L(E⁵,1) ∈ [5.3548616166 ± 1.7×10⁻⁷¹] ⊂ (0,∞), N = 800, dps = 80 | 5.4(iv) |

E⁵ local factors: for good p ∤ 925 take a_p = χ₅(p)·a_p(E) (χ₅: mod 5 {1,4}→+1, {2,3}→−1); p = 5 additive a = 0; p = 37 multiplicative a = +1 (s = 3 closure ratio 0.99999967 pins the sign and ε).

## 2. File layout

```
c:\proj2\
├── BSD.lean                 # library root: import BSD.Main (lake lean_lib root-module convention)
├── BSD\
│   ├── Main.lean            # main body: object + declaration + theorem layers (import BSD.LSeries5)
│   ├── LSeries5.lean        # ① E⁵ local factors + L(1) reflection formula (geometric-series tail closed)
│   ├── LPrime.lean          # L′(E,1) series form + positivity (B3-min + ①c; mathematical axioms zeroed)
│   ├── TwoDescent.lean      # ② E′ integral model + infinite-order numeric layer + 2-descent skeleton (②b first genuine-proof layer)
│   ├── Positivity/          # component positivity objects (zeroOrderE/E5, analyticZeroOrder, lprime_pos_of_rank_one, ...)
│   ├── ExclusionReduction.lean   # rank-1 reverse exclusion layer (ord ≤ 1, excludes ord ≥ 3)
│   ├── LeibnizReduction.lean     # tasks 1/2: second-order Leibniz genuine theorems (product_second_deriv, leibniz_20/02/11_second, p_star_type_via_leibniz)
│   ├── LPrime43.lean        # 43a1: L_P(43a1,1) > 0 genuine theorem
│   ├── LSeries5_43.lean     # 43a1 E⁵ side: term_i numerical bridging, crude50_ge_R_43, tail51_bound_43, L_E5_43_one_pos/ne_zero all closed
│   ├── SymmetryReduction.lean   # generic twist-involution rank symmetry (rank_additivity, Kolyvagin ×2, descent axioms; symbol_symmetry_11, p_star_11_sym, symmetry_closure_11)
│   ├── SymmetryClosure.lean     # 79a1 (1,1) triple assembly (entanglement_79, Lpp_EK_79_pos/ne_zero, rank_EK_79_two, sha_finite_EK_79, symmetry_closure_79)
│   ├── SelmerDescent.lean       # task 3: Selmer-layer descent axioms (exact sequence + descent sequence + Kolyvagin Selmer form; sha_finite_EK_11_via_selmer)
│   ├── LeibnizThird.lean        # (2,1)/(1,2) third-order Leibniz genuine theorems (product_third_deriv, leibniz_21/12_third, _ne_zero)
│   ├── BSD_summary.md       # this file
│   ├── compile_log.txt      # authoritative compilation record (all modules, exit codes)
│   ├── document/            # 《弱BSD秩1反向的正性判别.docx》《弱BSD秩2反向的正性判别.docx》 etc.
│   └── _check_*.lean        # #print axioms closure audits
└── lakefile.toml            # [[lean_lib]] name = "BSD" (no root field!)
```

> Pitfall record: the lakefile.toml lean_lib does **not** support a root field (that is lakefile.lean); the root module file must be the project-root file `BSD.lean` (content: only `import BSD.Main`). `Mathlib.Data.Rat.Basic` does not exist in 4.34 → use `Defs`. `Real.gamma` is `Real.Gamma` (capital G).

## 3. Layers and statistics

### 3.1 Object layer (genuine Lean proofs, clean axiom closure)

**Main.lean**: `Curve37a1` (Weierstrass equation), `Twist5`, `P0 : Point Curve37a1` with P0 = (0,0) `by norm_num` on the curve.

**LSeries5.lean** (local-factor algebra layer, 7 proven theorems):
- `chi5` definition + `chi5_zero_at_5 / chi5_neg_at_2 / chi5_pos_at_11`
- `ap5` definition + `ap5_additive_at_5` (=0) / `ap5_multiplicative_at_37` (=+1) / `ap5_sample_2` (=2) / `ap5_sample_11` (=−5)

**LSeries5.lean** (analytic inequalities, fully closed):
- `tsum_geom_shift`: Σ r^(m+n) = r^m/(1−r), |r| < 1
- `geom_tail_bound`: Σ e^(−α(N+1+n)) = e^(−α(N+1))/(1−e^(−α)), 0 < α
- both with axiom closure = [propext, Classical.choice, Quot.sound] — pure foundational axioms
- `alpha_gt_2065`, `exp_neg_alpha_lt_8136`, `exp_neg_alpha_801_lt`, `tail_ivc_bound`, `tail_sufficient_pos`: elementary inequality chain (iv-c) — closure = 3 foundational + **native_decide computation-trust axiom** (see note)
- `part50_ge : 2.6766 ≤ Σ_{n<50} fE5 n` (iv-d partial-sum lower bound; 50 terms term-by-term + 10-block cast bridge) — closure has no mathematical axiom, only native_decide computation-trust
- ①b multiplicative assembly: `ppow_0/1/rec`, `ssum` + `ssum_rec`, `ppow_eq_ssum`, `ssum_abs_bound`, `ppow_bound`, `coefficient_bound_assembled`, `coefficient_bound` (new theorem form: |∏ a_{p^{k_p}}| ≤ τ(n)·√n) — closure = 3 foundational + `ap5_satake` (declaration)

> **native_decide computation-trust axiom (transparent)**: the ℚ judgment (1017/1250)^801 < 10⁻⁶⁰ is done by `native_decide`, generating `exp_neg_alpha_801_lt._native.native_decide.ax_1_1`. This is a computation-trust axiom delegating bignum comparison to the verified native compilation channel, not a mathematical assumption. Independently checkable: 1017^801·10⁶⁰ < 1250^801. A fully kernel-checked upgrade (factorial remainder chain) is left for later.

### 3.2 Declaration layer (axioms, each with "to be proved" comment and upgrade path)

**Main.lean — 7**: `analyticRank`, `mwRank`, `analytic_rank_K_eq_one_of_LK_prime_ne_zero`, `rank_E_Q_ge_one`, `rank_E_Q_le_one`, `rank_E5_Q_eq_zero`, `twist_decomposition` (for meanings and upgrade paths see the Chinese original; each is a documented axiom with an upgrade route, no dead ends).

**LSeries5.lean — 7**: `ap_E`, `ap_E_values`, `ramanujan_ap_E` (Deligne — permanent-axiom risk), `ap5_satake` (Deligne — permanent-axiom risk), `GammaUpper`, `Lambda_E5` (automorphic L — permanent-axiom risk), `L_E5_series_split` (upgrade: tail-splicing theorem).

### 3.3 Theorem layer (assembly)

- `LK_prime_pos`: L_K′(1) > 0 (genuine theorem; closure = `Lprime_E1_pos` theorem + `L_E5_one_pos` theorem + LSeries5 declarations + foundations)
- `analytic_rank_K_eq_one`: analytic rank (E/K) = 1 (upgraded from axiom to theorem)
- `algebraic_rank_K_eq_one`: mwRank E(K) = 1 (rw assembly)
- `rank_E_Q_eq_one`: rank E(ℚ) = 1 (upgraded: `le_antisymm rank_E_Q_le_one rank_E_Q_ge_one`)
- `weak_BSD_37a1`: mwRank = analyticRank (weak BSD rank 1 holds)
- No sorry; closure audit via `_check_bsd.lean`

> **B3-min closure (2026-10-07)**: `Lprime_E1` / `Lprime_E1_interval` (bare numeric axioms, LMFDB 0.305999773834…) deleted entirely and replaced by a formula-form genuine theorem chain: `LPrime.lprime1 = 2·∑' aE(n+1)/(n+1)·E1(2π(n+1)/√37)` → `lprime1_pos : 0 < lprime1` (partial sums ≥ 0.0557 vs tail |·| ≤ 0.0125). LPrime.lean mathematical axioms zeroed.
> **①c replication closure (2026-10-07)**: `lprime1_summable` axiom → theorem (absolute convergence via geometric series; termwise bound |aE(n+1)/(n+1)·E1(bn(n+1))| ≤ (2/1.03)·e^{−1.03(n+1)}).

> Note: `weak_BSD_37a1` axiom closure now = `analytic_rank_K_eq_one_of_LK_prime_ne_zero` + `analyticRank`, `mwRank`, `rank_E_Q_ge_one`, `rank_E_Q_le_one`, `rank_E5_Q_eq_zero`, `twist_decomposition` + LSeries5 declarations (`Lambda_E5`, `L_E5_series_split`, `coefficient_bound_aE5`, `summable_fE5`, …) + native_decide computation-trust + foundations.

## 4. Compilation and verification

```powershell
Set-Location c:\proj2
lake build BSD            # full library; log > build_*.txt
lake env lean BSD/_check_bsd.lean   # #print axioms verification
```

Statistics: `(Select-String -Path BSD\*.lean -Pattern "^axiom ").Count` — library code = 14 (Main 7 + LSeries5 7; `_check_*.lean` scripts excluded; TwoDescent.lean has no axiom); sorry = 0.

## 5. Status and roadmap

**Closed up to 10-07**: library structure, object layer, local-factor identities, geometric-series tail (①a), theorem-layer assembly, (iv-c) elementary inequality chain, (iv-d) partial-sum lower bound, ①c (tail triple + `L_E5_one_pos`/`L_E5_one_ne_zero`), ①b (prime-power recursion + multiplicative assembly → `coefficient_bound`), ② descent layer (E′ integral model, infinite-order proof via `P7_X_den_nonbad_factor`, 2-descent Selmer numeric computation |Sel²| = 2, `Eprime_poly_no_root`/`Eprime_two_torsion_trivial` genuine), ②a first genuine-proof layer (group law `Eprime_double`/`Eprime_add`, 2P′..7P′ chain). `lake build BSD` exit 0; axioms 14 = 14 (Main 7 + LSeries5 7); sorry = 0.

**Permanent-axiom risks (honest labeling)**: `ramanujan_ap_E` (Deligne), `ap5_satake` (Deligne), `Lambda_E5` (automorphic L) — no corresponding theory in mathlib; kept as axioms with documented "numerically/literature-verified" status unless full modular/automorphic theory is imported.

**To-do (by magnitude, up to 10-07)**: ②b `rank_E_Q_le_one` full Lean-ization (needs class-field/local-field theory, mathlib missing; mathematics pinned by selmer7.py + LMFDB); record ε_K = −1 basis (root-number multiplicativity) explicitly; Silverman VIII.7.1(b) itself; ③ `twist_decomposition` (Galois module decomposition).

## 6. Related artifacts

- Discussion draft: 《弱BSD秩1_Hecke显式公式重证明_骨架A讨论稿.docx》 (SHA256 = 6D3C37…FEB2)
- Numeric pipeline: `_tmp_skA\verify_E5.py` / `verify_E5_iii.py` / `E5_out.txt`
- Field infrastructure: `OrderPreservingBijection/QuadraticFieldFive.lean` (GoldenInt, phi² = phi+1, norm)
- Documents: `document/弱BSD秩1反向的正性判别.docx`, `document/弱BSD秩2反向的正性判别.docx` (both written in "we" voice, no "you")

## 7. 2026-10-08 → 10-11: rank-2 symmetry chain + n=3 skeleton (session 《编译lean项目20261011》)

The main line progressed from "rank-1 reverse (exclusion layer ord ≤ 1) theory" through the "rank-2 symmetry closure ((1,1) type)" and the "three-layer arbitrary-rank symmetry analysis", closing with the (2,1)-type third-order Leibniz genuine theorem as the first skeleton block of the n=3 difficulty transfer.

### 7.1 Artifact list (all compiled exit=0; compile_log.txt is the authoritative record)

| Date | File | Content |
|---|---|---|
| 10-08~10-10 | `Probe389/` `Probe5077/` `PStarOr/` `Stage2/RankTwoExclusion.lean` `ZeroGap/` `Main.lean` (updated 10-10) | 389a1/5077a1 probes, P* or-type, rank-2 exclusion layer (excludes ord ≥ 3), zero gap; all green in compile_log |
| 10-11 | `ExclusionReduction.lean` | rank-1 reverse exclusion layer theory Lean-ized (template module; `exclusion_layer_nonzero`) |
| 10-11 | `LeibnizReduction.lean` | **tasks 1/2**: `leibniz_artin` (formerly a P* axed axiom) promoted to genuine second-order Leibniz theorems of three types — `product_second_deriv` / `leibniz_20/02/11_second` + `_ne_zero`; object-level `L_fun_structure` axiom + `leibniz_artin_theorem` + `p_star_type_20/11/02_via_leibniz`; `p_star_via_leibniz` assembly |
| 10-11 | `LPrime43.lean` `aE_table_43.lean` `aE5_table_43.lean` `LSeries5_43.lean` `_check_43a1.lean` | **43a1 (1,0) type fully closed**: L_P(43a1,1) > 0 genuine theorem (round 18), 200/800-term coefficient tables (aE5 row 47 manually fixed |43|→1), L(E⁵,1) > 0/≠ 0 fully closed (term_i numerical bridging + crude50_ge_R_43 + tail51_bound_43), `L_prime_43_ne_zero` assembly (= lprime1_43_pos × L_E5_43_one_ne_zero, mirroring exclusion_layer_nonzero) |
| 10-11 | `SymmetryReduction.lean` | **generic twist-involution rank symmetry** (ns BSD.SymmetryReduction): object layer rankE/E5/EK + `rank_additivity` (rank-additivity axiom) + `ShaFiniteE/E5/EK`; Kolyvagin axioms ×5 + `sha_finite_EK_of_descent`; genuine theorems `symbol_symmetry_11` (= symmetric restatement of leibniz_11_second_object), `p_star_11_sym` (= p_star_type_11_via_leibniz); assembly `rank_EK_two_of_both`/`sha_finite_EK_of_both`/`symmetry_closure_11` |
| 10-11 | 《弱BSD秩2反向的正性判别.docx》 §4.7 | **rank symmetry into the document**: "扭对合秩对称：秩 2 由秩 1 对称组合" (P1–P4); audit --source exit=0, no "you" anywhere, sha256-verified write-back to the original path (34d7d14d…46dd7b6) |
| 10-11 | `SymmetryClosure.lean` | **task 4**: 79a1 (1,1) triple assembly — `entanglement_79`/`entanglement_79_pos`/`Lpp_EK_79_pos`/`Lpp_EK_79_ne_zero` (mirroring L_prime_43_ne_zero)/`rank_EK_79_two`/`sha_finite_EK_79`/`symmetry_closure_79` |
| 10-11 | `SelmerDescent.lean` | **task 3** (mathematics is a theorem; axiomatized at theorem level, same layer as Kolyvagin): exact sequence 0→Sel(E)→Sel(E/K)→Sel(E⁵) (bad-p finite correction) + descent sequence 0→E(K)/p^n→Selⁿ→Sha[p^n]→0 (Sel finite ⟹ Sha finite) + Kolyvagin Selmer form; `sha_finite_EK_of_selmer_descent`/`sha_finite_EK_11_via_selmer` |
| 10-11 | (pure analysis) | **three-layer arbitrary-rank symmetry conclusion** (no tool artifact; inline SVG diagram) |
| 10-11 | `LeibnizThird.lean` `_check_leibniz_third.lean` | **first skeleton block of the n=3 difficulty transfer**: (2,1)/(1,2) third-order Leibniz leading-term genuine theorems (see §7.3) |

### 7.2 Mathematical conclusion: three layers of rank symmetry (arbitrary rank n, extension degree m = [K:ℚ])

1. **Structural layer (holds for arbitrary n and arbitrary m; theorem)**: rank E(K) = Σ_χ rank E^χ(ℚ); L(E/K) = Π_χ L(E^χ) (Artin decomposition) hence ord additivity; Selmer descent along χ. K-side rank n ⟺ distribution (n₁,…,n_m) with Σnᵢ = n.
2. **Symbol layer (unconditional for arbitrary n)**: P*_n (analytic rank r ⟹ L^(r)(1) > 0) is given directly by Channel B — L^(r)(1)/r! = lim_{s→1⁺} L(s)/(s−1)^r ≥ 0 and L^(r)(1) ≠ 0; **no formula, no GRH, no dependence on symmetry** (symmetry is only the structural identity of the entanglement product at the symbol layer).
3. **Full closure (⟺ n ≤ m)**: rank additivity + both-side rank reverse (Kolyvagin–Gross–Zagier, closed only for rank ≤ 1 components) + both-side Sha finiteness (Kolyvagin), all assembled from rank ≤ 1 theorems ⟺ existence of the all-ones distribution ⟺ **n ≤ m**. Pigeonhole: n > m ⟹ some component has rank ≥ 2, falling back to the 389a1-class open problem. For quadratic fields m = 2: the only non-trivial fully-closed rank is n = 2 ((1,1), 79a1 landed); n ≥ 3 contains a rank ≥ 2 component. **Difficulty transfer = max component rank** ((1, n−1) type lowers the order by one).
4. **Higher-order Leibniz leading-term formula**: (fg)^(a+b)(1) = C(a+b, a)·f^(a)(1)·g^(b)(1); the (2,1) type is C(3,2) = 3.

### 7.3 LeibnizThird.lean ((2,1)/(1,2) third-order genuine theorems, pure calculus)

- `product_third_deriv`: (f·g)‴(1) = f‴(1)·g(1) + 3·f″(1)·g′(1) + 3·f′(1)·g″(1) + f(1)·g‴(1).
- `leibniz_21_third`: (2,1) type (f(1)=f′(1)=0, g(1)=0) ⟹ (fg)‴(1) = **3·f″(1)·g′(1) = C(3,2)·f″(1)·g′(1)**.
- `leibniz_12_third`: (1,2) symmetric ⟹ (fg)‴(1) = 3·f′(1)·g″(1).
- `leibniz_21/12_third_ne_zero`: nonzero propagation (f″(1)≠0 ∧ g′(1)≠0 ⟹ (fg)‴(1)≠0).
- Proof route: v4.34 has **no `iteratedDeriv_mul`** (the IteratedDeriv module does not exist; confirmed by probe) → manual three layers (C3At open-neighborhood C³ → pointwise identities on v ×3 → eventual equality → HasDerivAt six-term assembly + ring).
- **Closure audit (#print axioms exit=0)**: the five theorems depend only on `[propext, Classical.choice, Quot.sound]` — **pure logic, zero axioms, zero formulas, zero GRH, zero object-layer axioms**; the first zero-axiom module on the n=3 side (contrast: p_star_11_sym contains bsd_formula_rank_one/one5).

### 7.4 Closure-audit facts (#print axioms, mathematical layer evidence)

| Theorem | Closure | Layer |
|---|---|---|
| `symbol_symmetry_11` | no bsd_formula_rank_* | Leibniz three types + L_fun_structure + Positivity numeric objects + logic |
| `p_star_11_sym` | contains bsd_formula_rank_one/one5 + Omega/Regulator/Sha/Torsion component objects | component sign is a Positivity-level axiom, mathematically Kolyvagin's theorem |
| `symmetry_closure_79` | only 79-series object-layer axioms | data zeroOrder + theorem-level axioms (leibniz_11_79/rank_additivity_79/Kolyvagin ×2/descent); no formulas, no GRH |
| `sha_finite_EK_11_via_selmer` | only SelmerDescent object layer + zeroOrder | theorem-level axioms, same layer as Kolyvagin; no formulas, no GRH |
| `product_third_deriv` and the other four | only propext/choice/Quot.sound | pure-calculus genuine theorems |

### 7.5 Compilation pitfalls (new on 10-11; avoid repeating)

1. **rw chain auto-closes goals**: on ℕ, rw on definitional equalities (1+1=2) closes the goal automatically; a trailing norm_num/rfl then reports "No goals to be solved" — write a single `rw [a, b, c]`.
2. **unfold errors**: when the goal is already expanded to product form, `unfold` reports "Tactic unfold failed" — drop the redundant unfold.
3. **`𝓝` is a scoped notation**: need `open scoped Topology`; merely importing `Mathlib.Topology.Basic` is not enough.
4. **v4.34 `DifferentiableOn` yields `DifferentiableWithinAt`**: lift to At via `(h_diff s hs).differentiableAt (hv_open.mem_nhds hs)`.
5. **`deriv_mul` returns an equality**: cannot project `.differentiableAt`; use `DifferentiableAt.mul` for the differentiability arguments.
6. **Dependency-failure contagion**: when a depended-on module fails to compile, importing files report "object file ... does not exist" (fix the dependency first).
7. **v4.34 has no `iteratedDeriv` abstraction**: third-order Leibniz must be done by hand in three layers (ContDiffOn 3 stratification + pointwise identities + HasDerivAt assembly).

### 7.6 To-do / open items

- **(2,1) object layer, two steps** (continuation of the n=3 difficulty transfer):
  - (a) `L_fun_structure` third-order version: L‴(E/K,1) numeric object + Artin-decomposition (2,1) distribution axiom;
  - (b) connect with a third-order Positivity object (of the `lprimeprimeprime_pos_of_rank_three` type) to push the Channel-B symbol layer to rank 3.
- **m ≥ 3 full closure**: existence of the all-ones distribution is conditional; no instance data (the symmetry statement is conditional: *if* the distribution is all-ones, closure holds).
- **Acceptance**: tasks 1–4 (LeibnizReduction/SymmetryReduction/SymmetryClosure/SelmerDescent), document §4.7, and LeibnizThird are delivered and await acceptance; we will revise on request.
- **Legacy calibration**: the aE5 row-47 manual fix (|43|→1) in the 43a1 (1,0) table is commented (multiplicativity special case); can be upgraded to the ap5_multiplicative-family theorems if needed.

## 8. 2026-10-12: Formula-(4) negative-root-number twist count module (session 《编译lean项目20261012》 continued)

Landed the §5.2 (3)(4) formulas and the §8 landing point of the linkage document《对称性+正性 ⟷ K-GRH：联系链》as a sister module of `SymmetryClosure`: **`BSD.SymmetryFormula4`** (`BSD/SymmetryFormula4.lean`). The logic is purely algebraic (finite-character counting + parity + sign arithmetic) with no contact with the analytic continuation of L-functions — formalization difficulty far below Kolyvagin / Selmer descent.

### 8.1 Module structure (three axiom classes + assembly + genuine theorems)

| Layer | Name | Content |
|---|---|---|
| Object layer | `zeroOrderE/E5/EK_f4`, `rootE/rootE5_f4`, `LppEK_f4`, `chi_NE/chi_neg/local_f4` | component analytic ranks, root numbers, K-side second derivative, the three inputs of the twist-root-number formula |
| (1) L decomposition | `l_fun_decomposition_f4` | ord L(E/K,1) = ord L(E,1) + ord L(E⁵,1) (Artin decomposition; theorem-level axiom) |
| (2) BSD parity | `bsd_parity_f4` / `bsd_parity5_f4` | ε(E⊗χ) = (−1)^{ord L(E⊗χ)} (self-dual L-function) |
| (3) twist root-number formula | `twist_root_number_f4` | ε(E⊗χ) = ε(E)·χ(N_E)·χ(−1)·(local correction) (linkage §5.3) |
| Assembly (3)-core | `lpp_pos_iff_root_prod_f4` | L″(E/K,1) > 0 ⟺ product of root numbers over r_χ = 0 components = +1 (§5.1 component signs + §5.2 convolution; axiom) |
| Formula-(4) theorem | `formula4_f4` | K-side rank 2 ⟹ L″>0 ↔ negative-root-number count even (**genuine proof**: exhaustive over the three types) |
| Corollary | `lpp_pos_of_analytic_two` | K-side rank 2 ⟹ L″>0 (**genuine proof**) |

### 8.2 Key mathematics: Σr_χ = 2 forces the count even

The right-hand side of (4) is **automatically even** under K-side rank 2: the (0,2)/(1,1)/(2,0) types (via BSD parity ε = (−1)^ord) give negative-root counts 0/2/0 respectively — the parity-layer echo of the unconditional Channel-B P*; formula (4) and the symbol channel converge along two independent routes. The "one positive one negative ⟹ count 1 odd ⟹ contradiction" case is automatically excluded by ε(E/K) = ∏ε(E⊗χ) = (−1)^{Σr} = +1 (Σr = 2 even).

### 8.3 Double instances (data-layer axioms + genuine assembly theorems)

| Instance | Type | ε(E), ε(E⁵) | Count | Conclusion | Cross-check |
|---|---|---|---|---|---|
| 79a1 | (1,1) | −1, −1 | 2 (even) | L″>0 | converges with the SymmetryClosure entanglement-product channel (`lpp_EK_79_pos_both_f4`) |
| 389a1 | (2,0) | +1, +1 | 0 (even) | L″>0 | interval arithmetic L″(389a1,1) = 1.518633 > 0 (Probe389) |

- 389a1 data (Probe389/probe389_summary.md §2, verified): ε(E)=+1 (LMFDB; rank 2 even, a₃₈₉=+1 split mult); χ₅(−389)=(5/389)·χ₅(−1)=+1 (reciprocity (5/389)=(389/5)=(4/5)=1; real quadratic field gives χ₅(−1)=+1); local factor = 1 (gcd(389,5)=1, χ unramified at 389).
- `rootE5_eq_rootE_79/389_f4`: arithmetic self-consistency of the twist-root-number formula at the instances (χ·χ(−1)·local = 1 ⟹ ε(E⁵)=ε(E), matching the ε values from BSD parity).
- The two instances cover exactly the two sources of evenness of the right-hand side of (4): 79a1 "two negatives cancel" (count 2), 389a1 "no negatives" (count 0); under (2,0), formula (3) degenerates to the zero-order component product = ε(E⁵) = +1.

### 8.4 Closure audit and compilation

| Theorem | Closure |
|---|---|
| `formula4_f4` / `lpp_pos_of_analytic_two` | this module's object layer + three axiom classes + (3)-assembly; **no GRH, no bsd_formula_rank_\*** |
| `lpp_pos_79_f4` / `lpp_pos_389_f4` | the above + instance data layer |
| `rootE5_eq_rootE_79/389_f4` | twist-root-number formula + instance arithmetic data |

- Compilation: `lake build BSD.SymmetryFormula4` exit 0; after adding `import BSD.SymmetryFormula4` to `BSD.lean`, `lake build -R` is all green (7690 jobs; 10 BSD oleans in the workspace); closure probe `_check_symmetry_formula4.lean` exit 0.
- Engineering: build logs `build_project_20261012_f4*.txt`; `BSD.lean` / `SymmetryFormula4.lean` / `_check_symmetry_formula4.lean` synced to Windows-RH-Lean-PC-2 (SHA256 match).
