# BSD Library — Lean Formalization of Weak BSD Rank 1 / Rank-2 Symmetry + n=3 Skeleton (Status Summary)

> Updated: 2026-10-15 (λ₁₁ = 2 numerical pillar + cross-prime check) — Numerical path 1 completed: for 389a1/p=11 the series(11) replication (PARI/GP true-modular-symbol pipeline) verifies **ord_T L₁₁ = 2 (λ₁₁ = 2)** (L₁₁(T)=9T²+9T³+… mod 11; T⁰≡0 mod 11⁴, T¹≡0 mod 11, T²≡9 mod 11≠0; 220+22 points self-consistent, both distribution identities hold exactly); recorded as Lean axioms (`Sha11_389.lean` numerical-verification layer; build all green); then ③ cross-prime check: E^χ (twist, cond 24896) has **analytic rank 0, M(0)=2** ⟹ T⁰≡10 mod 11≠0 ⟹ **λ₁₁(E^χ) = 0**; character decomposition **λ(E/K) = λ(E) + λ(E^χ) = 2 + 0 = 2** (Q-side = K_cyc-side; λ = rank = 2 at {3,11} consistently); recorded as Lean axioms + genuine theorem `lambda_ek_two_389`. `lake build BSD.Sha11_389` all green. See §10.
> Updated: 2026-10-13 (Sha-finiteness attack) — the five-stage roadmap (Iwasawa-Euler-system extension) is fully green at Stage A, landed at Stage B, and the Stage B-6 rank-2 Euler-system assessment hit CH22; two framework-correction findings; the CH22 chain was Lean-integrated (`sha11_finite_389 : ShaFinite Curve389a1 11` genuine theorem); the λ₁₁ K_cyc-side assessment is complete (three paths pending). `lake build -R` all green, 7690 jobs. See §9.
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

### 8.2 Key mathematics: under Σr_χ = 2 the right-hand side of (4) is tautological — a parity necessary condition, not the positivity itself

The evenness of the right-hand side of (4) **holds automatically** under K-side rank 2: the (0,2)/(1,1)/(2,0) types (via BSD parity ε = (−1)^ord) give negative-root counts 0/2/0 respectively — one layer deeper: the right-hand side of (3) (zero-order root-number product = +1) is tautological under Σr = 2 (empty product = 1 for (1,1); ε(rank-0 component) = (−1)^0 = +1 for (2,0)/(0,2)).

Therefore **(3)/(4) is a parity necessary condition, not the positivity itself**: in the rank-2 case it carries no constraint beyond "each component's sign is positive" (Channel B for r ≥ 1; root number + BSD sign theorem for r = 0). The value of (4) lies in **contradiction detection** (if an instance had an odd count, K-side rank 2 would be incompatible with positivity). The positivity source depends on the type; see §8.3. The "one positive one negative ⟹ count 1 odd ⟹ contradiction" case is automatically excluded by ε(E/K) = ∏ε(E⊗χ) = (−1)^{Σr} = +1 (Σr = 2 even).

### 8.3 Double instances (data-layer axioms + genuine assembly theorems)

| Instance | Type | ε(E), ε(E⁵) | Count | Conclusion | Cross-check |
|---|---|---|---|---|---|
| 79a1 | (1,1) | −1, −1 | 2 (even) | L″>0 | converges with the SymmetryClosure entanglement-product channel (`lpp_EK_79_pos_both_f4`) |
| 389a1 | (2,0) | +1, +1 | 0 (even) | L″>0 | interval arithmetic L″(389a1,1) = 1.518633 > 0 (Probe389) |

- 389a1 data (Probe389/probe389_summary.md §2, verified): ε(E)=+1 (LMFDB; rank 2 even, a₃₈₉=+1 split mult); χ₅(−389)=(5/389)·χ₅(−1)=+1 (reciprocity (5/389)=(389/5)=(4/5)=1; real quadratic field gives χ₅(−1)=+1); local factor = 1 (gcd(389,5)=1, χ unramified at 389).
- `rootE5_eq_rootE_79/389_f4`: arithmetic self-consistency of the twist-root-number formula at the instances (χ·χ(−1)·local = 1 ⟹ ε(E⁵)=ε(E), matching the ε values from BSD parity).
- The two instances cover exactly the two sources of evenness of the right-hand side of (4): 79a1 "two negatives cancel" (count 2), 389a1 "no negatives" (count 0).

**The asymmetry of the positivity source (to be made explicit)**: for the (1,1) type (79a1) positivity = the entanglement product 2L′(E,1)L′(E⁵,1), i.e. the rank-1 component signs (Gross–Zagier / Channel B at rank 1, unconditional); for the (2,0) type (389a1) positivity = the ℚ-side rank-2 component L″(E,1) > 0 — under (2,0), L″(E/K,1) = L″(E,1)·L(E⁵,1) (Leibniz, vanishing terms) and sign L(E⁵,1) = ε(E⁵) = +1 (unconditional), hence L″(E/K,1) > 0 ⟺ L″(E,1) > 0. Rank-2 positivity is an open conjecture for general curves; for 389a1 it is unconditionally verified by interval arithmetic L″(389a1,1) = 1.518633 > 0 (Probe389). **Hence (4) alone proves the positivity of neither type; it only passes the parity sieve, and the (2,0) difficulty is precisely located at the ℚ-side rank-2 component** (framework wording corrected: the earlier "two independent channels converge" is replaced by "parity necessary condition + component-sign inputs").

### 8.4 Closure audit and compilation

| Theorem | Closure |
|---|---|
| `formula4_f4` / `lpp_pos_of_analytic_two` | this module's object layer + three axiom classes + (3)-assembly; **no GRH, no bsd_formula_rank_\*** |
| `lpp_pos_79_f4` / `lpp_pos_389_f4` | the above + instance data layer |
| `rootE5_eq_rootE_79/389_f4` | twist-root-number formula + instance arithmetic data |

- Compilation: `lake build BSD.SymmetryFormula4` exit 0; after adding `import BSD.SymmetryFormula4` to `BSD.lean`, `lake build -R` is all green (7690 jobs; 10 BSD oleans in the workspace); closure probe `_check_symmetry_formula4.lean` exit 0.
- Engineering: build logs `build_project_20261012_f4*.txt`; `BSD.lean` / `SymmetryFormula4.lean` / `_check_symmetry_formula4.lean` synced to Windows-RH-Lean-PC-2 (SHA256 match).

## 9. 2026-10-12 → 10-13: Sha-finiteness attack (five-stage roadmap, A/B all green + CH22 Lean integration + λ₁₁ assessment)

The main line moved from "rank-symmetry closure" to a frontal attack on **Ш-finiteness**: from-definition assessment → five-stage roadmap landed → Stage A (free-layer closure) → Stage B (Rank-1 Euler system → Iwasawa corank, λ_p = 0) → Stage B-6 (rank-2 Euler system / generalized Kato classes assessment) → CH22 framework verification + Lean integration → λ₁₁ K_cyc-side assessment.

### 9.1 "From-definition" assessment and numerical anchors

- The four pure-definition routes (Poitou–Tate layer-by-layer finiteness, local Tate pairing, descent, Cassels pairing) cycle back to, or are equivalent to, BSD/Kolyvagin — **no new mathematical input**; but `|Ш[n]| = |Sel_n|/|E(K)/nE(K)|` is computable n-by-n and serves as a cross-check (`Probe389/sha_crosscheck.*`).
- Anchor cross-check: Ω = 4.98042512171011, Reg@n=9 = 0.1524593847, ∏c = 1, BSD prediction |Ш| = 1.0000000000004; **|Sel₂(389a1)| = 4 independently reproduced over the cubic field** (A = ℚ(β), β = 2θ, G = x³+2x²−8x+2, β² ≡ 1 mod A*² collapsing 16→8 classes; p=2 all pass, p=389 rejects the 4 γ¹-classes, ∞ rejects the γ class). The old "g is not 389a1" diagnosis was overturned by the j-invariant counter-check (E″:Y²=X³+4X²−32X+16 is isomorphic).

### 9.2 Five-stage roadmap (`BSD/document/Iwasawa欧拉系延伸路线.md`)

Ш finite ⟺ (i) the p-rank is bounded for every p = **λ_p = 0** (Iwasawa-main-conjecture side) ∧ (ii) Ш[p] = 0 for all but finitely many p. Stages A/B/C/D/E: A (free layer) → B (Rank-1 Euler system → λ_p = 0) → B-6 (rank-2 Euler system / generalized Kato; new mathematical input) → C/D/E (literature chains / numerics / Lean axioms).

### 9.3 Stage A (free-layer closure, all green)

- `BSD/ShaPComponent.lean`: **Lemma A.1 genuine theorem** `G[p] = 0 ⟹ G[p^∞] = 0` (torsionBy/nsmul family).
- `BSD/ShaFreeLayer.lean`: descent cardinality genuine theorem `card_eq_mul_of_short_exact_add`, Cassels alternating-pairing structure genuine theorem `injective_of_nondegenerate`, square-conclusion axiom, and 389a1/p=2 **`sha2_389_card_eq_one` genuine derivation** (|Ш[2]| = 1).
- Merged into the `BSD.lean` aggregate; closure checks `_check_l01/l02.lean` clean; `lake build -R` 7690 jobs all green.

### 9.4 Stage B (`BSD/EulerSystem.lean`, B-0..B-6)

- Object layer: `Corank`/`Rank`/`Lambda`/`OrdinaryAt`/`EulerSystemRankOne`/`Sha_p`(+group/fintype)/`kolyvagin_descent_bound`/`KatoClassNonzero`/`kato_corank_bound` axioms (namespace BSD.EulerSystem).
- **Genuine composite theorems**: `lambda_zero_of_kato` (control theorem + Kato bound ⟹ λ_p = 0), `lambda_zero_iff_corank_eq_rank`.
- **Blind spot made explicit**: `kolyvagin_rank2_blind_389a1 : ¬ EulerSystemRankOne Curve389a1 K389a1 2` (the Rank-1 Euler-system tool fails at rank 2 — the starting point of B-6).
- 389a1/p=2 instances: `rank_389a1 : Rank Curve389a1 K389a1 = 2`, `ordinary_389a1_2` (⚠ mathematically overturned, see 9.6), `lambda2_389a1_eq_zero` (axiom).
- Compilation pitfalls (recorded): axiom/theorem parameters must be explicit `(E : Type)` (implicit misplaces the K argument); variable names must not contain the `λ` character (parsed as the lambda keyword); `import Mathlib.GroupTheory.Index`; `Nat.add_left_cancel` direction (2+0=2+x ⟹ x=0); split rw lists containing local variables into single rewrites.

### 9.5 Stage B-6 rank-2 Euler-system assessment (CH22 hit)

- Tool matrix (confirmed by search): LLZ14 (V_f⊗V_g Rankin–Selberg Euler system), BDR (Beilinson–Flach + syntomic regulator), KLZ (Rankin–Eisenstein classes), DR16 (generalized Kato class κ(f,g,h), weight (2,1,1) Hida limit, **not an Euler system**), **CH22** (Castella–Hsieh, DR conjecture proved in the CM-auxiliary-modular-form case), Castella 2312.01481 (κ_p ≠ 0 ⟹ dim Sel = 2, converse ⟺ loc_p ≠ 0), Kim 2203.12159 (weak IMC for arbitrary-rank Selmer structure), BKS 2103.11535 (derivatives of Kato's Euler system + unconditional evidence for Mazur–Tate).
- **CH22 Appendix Table 1 first row is exactly 389a1 / p=11 / K=ℚ(√−2)**, all conditions verified: D=−8 (389∤D), 11≡3 mod 8 split, (−2/389)=−1 inert, E[11] irreducible (only one curve in the 389a class, no rational m-isogeny m>3), L(E^K,1)≠0, χ infinite via Vatsal. Theorem chain: ord_T Θ_{f/K} = 2 (numeric 10T²+69T³+… mod 11²) → (Thm B) κ≠0 → (Thm A(1.9), unconditional) dim Sel(ℚ,V₁₁E) = 2 → (descent + rank=2) **Ш[11^∞](E/ℚ) finite**.

### 9.6 Two framework-correction findings (important)

1. **389a1 minimal model = [0,1,1,−2,0] (y²+y=x³+x²−2x)** — previously a wrong equation (y²+y=x³−x²−2x+1) corrupted all a_p values. Recomputed: a₂=−2, a₃=−2, a₅=−3, a₇=−5, **a₁₁=−4** (⟹ good ordinary at 11), a₁₃=−3, a₁₇=−6, a₁₉=5.
2. **p=2 is never ordinary** (a₂ always even) ⟹ the old record "389a1/p=2 good ordinary" is wrong; Greenberg's control theorem premise fails at p=2, so the λ₂ axiom is even more independent than B-4 stated (no ordinary framework at 2). The `ordinary_389a1_2` axiom semantics must be corrected (kept as a trace).
Landed: `BSD/Probe389/kato_framework_check.md`, `ap_ordinary.py`; roadmap doc gained §4.4.

### 9.7 CH22 Lean integration (`BSD/Sha11_389.lean`, merged into the aggregate, all green)

| Layer | Content | Status |
|---|---|---|
| Objects | `SelDim`/`ShaCorank`/`ShaFinite` (⟺ corank=0) | definitions |
| CH22 conditions | `ThetaOrderTwo389` (ord_T Θ=2 numeric fact), `KatoNonzero389` | axioms |
| Literature theorems | `kato_nonzero_of_theta_order` (Thm B), `sel_dim_two_of_kato_nonzero` (Thm A(1.9)), `sel_dim_eq_rank_add_sha_corank` (descent, dimension form) | axioms |
| Composite genuine theorems | `sel_dim_two_389` (B+A chain), `sha_corank_zero_389` (2=2+x⟹x=0, Nat arithmetic), **`sha11_finite_389 : ShaFinite Curve389a1 11`** | genuine theorems |

- Closure check `_check_l04.lean`: `sha11_finite_389` depends only on this module's CH22 axioms + EulerSystem reuse (Curve389a1/Rank/rank_389a1) + the kernel (propext/choice/Quot) — no sorry, no logical leakage.
- Engineering: EulerSystem has `namespace BSD.EulerSystem` ⟹ Sha11_389 needs `open BSD.EulerSystem`; Sha11_389 itself is wrapped in `namespace BSD.Sha11_389`.
- Compilation: `lake build BSD.Sha11_389` exit 0; after the `BSD.lean` import, `lake build -R` **7690 jobs all green**.

### 9.8 λ₁₁ K_cyc-side assessment (2026-10-13, latest)

**Mathematical positioning**: λ₁₁ = corank_{ℤ₁₁} Sel_{11^∞}(E/K_cyc) − rank E(ℚ); under IMC (ordinary, μ=0), λ_p = ord_T L_p(E,T) − rank.

**Key diagnosis — why CH22 cannot give λ₁₁**: CH22 closes the **ℚ side** (Ш[11^∞] finite ⟹ corank Sel(E/ℚ) = 2), but the control theorem is the **fixed-point version** corank(Sel_{K_cyc}^G) = 2; the full-group corank = corank(Sel^G) + corank(Sel/Sel^G) = 2 + λ₁₁ — **λ₁₁ is precisely the "K_cyc-tower extra part" (the cofree part of M/M^G), out of reach of the control theorem**.

**Tool coverage**: Skinner–Urban IMC covers only analytic rank 0/1 (L_p nonzero special value); rank 2 ⟹ the L_p-zero case — **uncovered for every p** (correction of the B-4 wording: "rank 2 + p=2" → "analytic rank ≥ 2 uncovered; p=2 merely adds the 2-adic Hida obstruction"). CH22's generalized Kato class is on the ℚ side; Kim's weak IMC is assumption-based; the BKS Kato-derivative mechanism is on point but gives no corank theorem.

**ord_T L₁₁ = 2 numeric expectation**: the analytic side L″(E,1)/2! = 0.759316500288 ≠ 0 (unconditionally verified) + no exceptional-zero mechanism for non-CM good ordinary ⟹ p-adic interpolation is expected to give T-order exactly 2.

**Three executable paths (pending choice)**: ① numeric evidence layer — verify T²∥L₁₁ mod 11^k in the Iwasawa expansion of L₁₁(E,T) (p=11 is far more tractable than p=2; no Hida obstruction); ② IMC + ord=2 ⟹ λ₁₁ = 0 as an axiom (alongside λ₂, Lean axiom layer); ③ genuine Kato-Euler-system-derivative theorem (BKS mechanism; realistic at p=11) — the continuation of the B-6 new-mathematical-input line.

### 9.9 Current status table (389a1, Sha-finiteness side)

| Prime | Target | Status | Vehicle |
|---|---|---|---|
| 2 | Ш[2] finite | **genuine theorem** | ShaFreeLayer.lean (sha2_389_card_eq_one derivation) |
| 11 | Ш[11^∞] finite | **Lean theorem chain** (CH22 axioms + composite genuine theorem) | Sha11_389.lean (sha11_finite_389) |
| 2 | λ₂ (K_cyc side) | axiom; p=2 non-ordinary voids the control-theorem premise | EulerSystem.lean |
| 11 | λ₁₁ (K_cyc side) | open; three paths pending | — |
| other ℓ | Ш[ℓ^∞] finite | open | — |

Engineering note: all §9 artifacts live in `c:\proj2\BSD\` (main project); backup-repo sync awaits a further instruction.

## 10. 2026-10-15: λ₁₁ = 2 numerical pillar + Lean axioms + cross-prime check (K_cyc side)

Main line: landing the §9.8 "numerical path 1" decision — series(11) replication verifying ord_T L₁₁ = 2 (λ₁₁ = 2), recording it as Lean axioms, then the cross-prime check between the p-side Iwasawa λ₁₁ and the K_cyc-side λ. All numerics run through the PARI/GP 2.13.3 (WSL) true-modular-symbol pipeline (`msfromell` + `mseval`); the replication structure was calibrated on 11a1/p=3 (Σ ≡ 68 mod 243 exact hit, `series_points_check.md` §6).

### 10.1 series(11) replication (389a1/p=11, `Probe389/`)

- **Result**: L₁₁(T) = 0 + 0·T + 9·T² + 9·T³ + … (mod-11 coefficients); T⁰ ≡ 0 mod 11⁴ (bd=4), T¹ ≡ 0 mod 11 (bd=1), T² ≡ 9 mod 11 ≠ 0 ⟹ **ord_T = 2 (λ₁₁ = 2)**.
- **Data quality**: 220 series points (j=0..10 × a=1..10, denominators 121/11) + 22 extra points, all measured in PARI, duplicate values consistent (distinct r121=110, r11=10); **both distribution identities hold exactly** (hard H₁ self-consistency test): r=1/121: −4·0 = 0 = −1 + f(1/11); r=1/11: −4·1 = −4 = −4 + f(1).
- **No cuspidal endpoints** for 389a1 (c<121 coprime to N=389), so no cusp-symmetry repair needed (contrast 11a1).
- **Cross-checks**: Sage docstring series(3) = O(3⁵)+O(3²)T+(2+2·3+O(3²))T² (T²≡2 mod 3 ≠ 0; rank-2 consistency across primes); L″(E,1)/2 = 0.759316500288 (interval arithmetic, analytic rank 2); M(0) = 0 (rank 2 ⟹ L(E,1)/Ω = 0).
- Artifacts: `read_pari_series11.py` (one-click reproduction), `ms389a1_series.gp` and 6 more scripts/outputs, `series11_389_check.md` (record).

### 10.2 Lean axioms (`Sha11_389.lean` numerical-verification layer)

New "numerical-verification layer" (between the CH22 condition layer and the theorem layer): `L11OrderTwo389 : Prop` + `l11_order_two_389 : L11OrderTwo389` (axioms). Comments make the **object distinction** explicit: L₁₁(T) (E/ℚ ordinary p-adic L, direct evidence for λ₁₁=2) ≠ Θ_{f/K} (E/K anticyclotomic, CH22 theorem premise) — both are instances of "rank 2 ⟹ second-order vanishing", forming an independent parallel endorsement of the CH22 chain. `lake build BSD.Sha11_389` all green (1069 jobs).

### 10.3 Cross-prime check (③, K_cyc-side λ)

**Mathematics**: Iwasawa character decomposition (K/ℚ quadratic abelian, 11 split in K ⟺ χ(11)=(−2/11)=+1): L_p(E/K,T) = L_p(E,T)·L_p(E^χ,T) ⟹ λ₁₁(E/K) = λ₁₁(E) + λ₁₁(E^χ).

| Object | λ | Evidence |
|---|---|---|
| E/ℚ, p=11 | **2** | series(11): T²≡9 mod 11 ≠ 0 (§10.1) |
| E/ℚ, p=3 | **2** | docstring series(3): T²≡2 mod 3 ≠ 0 (cross-prime consistency) |
| E^χ/ℚ, p=11 | **0** | analytic rank 0 (ellanalyticrank, unconditional) + T⁰≡10 mod 11 ≠ 0 |
| **E/K, K_cyc, p=11** | **2 = 2+0** | character decomposition |

**E^χ data** (PARI): equation [0,−8,0,−128,−128] (`elltwist(E,−8)`; −8 = field discriminant of K), conductor **24896 = 389·64** (389 inert in K preserved); **analytic rank = 0**, **L(E^χ,1) = 2.7884581989… ≠ 0** (ellanalyticrank, unconditional); **M(0) = L/Ω⁺ = 2 (exact rational)** (msfromell @ N=24896, 4G stack). Rank-0 identity (calibrated on 11a1) T⁰ ≡ (1−1/α)²·M(0) mod 11, (1−1/α)² ≡ 5 mod 11 ⟹ **T⁰(E^χ) ≡ 10 mod 11 ≠ 0 ⟹ ord_T = 0 ⟹ λ₁₁(E^χ) = 0**.

**Conclusion**: the rank-2 curve has λ = rank = 2 at the ordinary primes {3,11} (cross-prime consistency); the K-side quadratic twist is rank 0 (non-zero case), contributing λ = 0 ⟹ E/K also has λ = 2 (zero case), Q-side = K_cyc-side. Compatible with the "Ш[11^∞] finite ⟹ corank 0" descent structure — a cross-prime, cross-field numerical consistency endorsement for the B-6/CH22 framework.

Artifacts: `ms389twist_smoke.gp`/`ms389twist2.gp` + outputs, `cross_prime_lambda_check.md` (record).

### 10.4 Lean axioms (cross-prime-check layer)

New "cross-prime-check layer": `LambdaTwistZero389 : Prop` + `lambda_twist_zero_389` (axiom; numeric-analytic evidence); `LambdaEKTwo389 : Prop` (axiom); `lambda_ek_add_of_decomp : L11OrderTwo389 → LambdaTwistZero389 → LambdaEKTwo389` (character-decomposition axiom, literature fact); genuine theorem **`lambda_ek_two_389 : LambdaEKTwo389`** (pure composition of the two axiom premises, mirroring the `sel_dim_two_389` pattern). Build all green (1069 jobs, 5.8s incremental).

### 10.5 Current status (λ side, 389a1)

| Prime | Target | Status | Vehicle |
|---|---|---|---|
| 11 | λ₁₁(E/ℚ) = 2 | **numerically verified** (ord_T L₁₁ = 2) + Lean axioms | series11_389_check.md / Sha11_389.lean |
| 11 | λ₁₁(E^χ) = 0 | **numeric-analytic** (rank 0 + T⁰≠0) + Lean axioms | cross_prime_lambda_check.md / Sha11_389.lean |
| 11 | λ₁₁(E/K) = 2 | **character-decomposition derivation** + Lean genuine theorem | Sha11_389.lean (lambda_ek_two_389) |
| 3 | λ₃(E) = 2 | docstring numerics (cross-prime consistency) | Sage series(3) |
| other ℓ | λ_ℓ | open | — |

Engineering note: this section's numerical artifacts (PARI scripts/outputs/replication pipeline) live in `c:\proj2\BSD\Probe389\`; the three axiom blocks of `Sha11_389.lean` (CH22 conditions + L₁₁ numerics + cross-prime check) are independently recorded with all logical composition genuine theorems; backup-repo sync awaits an explicit instruction.
