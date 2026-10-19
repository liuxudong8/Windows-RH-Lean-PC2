# BSD Library — Lean Formalization of Weak BSD Rank 1 / Rank-2 Symmetry + n=3 Skeleton (Status Summary)

> Updated: 2026-10-19 (spectral-duality line added: ζ_K zero-union structure — cross-family pairing explicit formula, character-oscillation cancellation, and the boundary of the Hilbert-space method) — **The spectral-duality series (K=ℚ(√5), ζ_K=ζ·L(χ₅), sharing the same χ₅ structure with the E⁵ twist: a_p = χ₅(p)a_p(E)) closed at assaults XVIII/XIX, producing three objects defensible independently of the truth of RH/GRH/QRH.** **① Q(0) verdict (decisive negative result)**: Q(0)=∫η⁴=∫f² (f=η² a probability density with supp⊂[−1/2,1/2], ∫f=1); Cauchy–Schwarz gives **Q(0)≥1 (equality iff uniform)**, and Lamzouri's Proposition 2.1 (arXiv:2609.02882) applied to the union Z_K has lower bound **2−C_MT(f)−Q(0)(f)≤0 identically** (extremal f₀ gives −0.3338, uniform −0.3333) — the Hilbert-space inequality **fails outright for unions of product L-functions** (cross-family pairs contribute Q(0)≥1 to ΣK² with no corresponding independent count in Σ1). **② Prime-term net suppression quantified (Assault XIX)**: Σ_p χ₅(p)/√p (σ=1/2, critical) has **bounded partial sums sup≤2.457** (X≤5×10⁶) — character sums cancel, no long-period drift; the union prime-term sup envelope (Σ(1+χ₅)/(√p log p)) is below the single-family one at every scale (segment ratios 0.57/0.71/0.82/0.90/0.94); but **in mean-square the union is 1.263× the single family** (Σ(1+χ)²/p = 3.457 vs Σ1/p = 2.736 at X=2×10⁶; (1+χ)² = 4·1_{χ=+1}) — the net suppression holds only at the sup level, not at the power level (echoing the Assault-XVI white-noise verdict). **③ On-line proportion remainder magnitude**: density side sup|S_K|/(π·(T/2π)λ) ≈ 8.1×10⁻⁶, pairing side ∫dF ≈ −0.0094 ≈ 0 ⟹ **0.6725−O(10⁻⁵~10⁻³)** — the gap is in the Levinson constant, not the remainder; 7/8 = 0.875 belongs to the QRH-class mechanism (quasi-random premise), not a constant push of the same argument. **④ L(χ₅) main-term correction**: N_L(T) = (T/2π)[log(T/2π)+log 5−1]+O(log qT) (Γ(s/2) phase; log q is a linear term; historical scripts using the ζ convention or missing log q produced ~10⁵ spurious main terms, now fixed; ζ-side D(t)≈0 verified perfectly; L data carry a 0.27% R-S root-finding artifact, disclosed). **Strategic positioning**: externally defensible assets = the cross-family pairing explicit formula (Theorem 3.1′: ζ–L(χ₅) cross-family pair correlation has main term f(0), primes killed by character oscillation O(x^{−1/2}) — a new tool for pair-correlation theory of products of L-functions) + the character-oscillation cancellation structure + the Q(0) negative result (method boundary / dead-end map in the AI era); the spectral-duality chain (Arthur trace formula ↔ Weil explicit formula, the agreed reparametrization (ℓ₁,ℓ₂)↦(T,W)) remains a belief, not closed — honestly labelled. Numerical system (zeros_T6e5.npz: ζ 999,492 + L 1,150,050 zeros; route2m.json cross-family pairing; Fourier profiles) and the Assault XVI–XIX documents live in the d1 directory. See §15.

> Updated: 2026-10-16 (rank push closed: the `rank_389a1` black-box axiom split into a genuine proof) — **`RankTwo389.lean` landed**: the algebraic rank-2 claim is split into "genuine upper bound + recorded lower bound" — `rank_le_two_389` (genuine: `sel2_rank_bound` (2-descent order bound axiom: 0→E/2E→Sel₂→Ш[2]→0 + E(ℚ) torsion-free ⟹ 2^rank ≤ #Sel₂) + `sel2_order_four_389` (|Sel₂|=4, G4 anchor) ⟹ 2^rank ≤ 4 ⟹ rank ≤ 2) + `rank_ge_two_389` (recorded: two independent infinite-order points P₁=(−1:1:1), P₂=(0:−1:1), height-pairing det = 0.15246017794314375162…≠0 (G3) ⟹ rank ≥ 2 via Mordell–Weil) + `rank_two_389 := le_antisymm` (genuine assembly). **Closure check (#print axioms)**: `rank_two_389` depends on [sel2_rank_bound, sel2_order_four_389, PointsIndependent389, points_independent_389, rank_ge_two_of_points] + infrastructure — **without `rank_389a1`**: algebraic rank 2 is downgraded to "|Sel₂| data anchor + descent structure axiom + two-point single recording". **Build-chain closure**: the lake clean incident (mathlib `.trace` wiped ⟹ near-full recompilation + parallel `.private` read races / module crashes / missing dependencies in batches) was fixed by 3 rounds of serial `lake build Mathlib.XXX` patches; **Lake 5.0 `-R` = `--reconfigure`, building only the default targets (exe chain) — the BSD library requires an explicit `lake build BSD`**; RankTwo389 entered the default build via `BSD/Main.lean` adding `import BSD.RankTwo389` (lean_lib default roots = ["Main"]; globs/roots TOML syntax is unusable under Lake 5.0, config kept default); `lake build -R` all green 7690 jobs, `lake build BSD` all green 3476 jobs (BSD 14 oleans). See §14.
> Updated: 2026-10-16 (G3/G4 engineering closure + recorded into the Lean genuine-proof layer) — **G3 (Reg full precision) closed**: Sage regulator(precision=200) = 0.15246017794314375162432475704945582324372707748663..., height-pairing det 0.152460177943144 (gens [(−1:1:1),(0:−1:1)]); four sources (Python NT / Sage / Magma / LMFDB 389.a1) agree to ~10⁻¹⁹; the G2a discriminant margin grows ~6 orders (Reg error 5×10⁻⁶ → ~10⁻¹⁹, #Ш_pred ≈ 1±10⁻¹²). **G4 (pure-Python independent recomputation of |Sel₂|) closed**: A = ℚ[x]/(x³+x²−2x+1/4) (totally real cubic), unit search ε₁=(−1,8,−4), ε₂=(−1,8,4); class number h=1 (Minkowski bound 8.76 + P₂/P₃ principal via N=±2/±3 elements); |A*/A*²| = 8, N∈ℚ*² sieve ⟹ **|H¹(ℚ,E[2])| = 4** (δ = 1, (1,−8,4), (1,−8,−4), (−3,20,16)) ⟹ |Sel₂| ≤ 4 ∧ rank=2 torsion-free ⟹ |Sel₂| ≥ 4 ⟹ **|Sel₂| = 4** (pure stdlib, no numpy). **Recorded into `Sha11_389.lean`**: `sel2_order_four_389` (axiom) + **genuine theorem `sha2_order_one_389` (#Ш[2] = 1 = 4/2², descent order relation; data anchor closed)** + `RegHighPrecision389`/`reg_high_precision_389` (axiom); G2-layer comments updated to the 200-bit Reg convention. `lake build -R` all green, 7690 jobs. See §13.
> Updated: 2026-10-15 (Gap A numerical verification closed — CH22 Theorem A hypothesis layer completed) — **L(E/K, χ², 1) ≠ 0 verified numerically**: constructed the quadratic ring-class character χ² = (N(𝔞)/5) of Cl_5 (conductor 5), θ(χ²) of level 200, and the Rankin-Selberg convolution a_n = Σ_{d|n} a_E(d)·b_{n/d} (Sage, 50000 coefficients); in PARI the low-level lfuncreate format `[an, 1, [0,1/2,1,3/2], 3, 77800, 1]` (Vga of Γ(s)Γ(s+1/2) type, k=3, N = 389·200, eps = +1) — **a three-parameter scan verdict** (5 conductor candidates / eps ±1 / 3 Vga candidates, unique lfuncheckfeq winner): **L(1) = 4.9098500369129333522552480141603036183… ≠ 0**, 5000/50000 coefficients agreeing to 10⁻²⁷. Written back to `Sha11_389.lean`: the `LEKChi2Nonzero389` / `l_ek_chi2_nonzero_389` comments changed from "numerical verification pending" to "verified closed" (axiom kept: numerical support does not replace a proof); build all green (1069 jobs). **All five Theorem-A hypotheses now have numerical anchors** (① L(E^χ,1) ≠ 0 = 2.788 recorded; ② χ² non-vanishing = 4.90985 newly closed; ③ ρ̄ irreducible via the single-curve argument in the 389a class; ④ N⁻ squarefree since 389 is prime; ⑤ ramification at q|N⁻ via the multiplicative reduction at 389). See §12.
> Updated: 2026-10-15 (Θ_{f/K} anticyclotomic replication closed) — the "hardest" line, **Θ_{f/K} Sage Brandt-module replication** (a true replication of the CH22 Theorem-B premise ord_T=2), reached a phase closure: ① **root-cause bug fixed** (v4–v10 summed the class index as if it were the f value — f never entered Θ); ② **ord_T=2 verdict closed**: 389a1 (T²≡78) and 709a1 (T²≡94) both satisfy T⁰=T¹=0, T²≢0 mod 121 ⟹ ord_T=2, independently for both curves, consistent with the CH22 targets (T⁰=T¹=0 is a structural property, stable under p-adic normalization of f_E); ③ **coefficient-wise target matching located as unreachable** (the "p-adically normalized" detail of f_E + the optimal embedding choice are not given in the paper); ④ the ord_T=2 verdict is **recorded into the `Sha11_389.lean` evidence block** (axiom layer unchanged; evidence comments updated + new evidence block), build all green. See §11.
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

## 11. Θ_{f/K} anticyclotomic replication (Sage Brandt module, closed 2026-10-15)

### 11.1 Goal and pipeline

The "hardest" line: **a true replication of the CH22 (Castella–Hsieh 2022, arXiv:1809.09066) Theorem-B premise ord_T Θ_{f/K} = 2** — replicate from the definition the theta element of Table 1 first row 389a1/11/K=ℚ(√−2), without using the target values. Pipeline: SageMath 9.5 (WSL Ubuntu-22.04, built-in Brandt module) `BrandtModule(389,1)` (33-dimensional) + custom P_n^a construction + class matching + formula assembly.

- Formula (CH22 §3, verified word-for-word against example.tex / ar5iv §6 / BD96 §2.7):
  Θ_{E/K,2}(T) := (1/α₁₁³)·Σ_{i=0}^{120}Σ_{a∈μ₁₀}(α₁₁·f_E(P₂^{a·uⁱ}) − f_E(P₃^{a·uⁱ}))·(1+T)ⁱ mod (11², T¹¹); u=1+11.
- f_E: Cl(R)→ℤ (JL image, T₁₁·f = −4f verified exactly); P_n^a lattice condition pⁿ·[[1,−a·p⁻ⁿ],[0,1]]·M_x ≡ 0 mod p^{2n} (integralization + LLL + fractional lattice basis).
- Component-level all-passed: **full audit of 121 P₃ class matchings** (theta(10)=theta(30), zero discrepancy, zero missed), **ip ring isomorphism 16/16** (mod 11⁶), ip(√−2)=diag(u,−u), P₀=trivial, P₂ classes 9/21/13/1/4.

### 11.2 Root-cause bug fix (explains all historical systematic mismatches)

v4–v10 summed the **class index** (0..32) returned by `class_f()` as if it were the **f value** (∈{−2..2}) — **the f eigenvector never entered Θ**. After the v12 fix, f values enter correctly.

### 11.3 ord_T = 2 verdict closed (core result)

| Curve | Θ (teich, f values, mod 121) | T⁰ | T¹ | T² | ord_T |
|---|---|---|---|---|---|
| 389a1 | [0,0,**78**,46,71,81,59,99,113,85,49] | 0 | 0 | 78≠0 | **2 ✓** |
| 709a1 | [0,0,**94**,97,17,40,56,104,41,35,67] | 0 | 0 | 94≠0 | **2 ✓** |

- **T⁰=T¹=0 is a structural property of the summation**, invariant under p-adic normalization (ℤ₁₁^× scaling) of f_E; T²≠0 is preserved under scaling and sufficient precision ⟹ **the ord_T=2 verdict does not depend on the normalization convention the paper does not give**.
- Independently established for both curves, consistent with the CH22 targets (ord_T=2) — the numerical premise of the CH22 chain has reached its structural goal.

### 11.4 Coefficient-wise target matching: unreachable (honest localization)

- T²+ coefficients deviate systematically (389 target [0,0,10,69,1,103,106,66,11,55,110]; 709 target [0,0,27,114,3,14,36,15,42,44,91]); term-by-term ratios are not proportional ⟹ **not an f-scaling issue**.
- All recoverable degrees of freedom exhausted: u sign, teich direction (mathematically forced), integer representatives, α unit root (29 unique; 93 not a root, 88 not a unit), class shift (Sage right-ideal multiplication collapses to a degenerate table; mechanism unimplementable), Brandt identity (unknown theta normalization).
- Remaining difference pinned down: the author implementation's **f_E "p-adically normalized" normalization detail** and **the i_p optimal-embedding choice** — not given in the paper, not recoverable from it. Pending the authors' implementation (contact Castella/Hsieh or GitHub).
- **The gap does not affect the ord_T=2 verdict** (structural property, stable under normalization).

### 11.5 Lean recording (`Sha11_389.lean` evidence layer update)

- `theta_order_two_389` comment updated: independent Sage verdict + 709 cross-reproduction + gap noted (axiom layer unchanged).
- New evidence block "Θ_{f/K} ord_T=2: Sage Brandt-module replication" (formula, numbers, robustness argument, component verification, honest gap).
- Build: `lake build BSD.Sha11_389` all green (1069 jobs, 9.9s).

### 11.6 Current status (Θ side, 389a1)

| Target | Status | Vehicle |
|---|---|---|
| ord_T Θ_{f/K} = 2 (CH22 Thm-B premise) | **numerical verdict closed** (389+709 independent, robust structural property) + Lean evidence block | theta_replica_final.md / Sha11_389.lean |
| coefficient-wise target matching (Table 1 values) | **unreachable** (f_E normalization / embedding detail not in paper) — downgraded to "pending author implementation" | theta_replica_final.md |
| remaining CH22-chain numerical premises | closed (series(11), mspadicL all-prime, cross-prime check) | §9/§10 |

Artifacts (`Probe389/`): `_sage_theta_v12_fvalue.sage` (**current authoritative replication script**, correct f values), `_sage_audit_p3_full.sage`/`_sage_check_iso.sage` (component verification), `theta_replica_final.md` (final conclusions), `theta_replica_v12v14_diagnosis.md` (intermediate diagnosis), `ch22_src/` (CH22 source + ar5iv full text + BD96 full text). Dead ends (do not retry): PARI mseval, Sage Cell online, conjugate(), cyclic_right_subideals, the `O.ideal()` bug, `inverse_mod` on Integer, class shift (collapsed multiplication table), flip/teich_inv, Brandt identity.

## 12. Gap A numerical verification closed: L(E/K, χ², 1) ≠ 0 (2026-10-15)

### 12.1 Position

CH22 Theorem-A hypothesis item ② `L(E/K, χ², 1) ≠ 0` — previously only an axiom (`LEKChi2Nonzero389` marked "numerical verification pending"); this section completes the numerical verification.

### 12.2 Construction

- K = ℚ(√−2) (class number 1); χ² = (N(𝔞)/5): the quadratic ring-class character of Cl_5 (conductor 5; satisfies (pN_f, cD_K) = 1 — CH22's χ is guaranteed to exist by Vat03/CH18 Thm D without a specified form; this is an explicit computable realization).
- θ(χ²)(q) = Σ_m (m/5)·r(m)·q^m, r(m) = #{a²+2b²=m} (counting in ℤ[√−2]), level = |D_K|·f² = 8·25 = 200.
- L(E/K, χ², s) = L(E ⊗ θ(χ²), s) (Rankin-Selberg, weight 3): a_n = Σ_{d|n} a_E(d)·b_{n/d}.
- Sage convolution, 50000 coefficients (a_1..5 = [2,−6,−8,10,−6]); PARI low-level lfuncreate format.

### 12.3 Three-parameter scan verdict (unique lfuncheckfeq winner)

| Parameter | Candidates | Winner |
|---|---|---|
| Vga (gamma-factor type) | [0,1,0,1] (Γ(s)²) / **[0,1/2,1,3/2]** (Γ(s)Γ(s+1/2)) / [0,0,1,1] | **[0,1/2,1,3/2]** (checkfeq −5 vs 0/−1) |
| conductor | {77800, 311200, 700200, 1945000, 38900} | **77800 = 389·200** (−5 vs ≤−2) |
| eps | ±1 | **+1** |

### 12.4 Numerical conclusion

**L(E/K, χ², 1) = L(E⊗θ(χ²), 1) = 4.9098500369129333522552480141603036183… ≠ 0**

- Convergence: L(1) from 5000 and 50000 coefficients agrees to 10⁻²⁷.
- Functional equation: checkfeq = −5 (log10 error; 0/−1 when the structure is wrong).
- ε(E⊗θ) = +1 implies ε(θ(χ²)) = −1 (ε(E) = +1, χ_g(389) = −1; consistent with the dihedral root-number formula; optional further check).

### 12.5 Lean write-back

`Sha11_389.lean`: comments of `LEKChi2Nonzero389` / `l_ek_chi2_nonzero_389` updated to "numerical verification closed" (construction, parameters, numbers, scan verdict, convergence all recorded); **axiom kept** (numerical support does not replace a proof). Build all green (1069 jobs, 9.1s).

### 12.6 Status: all five Theorem-A hypotheses have numerical anchors

| Theorem-A hypothesis | Anchor | Status |
|---|---|---|
| ① L(E^χ, 1) ≠ 0 | E^χ = elltwist(−8), L = 2.7884581989 (ellanalyticrank, unconditional) | recorded (§10.3) |
| ② L(E/K, χ², 1) ≠ 0 | **Rankin-Selberg: 4.9098500369… (this section)** | **newly closed** |
| ③ ρ̄_{E,11} irreducible | 389a class has a single curve (no-11-isogeny argument) | axiom |
| ④ N⁻ squarefree | (−2/389) = −1 ⟹ N⁻ = 389 prime | axiom |
| ⑤ ρ̄ ramified at q|N⁻ | multiplicative reduction at 389 | axiom |

Artifacts (`Probe389/`): `_sage_lekchi2_coeffs.sage` (Sage convolution), `l_ek_chi2_coeffs.txt` (50000 coefficients), `write_an_gp.py` / `l_ek_chi2_an.gp` (PARI coefficient file), `lfun_ekchi2.gp` (construction + scan + final verification), `lfun_ekchi2_out.txt`, **`l_ek_chi2_verification.md` (conclusions recorded)**.

## 13. 2026-10-16: G3/G4 engineering closure + recording into the Lean genuine-proof layer (both rank2_status gaps closed)

The G-series cleanup concluded per the user's instruction "G3/G4 engineering completion": G3 (Reg full precision) and G4 (pure-Python independent recomputation of |Sel₂|) — both open gaps closed and recorded into `Sha11_389.lean`.

### 13.1 G3: Reg full precision (`Probe389/G3_Reg/`)

SageMath 9.5 (WSL) height-pairing final comparison:
- `E.regulator() = 0.152460177943144`; `regulator(precision=200) = 0.15246017794314375162432475704945582324372707748663081784028...`
- Height-pairing matrix [[0.686667083305587, 0.268478098806726], [0.268478098806726, 0.327000773651605]], det = 0.152460177943144
- **Four-source agreement** (Python NT height ∥ Sage ∥ Magma ∥ LMFDB 389.a1) to ~10⁻¹⁹ (previously 5×10⁻⁶)
- For the G2a verdict (#Ш[11]=1): Reg error no longer dominant, #Ш_pred ≈ 1±10⁻¹²; the margin excluding #Ш=11 grows ~6 orders (~10¹⁰)
- Boundary: Reg remains numerical (not proof-level), independently consistent across four sources.

### 13.2 G4: pure-Python independent recomputation |Sel₂| = 4 (`Probe389/G4_Sel2/`)

**Mathematical chain** (Silverman/Cassels class space + descent exact sequence):
```
E: y²+y = x³+x²−2x ⟹ y'² = f(x) = x³+x²−2x+1/4 (translation), A = ℚ[x]/(f) (Δ = 389/16 > 0, totally real cubic)
H¹(ℚ, E[2]) ≅ { δ ∈ A*/A*² : N(δ) ∈ ℚ*² }
0 → E(ℚ)/2E(ℚ) → Sel₂ → Ш[2] → 0  +  rank=2 torsion-free ⟹ |Sel₂| ≥ 4
⟹ |H¹| = 4 ⟹ |Sel₂| = 4
```

**Pure Python (stdlib + fractions; no numpy/sympy; compatible with the user's older Python)**:
- Unit search (B=25): 20 units; fundamental units ε₁=(−1,8,−4), ε₂=(−1,8,4) (N=−1; −εᵢ have N=+1)
- **Class number h(A) = 1** (g4_classno.py: Minkowski bound 8.76 ⟹ class group generated by norm ≤ 8 prime ideals; P₂=(2,t), P₃=(3,t−1) principal via N(δ)=±2 ((−12,6,8)), ±3 ((−13,10,8)) ⟹ Cl[2]=0, |A*/A*²| = 2³ exact)
- **|H¹| = 4**: δ = 1, (1,−8,4), (1,−8,−4), (−3,20,16) (all N=1; −1, ε₁, ε₂, −ε₁ε₂ have N=−1, excluded)
- ⟹ |Sel₂| ≤ 4 ∧ ≥ 4 ⟹ **|Sel₂| = 4**; and |Sel₂| = |H¹| automatically ⟹ #Ш[2] = 1 (consistent with Magma `Sha(E)[2] trivial`)

**Three-source comparison**: Magma (MordellWeilShaInformation + Effort=2) 4 ∥ Sage/PARI 4 ∥ **G4 pure Python 4**.

Boundary (honest): |Sel₂| ≥ 4 relies on rank=2 and torsion-freeness (established earlier in this project); G4 is an independent recomputation of the **value**, not an independent proof of the rank.

### 13.3 Lean recording (`Sha11_389.lean` appended G4/G3 blocks)

| Name | Layer | Content |
|---|---|---|
| `sel2_order_four_389 : SelPOrder Curve389a1 2 = 4` | axiom (data anchor) | |Sel₂|=4 (G4 pure-Python recomputation) |
| **`sha2_order_one_389 : ShaPOrder Curve389a1 2 = 1`** | **genuine composite theorem** | #Ш[2] = #Sel₂/2^rank = 4/4 = 1 (descent order relation + rank=2; data anchor closed — same pattern as `sha11_order_one_of_sel11` but **not dangling**) |
| `RegHighPrecision389 : Prop` / `reg_high_precision_389` | axiom | Reg = 0.15246017794314375162... (200-bit anchor) |

- G2-layer comments updated: Reg convention 5×10⁻⁶ → 200-bit; discriminant margin ~10¹⁰.
- `#Ш[2] = 1` is now an **independent Lean genuine-proof chain** (independent of BSD numerics), cross-checked against Magma's `Sha(E)[2] trivial` — dual vehicles: ShaFreeLayer's `sha2_389_card_eq_one` and Sha11_389's `sha2_order_one_389`.
- Build: `lake build -R` all green (7690 jobs).

### 13.4 Status: rank2_status.md G-series

| Gap | Status |
|---|---|
| G1 overall finiteness (rank-2 open problem) | open (GRH gives only "if finite then a bound") |
| G2 #Ш[11] order | conditional verdict (refined-BSD numerics) + genuine-proof skeleton (#Sel₁₁=11² dangling) |
| **G3 Reg full precision** | **closed** (200-bit, four-source agreement) |
| **G4 \|Sel₂\| pure Python** | **closed** (\|H¹\|=4 ⟹ \|Sel₂\|=4; class number h=1 verified) |
| G5 GRH upper-bound constant | closed (conditional) |
| G6 GRH contradiction-chain assembly | verdict passes (conditional on GRH+BSD) |

Artifacts: `Probe389/G3_Reg/g3_result.md` (+ g3_sage.sage), `Probe389/G4_Sel2/g4_result.md` (+ g4_sel2.py / g4_classno.py); `rank2_status.md` G3/G4 rows updated to "closed".

## 14. 2026-10-16: Rank push — the `rank_389a1` black-box axiom split into a genuine proof (RankTwo389.lean)

Continuation of the main line: after the Ш-finiteness work (G3/G4 closed), the user proposed "rank can be pushed one step further" and confirmed "do it" — split `BSD.EulerSystem.rank_389a1 : Rank Curve389a1 K389a1 = 2` (single black-box axiom) into "**genuine upper bound + recorded lower bound**", then assemble with `le_antisymm`, downgrading "algebraic rank = 2" to "data anchor + single-point recording".

### 14.1 Module structure (`BSD/RankTwo389.lean`, new)

| Layer | Name | Content |
|---|---|---|
| Structural axiom | `sel2_rank_bound (E K) : 2 ^ Rank E K ≤ SelPOrder E 2` | 2-descent order bound: 0→E(ℚ)/2E(ℚ)→Sel₂→Ш[2]→0, \|E/2E\| = 2^{rank+dim E[2]}, E(ℚ) torsion-free ⟹ 2^rank \| #Sel₂ (theorem-level recording) |
| Data anchor | `PointsIndependent389 : Prop` / `points_independent_389` | P₁=(−1:1:1), P₂=(0:−1:1) independent (height-pairing det = 0.15246017794314375162…≠0, G3 Sage regulator(200) measured gens) ∧ infinite order (torsion trivial standard fact) |
| Recorded fact | `rank_ge_two_of_points : PointsIndependent389 → 2 ≤ Rank ...` | Mordell–Weil: rank of a free abelian group ≥ number of independent elements (theorem-level recording) |
| Genuine | `rank_ge_two_389` / `rank_le_two_389` / **`rank_two_389 := le_antisymm`** | lower bound = anchor+recording composition; upper bound = `sel2_rank_bound` + `sel2_order_four_389` (|Sel₂|=4) ⟹ 2^rank≤2² ⟹ rank≤2 (`Nat.pow_le_pow_iff_right`); assembly = le_antisymm |

**pow lemma pitfall (recorded)**: `pow_le_pow_right₀` does not exist over ℕ (requires LinearOrderedSemiring); correct usage `(Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp` (probe `_probe_pow.lean` confirmed the signature `{a n m} (h : 1 < a) : a^n ≤ a^m ↔ n ≤ m`, import Mathlib.Data.Nat.Basic).

### 14.2 Closure check (core evidence, #print axioms)

| Theorem | axioms | Layer |
|---|---|---|
| `rank_le_two_389` | [propext, Classical.choice, Quot.sound, Curve389a1, K389a1, Rank, `sel2_rank_bound`, `SelPOrder`, `sel2_order_four_389`] | **genuine upper bound** (descent structure axiom + |Sel₂| data anchor) |
| `rank_ge_two_389` | [Curve389a1, K389a1, Rank, `PointsIndependent389`, `points_independent_389`, `rank_ge_two_of_points`] | **recorded lower bound** (two-point single recording) |
| `rank_two_389` | union of the two | **without `rank_389a1`** — black-box downgrade complete |

**Cycle trap (do not reverse)**: the order must be |Sel₂|=4 ⟹ rank≤2 ∧ independent points ⟹ rank≥2 ⟹ rank=2 ⟹ #Ш[2]=1 (`sha2_order_one_389` = 4/2²); never derive rank from #Ш[2]=1.

### 14.3 Build-chain closure (the lake clean incident and its fix, recorded)

1. **lake clean chain reaction**: wiping mathlib `.trace` triggered a near-full recompilation (most of the 7690 jobs are mathlib); parallel builds failed in batches — `failed to read ...olean.private` (toolchain files intact — **parallel race** confirmed), `Code 3221225727` crashes, missing-dependency timing (`Notation3.olean does not exist`). Fix = **serial `lake build Mathlib.XXX` patches of the failing modules**, 3 rounds to closure.
2. **Lake 5.0 semantics clarified**: `lake build -R`'s `-R` = `--reconfigure` (re-elaborate the config), **building only the default targets (exe chain: Main→OrderPreservingBijection), excluding the BSD library** — the BSD library needs an explicit `lake build BSD` (the historical "BSD library incremental replay" was a reconfigure replay log, not a rebuild).
3. **RankTwo389 into the default build**: under Lake 5.0 a lean_lib defaults to roots = ["Main"] (only the `BSD.Main` closure is built); the `globs`/`roots` TOML syntax is unusable under Lake 5.0 (`expected glob`; `roots=[]` has no effect) — final solution: `BSD/Main.lean` adds `import BSD.RankTwo389`, extending the closure naturally.
4. **Final all-green**: `lake build -R` all green, 7690 jobs (exit 0); `lake build BSD` all green, 3476 jobs (BSD 14 oleans, including RankTwo389).

Engineering notes: probes `_check_rank_two_389.lean` (closure check), `_probe_pow.lean` (pow lemma signature) kept; the historical `BSD\.lake` (old standalone-package artifacts) was deleted (under Lake 5.0 the lean_lib artifacts live in the workspace-level `.lake/build/lib/lean/BSD/`); the gens "(0,0),(1,0)" in the `EulerSystem.rank_389a1` comment mismatch the Sage-measured gens (historical; RankTwo389 uses the measured gens).

## 15. 2026-10-19: The spectral-duality line — ζ_K zero-union structure (sharing the χ₅ structure with BSD)

Main line: the spectral-duality series (K = ℚ(√5), Dedekind ζ_K = ζ·L(χ₅), χ₅ the real character mod 5) pushes the ζ_K on-line proportion lower bound; Assaults XVI–XIX closed. The connection point with the BSD library: **the E⁵ twist has local factors a_p = χ₅(p)·a_p(E) (§1 convention), i.e. L(E⁵, s) = L(E, χ₅, s) — the same character structure as L(s,χ₅)**; the spectral-duality work studies the zero structure of the latter (and how it merges into the union zeros of ζ_K).

### 15.1 Numerical system (reusable)

- `zeros_T6e5.npz`: ζ 999,492 zeros + L(χ₅) 1,150,050 zeros (t ∈ [6.6, 6×10⁵], Riemann–Siegel main-term root finding; first 15 L zeros verified with mpmath); N_K = 2,149,542, density ρ_K = 3.58.
- `route2m.json`: cross-family pair correlation F_cross/F_jit spectrum (α ∈ [0,2], 41 points); ∫dF ≈ −0.0094 (pairing white noise), F_cross/F_jit ≈ 0.99.
- Fourier profiles (`fourier_spectrum.png`): χ₅(p) = −1 prime terms **cancel exactly** in the union (∫P_K ≈ 10⁻⁵; suppression factor 10³–10⁵), χ₅(p) = +1 enhance exactly ×4, χ₅(5) = 0 terms vanish in L.

### 15.2 Three defensible results

1. **Q(0) ≥ 1 ⟹ union lower bound identically non-positive (Assault XVIII, decisive negative result)**: Proposition 2.1 (Lamzouri arXiv:2609.02882) applied to Z_K = Z_ζ ∪ Z_L has lower bound 2−C_MT(f)−Q(0)(f) ≤ 0, independent of the mollifier (extremal f₀ −0.3338 / uniform −0.3333). **The Hilbert-space inequality fails for unions of product L-functions** — cross-family pairs are pure debt (Q(0) ≥ 1 in ΣK², no corresponding count in Σ1).
2. **Cross-family pairing explicit formula (Theorem 3.1′)**: the ζ–L(χ₅) cross-family pair correlation has main term f(0) (density-level coefficient 1), prime terms killed by the χ₅ character oscillation (O(x^{−1/2}) type) — a generalization of Montgomery pair correlation to pairs of L-functions, a pair-correlation-theory tool independent of the truth of RH.
3. **Prime-term net suppression and remainder magnitude (Assault XIX)**: Σ_p χ₅(p)/√p has bounded partial sums ≤ 2.46 (character-sum cancellation); the union sup envelope is below the single family at every scale (0.57–0.94); in mean square the union is 1.263× the single family (no second-moment gain); the on-line proportion remainder is 0.6725−O(10⁻⁵~10⁻³) — **the gap is in the constant, not the remainder**.

### 15.3 L(χ₅) main-term correction (important repair to the numerical workflow)

N_L(T) = (T/2π)[log(T/2π)+log 5−1]+O(log qT) — the Γ(s/2) phase carries (T/2)log(qT/2π); log q = log 5 is a linear term; historical scripts using the ζ convention (missing log q) produced C_L ≈ 75098 spurious main terms, now fixed; the L zero data carry a ~0.27% R-S root-finding systematic artifact (trend −0.0052/unit), disclosed (difference conventions ε, Fourier are immune).

### 15.4 Strategic positioning and connections

- **Relation to 7/8 (0.874957, QRH class)**: 0.6725 is the unconditional Levinson–Lamzouri constant; 0.875 is a quasi-random-premise constant — different mechanisms, not a constant push of the same argument; chasing the boundary has no increment.
- **Defensible assets**: cross-family pairing explicit formula + character-oscillation cancellation + the Q(0) negative result (method boundary); packagable toward "pair-correlation theory of products of L-functions + method boundaries" (document 《ζ_K 零点并集结构》).
- **Spectral-duality chain status**: the agreed reparametrization (ℓ₁,ℓ₂)↦(T,W) of Arthur trace formula ↔ Weil explicit formula remains a belief (not closed to pairing constants), honestly labelled open.
- **Connection with BSD**: shared χ₅ structure (E⁵ twist and L(χ₅)); a θ_K-lower-bound push (if the L4 cross term lands) could supply numerical input for Chebotarev / prime-splitting distribution precision.
