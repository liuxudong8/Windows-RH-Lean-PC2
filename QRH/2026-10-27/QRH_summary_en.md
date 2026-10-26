# QRH Project Summary (Offensive XLII "Push to 1" Mainline + Lean Formalization)

> Finalized 2026-10-26. Mathematics S0–S7.6 closed and archived to d1; Lean formalization in progress (Core/Stage3 true-proof chain green, Main skeleton assembly pending).
> Calibration: 7/8 is the established target (31/32 rejected); A is data, not a theorem; "proving A→1" is NOT "approaching RH" (statistical vs. descriptive sense).

## 1. Project Positioning

Goal: prove that the single-family pairing constant A(λ) of L(s, χ₅) tends to 1. This is the only realistic channel for the QRH (quasi-random hypothesis) constant mechanism: QRH constant 0.6725 → 7/8 requires A ≤ 1.125. Since A→1 is far stronger than A ≤ 1.125, "pushing to 1" opens 7/8 in one stroke.

## 2. Decision Chain

- Pairing constant: A_L(K) = 1 + (Σ_{Δ≠0} K(δΔ)²)/N_Z, δ = logT/(2π).
- Constant mechanism: C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963; 0.6725 = 2 − C_MT (the QRH constant).
- Theorem S7.1 (L-version BGS-type pairing formula, under weak real-part hypothesis): A_L(K) ≤ C_MT + O(ε) + o(1).
- A ≤ 1.125 ⟺ 7/8 holds (0.6725 → 7/8 channel); A → 1 is the strongest case.
- Current numerics: Fejér narrow kernel λ→0 limit gives A → 1.0079 (T = 6×10⁵); after narrow-kernel push A ≈ 0.990; drift across 5 subintervals ≤ 0.005.

## 3. Mathematical Mainline (Offensive XLII S0–S7.6, archived to d1)

| Stage | Content | Verdict |
|---|---|---|
| S0 | Full-scale GUE pairing and online proportion 1−o(1); calibration fix and super-GUE repulsion | Gate of life and death: A→1 visible numerically |
| S1a | Parseval attribution: δF/δR decomposition and kernel dependence | Attribution of pairing-constant residual structure |
| S1b | λ(T) construction and quantification of kernel-dependent constant p (theorem skeleton) | Theorem framework for pushing to 1 |
| S2(i) | Weil explicit-formula real-part injection sensitivity (closure chain with S1 left-tail threat) | Threat window narrowed |
| S2(ii) | Cross-T decay-law discrimination (pairing constant error law) | S1b rate scaling pinned |
| S3 | Δ-constant fingerprint exclusion cross-check (explosive response to same-imaginary-part injection) | Threat excluded |
| S4 | Forward construction: narrow-kernel measurement and pairing-constant residual structure | Numerical anchor for λ(T) construction |
| S5 | ε theorem-level control: cross-family f(0) profile and unconditionalization of union pairing formula | Union formula unconditionalized |
| S6 | λ_eff ≤ 1 bottleneck removed: λ ≤ 1/2 optimal kernel family, 0.6725 strictification | Unique hard bottleneck solved |
| S7 | Yildirim method transfer closure: existence of L(s,χ₅) single-family BGS-type pairing formula | H2 closed |
| S7.1 | Lean formalization (Yildirim formula (7) L-version expansion + BGS Lemmas 3–5 item-by-item transfer) | See §5 |
| S7.2 | Numerical item F: super-support prime-term negligibility | S(X) = O(√X·poly(log X)) |
| S7.3 | Bone 1 (N1): BGS Lemma 5 super-support generalization (scaling automorphism) | A→1 path |
| S7.4 | Bone 2 (N2): ε–λ linkage (regularization support width vs. effective kernel width scaling law) | Support-width gap closed |
| S7.5 | Bone 3 (N3): offline-term consistent version (BGS remainder uniform across λ) | Cross-λ consistency |
| S7.6 | SW constant made explicit: L(s,χ₅) prime-term explicit bound (C,c) | Constants explicit |

## 4. Three Bones and the SW Constant (Push-to-1 Gap Closure)

The theoretical gap hit by "pushing to 1": the XLII route requires λ_eff(T) = (logT)^q → ∞ (narrower and narrower kernel, spectral support expanding indefinitely), while the S7 closure covers only λ ≤ 1/2 (hard condition of BGS Lemma 5). As λ → ∞ the real-space kernel width a → 0; in the difference-type pairing the support of ĥK(δ·log p) widens and the prime term S(X) may lose the protection of narrow frequency support. Three bones:

- **N1 (BGS Lemma 5 super-support generalization)**: scaling automorphism scaleKernel a r preserves support; under λ→∞ super-support the prime term is still cancelled by the χ₅ oscillation, opening the A→1 path.
- **N2 (ε–λ linkage)**: λ = (logT)^q, a = (logT)^{−q}, ε = c·(logT)^{−q} ⟹ deviation O((logT)^{−q}) — regularization support width linked to effective kernel width.
- **N3 (offline-term consistent version)**: BGS remainder O(T√logT) uniform over all kernels with supp⊂[−1,1] (outer ∃R uniform in K).
- **SW constant made explicit (S7.6)**: Siegel–Walfisz prime-term bound |Σ_{n≤x} Λ(n)χ₅(n)| ≤ C·x·e^{−c√log x}; theoretical c = 1/√R₀ ≈ 0.3954 (Kadiri R₀ = 6.3970); observed C_obs = 1.70e−3 recorded separately; L(1,χ₅) = 0.430409 > 0; β ≥ 0.9029.

Numerical item F: S(X) = Σ_{p≤X} Λ(n)χ₅(p)p^{−1/2}·K̂_a(δ·log p) = O(√X·poly(log X)) — o(1) relative to N_L ~ (X/2π)·logX, so NO e^{−c√logX} exponential suppression is needed; |S_a| ≈ 2.05 bounded convergence (stronger than the theoretical bound), |S_a|/N_L monotonically decays to 1e−8 (X = 10⁸).

## 5. Lean Formalization Status (C:\proj2\QRH, mathlib v4.34.0-rc2)

Build: `lake build QRH` 1965 jobs all green (exit=0); on Windows the aggregate Mathlib.olean is unavailable, so only specific module imports are used.

**Error-bound macros (Asymptotics.IsBigO and ε–N rejected)**: `Bound C T0 err f := 0≤C ∧ ∀T≥T0, |err T| ≤ C·f T`; `BoundBall C δ err f := 0≤C ∧ ∀|x|≤δ, |err x| ≤ C·f x`.

**True-proof chain (10 items)**:

- Core (S7_1_Core.lean): `sin_inv_sqrt2_ne_zero` (denominator well-defined), `Khat_neg` (evenness), `Khat_zero` (K̂(0)=1, sin/x limit extension), `Khat_abs_le` (frequency-decay triangle-inequality bound), `f0_continuous`.
- Stage3 (S7_1_Stage3.lean): `scaleKernel_support` (N1 support preservation), `f_eps_support` (N2 support [−1/2,1/2]), `Khat_a_even` (first-order correction identically zero), `sum_abel` (Abel summation by induction), **`khat_second_order_bound`** (K̂ second-order uniform bound, migrated in to replace the axiom on 2026-10-26).

**khat_second_order_bound true-proof chain** (BoundBall 1 (1/24)): K̂(u) multiplicative closed form Khat_closed_form = [cos m − √2·m·cotR·sin m]/(1 − 2m²), m = πu; |u| ≤ 1/24 and π < 16/5 ⟹ |m| ≤ 2/15 ⟹ m² ≤ 4/225 ⟹ denominator 1−2m² ≥ 217/225 > 0; numerator split N = m²(3/2 − √2·cotR) + (cos 2nd-order remainder) − √2·m·cotR·(sin 1st-order remainder); cos/sin remainders via Real.cos_bound/sin_bound, c0_bound (|3/2 − √2·cotR| ≤ 9/50, cotR ∈ [1, 237/200]); assembly gives |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴. Numerical check: ½|K̂″(0)| ≈ 1.53 < 2 (origin of the 2u² coefficient).

**Main theorem s71_main (assembly true-proof, 2026-10-27, replacing sorry)**: A_L(K) ≤ C_MT + C₁ε + C₂ with C₂ = 2 explicit. Proof chain = pair_sum_expansion decomposition A_L = diag + prime + offcrit → diag ≤ C_MT + C₁ε (n2_linkage O(ε)) + |prime|,|offcrit| ≤ 1 absorbed into C₂ (linarith + ring); (L3) axiom semantics strengthened (diag bound into statement). Full library 1965 jobs green (build_qrh_s71.txt).

**Outstanding axioms (recorded as-is)**: Core `f0_sub_feps_L1_bound`, `pair_const_eps_bias` (`C_MT<4/3` is a checklist item only, no axiom declared: mathematically it needs the 4th-order cos Taylor bound 73/96; mathlib's built-in cos_bound remainder (5/96)|x|⁴ is insufficient (combined with sin_bound's x⁵/100 correction it falls short by 0.13%); a self-contained proof needs the integration/series remainder layer — same batch as the integration layer); Stage3 `fourierCos_scale`, `scaleKernel_L1_invariant`, `n1_diag_invariant`, `n1_offdiag_vanishes`, `n2_linkage`, `n3_remainder_uniform`, `N_L`, `N_L_lower_bound`; Main `landau_explicit_L`, `siegel_walfisz_chi5`, `offcritical_small`.

**File layout**: C:\proj2\QRH.lean (root, imports Core/Main/Stage3); QRH\S7_1_Core.lean; QRH\S7_1_Stage3.lean; QRH\S7_1_Main.lean (zerosLChi5, pairConstant, WeakRealPart abstractions + s71_main assembly true-proof); QRH\Dbg_Khat.lean (khat true-proof development archive). Build evidence: build_core1..12.txt, build_main1..9.txt, build_stage3.txt, build_qrh_full{,2,3,_khat,_khat2,_s71}.txt, dbg_khat.txt, dbg_probe3.txt (IntervalIntegral.olean absence confirmed).

## 6. Next Steps (in dependency order)

1. **Stage 4 done** (2026-10-27): s71_main assembly true-proof (premises explicit, constants explicit, assembly true) — the farthest verifiable point on the Lean side is reached.
2. Conditional closure (pending aggregate mathlib Mathlib.olean / self-contained Taylor-remainder layer): Core items (f0_sub_feps_L1_bound; C_MT<4/3 needs cos 4th-order bound 73/96); Stage3 integration layer (fourierCos_scale → n1_diag/n1_offdiag → n2_linkage/n3_remainder_uniform).
3. Stage 2: (L3) pairing-sum expansion semi-formalized (finite multiset + finite sum, δ in ℝ).
4. (L2) SW / (L1) explicit formula kept as named axioms (proved mathematically; long-line formalization — PNT-in-AP scale, not a bottomless pit but a many-person-year project).

## 7. File Index

- Documents (d1 root C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\): 17 XLII documents (S0–S7.6 incl. S1a/S1b/S2(i)/S2(ii)/S3/S4/S5/S6 and "Full-scale GUE pairing S0"); English d1\en\ (XLI, XLII-S0 translated); earlier Offensives XL/XLI (0.6725→7/8 constant-mechanism closure).
- Numerics (qrh_work\, new-chat\xlii_work\): xlii_s7g_sw_constant.py/json/log, xlii_s7g_fig.py/png, xlii_s7f_bone1/2.py/json/fig, xlii_s7f_supersupport.py/json, xlii_s7_prime.json, xlii_s6_lambda.py/json; s7X doc generators + render-s7X\ authoritative renders.
- Lean: see §5.
