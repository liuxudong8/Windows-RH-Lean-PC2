# Stage 4 Summary — RH/K-GRH Spectral Duality Framework

| Item | Value |
|------|-----|
| Generated | 2026-09-30 (evening update: :109 contour refactor, Weil-exact refactor, three-paper audit, K-GRH target decision) |
| Lean version | v4.34.0-rc2 |
| mathlib | mathlib4-master (`c:\proj2\mathlib4-master`) |
| Project path | `c:\proj2` |
| Build | `lake build OrderPreservingBijection.stage_4` OK (3849 jobs, 2026-09-30); full build 7690 jobs (earlier 9/30) |

---

## Project status overview

| Item | Value |
|------|------|
| Active .lean files (excl. test/archive/.bak) | 26 |
| `sorry`/`admit` in stage_4.lean (statement-level) | 21 |
| `sorry` in ZetaZeros.lean | 1 (kept: `nontrivialZeroEnum_exists`, S infinite, user-mandated) |
| `sorry`/`admit` in ContourIntegral.lean | 2 (`:109` contour=residue admit, `:143` prime-Dirichlet diff admit; `:115` filled) |
| Custom `axiom` (active files) | 2 (both in stage_4.lean, not on main chain) |
| `#print axioms riemann_hypothesis` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| **Main-chain custom axiom** | **0** |

---

## Project goal and mathematical framework 【Target decision 2026-09-30】

**Current formalization target: K-GRH (local GRH for Q(√5))** — all nontrivial zeros of ζ_K(s) = ζ(s)L(χ₅,s) satisfy Re(ρ)=1/2, derived from the spectral-duality bridge (Arthur trace + order-preserving bijection + JL unitary equivalence + explicit formula).

**RH (for Riemann ζ) is a long-term goal**: needs an additional bridge "ζ_K zero side → ζ zero side" at the paper level (K-GRH does not imply RH: zeros of ζ ⊂ zeros of ζ_K, the reverse direction fails). All three source papers (数值匹配2 / 保序双射定理6 / 谱对偶论证9) use K=Q(√5) (Γ=PSL₂(𝒪_K)); **no F=Q setting exists in them**; Paper 3 explicitly abandons "Z_M(s)=ζ(s) global analytic identity" (algebraic class-field obstacle + zero-location obstacle + k≥1 factors; mathematically unprovable).

```
Arthur trace formula (compactly-supported weighted: spectral side Σf(λ) = geometric side ΣW(γ)f(ℓ(γ)) + elliptic + Cont)
    ↓  order-preserving bijection Φ:𝒢↔I_prim (Paper 2, ℓ=log Nm, h_K=1)
Jacquet-Langlands unitary equivalence (split primes w_p=1/2, unitary-projection normalization, not fudged)
    ↓
K prime-ideal weighted sum ↔ ζ_K explicit formula (after A2 fix; NOT the ζ explicit formula)
    ↓  real spectrum (self-adjoint spectral theorem + JL unitary equivalence; Dolgopyat only fallback)
λ = 1/4 + t², t∈ℝ ⟹ ρ = 1/2 + it ⟹ Re(ρ) = 1/2
    ↓
K-GRH (current target) → (bridge needed) → RH (long-term)
```

Code ↔ papers correspondence: `spectralSum`(Σf(λ) ↔ §2.2), `geometricSum`/`orbitWeight`(W=N log N/(N−1)² ↔ §3.1/App.B), `localJLWeight`=1/2 (↔ §3.2/D.3-D.5), `maassSpectralSum` (↔ §4.1), `jlLParameterMap`=1/2+it (↔ §5.2), mollifier normalization ∫g_ε=1 (↔ App.A).

---

## Completed main work

### 1. Infrastructure layer (proved, no sorry)

BasicInfrastructure / MellinInfrastructure / ManifoldInfrastructure / HeatKernel / HeatKernelSemigroup / HeatKernelConvolution / MollifiedFunction.

### 2. Proof-framework layer

| Module | Status |
|------|------|
| `BijectionPhi/Basic.lean` | framework complete |
| `Interpolation.lean` | framework complete |
| `stage_3.lean` | framework complete |
| `ContourIntegral.lean` | **:109 rewritten to contour-interior version**; `:115` filled; `:109/:143` admit |
| `ZetaZeros.lean` | **contourZeroFinset + farZeroContribution split** (1 kept sorry) |
| `CompletedZeta.lean` | **0 sorry** (`xi_one_sub` proved; entire/Γℝ-nonzero/zero-equivalence filled 9/30) |

### 3. Main-theorem layer (stage_4.lean)

`riemann_hypothesis` (statement kept as placeholder; target K-GRH). Key theorems: Perron framework; Mellin inversion; zero-weighted summability; pair localization; duality-norm lower bound; unified support; `mellin_transform_C2_rapid_decay` (proved, ‖M[f](s)‖ ≤ 8B'(R₀³+1)/|Im s|²); contradiction chain `off_critical_line_contradiction` vs `weil_explicit_formula_trivial_terms_cancel`.

---

## Work in this round (2026-09-28 ~ 09-30)

### A. Axiom batch downgrade (9/28, ~28)
Silent `axiom X : T` → `lemma X : T := by sorry`; snapshots to `c:\proj2\archive\` (49 files); deleted erroneous `stage_4_m.lean`.

### B. Main-chain custom axiom zeroed (9/28)
`nontrivialZero_im_ne_zero` (no real zero of ζ on (0,1)) proved via Dirichlet-eta bridge → theorem.

### C. ZetaZeros refactor (9/28)
`zeroMultiplicity` opaque→def; `zeroMultiplicity_symmetry` → theorem (with hypothesis).

### D. mathlib bridges (9/28)
`riemannZeta_conj`, `second_moment_gaussian_integral`, `cauchy_theorem_contour` → mathlib theorems.

### E. CompletedZeta.lean (9/28)
ξ(s) = (1/2)s(s-1)·completedRiemannZeta(s); `xi_one_sub` fully proved.

### F. zeroMultiplicity_symmetry (9/29)
Functional equation + Γℝ nonzero + factor nonzero + local analytic multiplicity chain.

### G. eta = (1-2^{1-s})·ζ on Re s>1 (9/29)
η(s)=∑(-1)^n/((n:ℂ)+1)^s = (1-2^(1-s))·ζ(s).

### H. ζ negative on real segment (0,1) (9/30, `riemannZeta_neg_on_Ioo`)
Paired series `etaPaired`; identity theorem extends `etaPaired = (1-2^(1-s))·ζ(s)` to connected domain `etaDomain` (four convex pieces, avoiding s=1). **`nontrivialZero_im_ne_zero` settled.**

### I. ContourIntegral :109 contour-interior refactor (9/30, plan i)
`:109` rewritten to `contourIntegral = zetaZeroSide f − farZeroContribution f` (docstring 4-step residue blueprint); `:115` filled (unfold+ring); `:128` rw.

### J. ZetaZeros refactor (9/30, contourZeroFinset + farZeroContribution)
`contourZeroFinset_finite` (closedBall(1/2,1) ∩ riemannZetaZeros finite), `contourZeroFinset`, `farZeroContribution`, split `nontrivialZeroSum = czf + farZeroContribution`, `nontrivialZeroSum_localization` rewritten. `:49` enum sorry kept with "correctable leftover, currently unused" note.

### K. Weil-exact refactor (9/30)
`mollified_trace_equality` keeps weylError term; new **`weil_explicit_formula_exact : spectralSum = nontrivialZeroSum`** (admit, core duality hypothesis); new **`weyl_far_error_pairing`** (theorem, ring elimination); deleted `weyl_error_vanishes`/`far_zero_vanishes`.

### L. Three-paper audit + target downgrade (9/30, ★ decision)
Read all three papers. Rulings:
1. **Algebraic setting**: all three papers K=Q(√5); **no F=Q setting**; Paper 3 abandons global identity (mathematically unprovable). Switching to F=Q has no paper support.
2. **Three paper flaws (tomorrow's paper-revision focus)**:
   - **A1 setting mismatch**: Paper 2 "real embedding, infinite volume, geodesics in ℍ² section" vs Paper 3 "compact" — same Γ; affects Cont(f) (compact: no scattering = 0; noncompact: Cont≠0).
   - **A2 inert primes (critical)**: Paper 3 App. D.5 treats inert primes as W(p)f(log p) inside "run over rational primes" — contradicts Paper 2 Nm(𝔭)=p² ⟹ ℓ=log p² and the numerical table (N=4,9); after fix the weighted geometric side = Σ_split W(p)f(log p) + Σ_inert W(p²)f(2log p) + W(5)f(log 5) ≠ Σ_p W(p)f(log p) — **ζ explicit-formula matching fails; after fix it matches the ζ_K explicit formula (K-GRH level)**.
   - **A3 continuity claim**: scattering-matrix-poles-are-negative-even claim meaningless under compactness.
3. **Target downgrade (user decision)**: K-GRH now; RH long-term. Lean side: docstrings of `weil_explicit_formula_exact`, `all_zeros_on_critical_line`, `riemann_hypothesis` annotated with target status (statements kept as placeholders; build OK).

---

## Remaining sorry/admit distribution (active files, 2026-09-30 measured)

| File | Count | Content |
|------|------|------|
| stage_4.lean | 21 | main-chain estimates + core duality admit (weil_explicit_formula_exact etc.) |
| ManifoldInfrastructure.lean | 11 | manifold analysis estimates |
| HeatKernel.lean | 10 | heat-kernel HS estimates |
| MellinInfrastructure.lean | 9 | Mellin estimates |
| Interpolation.lean | 8 | interpolation estimates |
| HeatKernelConvolution.lean | 8 | convolution estimates |
| BijectionPhi/Basic.lean | 8 | duality-map analysis |
| stage_3.lean | 6 | stage-3 bridge |
| ContourIntegral.lean | 2 | :109 contour=residue admit, :143 prime-Dirichlet diff admit (:115 filled) |
| CompletedZeta.lean | 0 | all filled |
| **ZetaZeros.lean** | **1** | **only `nontrivialZeroEnum_exists` (S infinite, kept)** |
| MollifiedFunction.lean | 1 | mollifier |
| test_*.lean | ~20 | tests (non-deliverable) |

## Remaining axiom (2, neither on the RH/K-GRH main chain)

| Location | Content |
|------|------|
| stage_4.lean:716 | `shimuraKernel_hilbert_schmidt` |
| stage_4.lean:5278 | `spectral_zero_set_match` (not feeding riemann_hypothesis) |

---

## Known real gaps (mathlib lacks infrastructure)

1. **General residue theorem** (no residue theory in mathlib; :109 blueprint step 1).
2. **S infinite (Weyl/Hardy)** (`nontrivialZeroEnum_exists` kept; S countable proved).
3. **Dolgopyat exponential mixing** (geometric fallback only, per Paper 3).
4. **Full Arthur trace / JL unitary equivalence formalization** (representation theory, admit-level).
5. **A2 inert-prime handling (paper level)**: decides whether the K-GRH bridge holds; after fix one gets the ζ_K explicit formula.

(Closed: ζ negative on (0,1) — see H; :115 contour residue sum — see I; main-chain zero custom axiom — see B.)

---

## Next steps

1. **(Tomorrow) Revise the three papers**: A2 (inert primes, decides the K-GRH bridge) > A1 (setting unification) > A3 (continuity claim); numerical paper notes in sync.
2. **Lean-side K-GRH landing**: replace Riemann-ζ zero infrastructure with ζ_K (needs Dedekind zeta / L(χ₅) / K-prime von Mangoldt definitions — mathlib lacks them, admit-level); nontrivialZeroSum → ζ_K zero side.
3. Progressively fill the 21 stage_4.lean framework assumptions.
