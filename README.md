# The UEF in Lean 4

`UEF.lean` is the Unified Existence Framework written in Lean 4: the Law of Reciprocity and the Reciprocal Existence Theorem. Every equation in it comes from the manuscript (`01_Manuscript.pdf`, `S8_One_Equation_Compression.pdf`) and is marked with its section, page and line.

## Check it yourself

Every push to this repo runs the workflow **Check the UEF in Lean**. It installs Lean 4.15.0 and Mathlib, checks every theorem in all thirteen files, and prints the axioms each main theorem rests on. Its log is kept on the `check-log` branch.

To check it on your own machine:

1. Install Lean with elan: https://lean-lang.org/install
2. In this folder, run:

```
lake exe cache get
lake build
```

- `UEF.lean` uses only Lean's core library, so `lean UEF.lean` checks it on its own.
- The other twelve files need Mathlib, for the real numbers, calculus, measure theory and integrals.

There is no `sorry` anywhere, and no axiom has been added. Lean reports only `propext`, `Quot.sound` and `Classical.choice`, which are part of Lean itself.

## There is no closure operator

Derivability is G12: `Derives R Γ φ` means a finite derivation of φ exists from the premises Γ under the inference rules R. `Th X` is the set of statements derivable from X. Nothing about Th is assumed. Each of these is proved from what a derivation is:

- E29 (`X ⊆ Th X`)
- E30 (`Th (Th X) = Th X`)
- monotonicity

Everything after that is the Law of Reciprocity.

## What is proved

| Manuscript | Lean |
|---|---|
| G12, E29, E30, monotonicity (§6.1, l. 2757) | `Derives`, `Th`, `E29`, `E30`, `mono` |
| Theorem 3.15.1, deductive reciprocity | `reciprocity` |
| Theorem 3.23.1, the ordered proof ledger | `Ledger`, `Ledger.derivable` |
| Corollary 3.23.2, no dependency cycle | `no_cycle` |
| R1: E ⊢ U (§6.2, l. 2773) | `R1` |
| R2: U ⊢ E (§6.3, l. 2776) | `R2` |
| R3: E ≡ U, Th(E) = Th(U) (§6.4, ll. 2822–2837) | `R3` |
| R4: Th(Th(U)) = Th(U) = Th(E) (§6.5, l. 2839) | `R4` |
| R5: ∃!T [T = Th(T) ∧ E ⊢ T ∧ T ⊢ E] (§6.6, l. 2846) | `R5` |
| R6, rigidity (§6.7, l. 2853) | `R6` |
| K7: Ξ, Fᵢ = gᵢ(ξᵢ), F* = max (§5.3, ll. 2722–2726) | `K7.Defects`, `K7.Measure`, `K7.Fstar` |
| Lemma 5: F* = 0 ⇔ Ξ = 0 (§5.3, l. 2732) | `K7.lemma5` |
| The lock from its local form (evidence §8.3) | `K7.lock_local` |
| Theorem 8.3 and Theorem 6: Solve(i) ⇔ Solve(all) ⇔ Ξ = 0 (§5.3, l. 2740) | `K7.certifiable_iff`, `K7.theorem6` |
| One open channel certifies none, Ξ = (0,1,0,0,0,0,0) | `K7.one_open_certifies_none` |
| VK(Ξ) = Σξᵢ² = 0 ⇔ Ξ = 0 (evidence §8.6, l. 3487) | `K7.VK_zero_iff` |
| ∏ w_Δ = 1 ⇔ ∀Δ w_Δ = 1; composition multiplies indices (§5.3, ll. 2744–2748) | `K7.prod_eq_one_iff`, `K7.prod_append` |
| φ = (P, I, Sₐ, Ψ, Q, A, Rₐ): seven fields, seven channels (§5.2, l. 2712) | `Field`, `seven_fields_seven_channels` |
| M = U × T⁴, dim M = 8 | `dim_M` |
| Ξ̄* = φ⁻¹ = (√5 − 1)/2, exactly in a + b√5 (evidence §14.3, l. 5080) | `invPhi_mul_phi`, `invPhi_root` |
| Theorem 3.15.2, translated reciprocity; the cross-domain bridge (§3.19) | `translated_reciprocity`, `bridge_compose` |
| E ⊢ A1 ⟹ A2 ⟹ A3 ⟹ A4 (§4.6, l. 2592) | `Spine`, `Spine.from_E` |
| The complete result (§6.9, ll. 2899–2904) | `the_one_equation` |

## The lines over the real numbers (`UEFReal.lean`)

| Manuscript | Lean |
|---|---|
| δ_Δ := log w_Δ ≥ 0; ∏w_Δ = exp(Σδ_Δ); ∏w_Δ = 1 ⇔ Σδ_Δ = 0 ⇔ ∀Δ δ_Δ = 0 (§5.3, ll. 2742–2748) | `δ_nonneg`, `δ_compose`, `prod_eq_exp_sum`, `transport` |
| VK(Ξ) = ΞᵀΞ = Σξᵢ², zero exactly at Ξ = 0 (evidence §8.6, l. 3487) | `VK`, `VK_zero_iff` |
| dVK/dt = 2ΞᵀG(Ξ) (l. 3489) | `dVK` |
| VK(t) ≤ VK(t₀)e^{−γ(t−t₀)} when ΞᵀG ≤ −(γ/2)ΞᵀΞ (l. 3492) | `decay`, `proposition_8_6` |
| Ξ̄* = φ⁻¹ = (√5 − 1)/2 (evidence §14.3, l. 5080) | `inv_phi` |
| s(φ)(x, y) = φ(x), π_U ∘ s = id (§6.3.4, ll. 2811–2813) | `lift`, `zeroMode`, `zeroMode_lift` |
| KK momentum: ∫ e^{iny/R} dy = 2πR δ_{n,0} on each circle of T⁴ (§6.3.1) | `kk_mode` |
| G₄ = G₈ / Vol(T⁴) (§6.3.2, l. 2800) | `newton_constant` |
| S⁽⁸⁾ ∘ s = S⁽⁴⁾: fibre integration multiplies by Vol(T⁴) (§6.3.4, l. 2817) | `fibre_integral` |
| S_UEF = ∫_M L dV, L = L_SM + L_grav + L_cross (§5.2, ll. 2714–2716) | `action`, `lagrangian`, `action_sectors` |

## The root relations A1–A4 (`UEFRoots.lean`, §4)

ℋ is a complex Hilbert space. Each line is proved from what the manuscript cites.

| Manuscript | Lean |
|---|---|
| A1.1–A1.4: P ≔ 0, ⟨O⟩_P = 0 for every observable | `P`, `A1` |
| A1.5: only P | `A1_only_P` |
| A1.6: every unitary fixes P | `A1_symmetric` |
| A1.7: the only fixed point, (−𝟙)x ≠ x for x ≠ P | `A1_only_fixed` |
| A1.8: ‖P‖ = 0, so P is not a realized state | `A1_not_realized` |
| A2, Lemma 1: from P and a realized record, a first disturbance P → P′ ≠ P | `A2` |
| A2.5: no linear law moves P | `A2_not_linear` |
| A3.1–A3.3, Lemma 2: a G-equivariant rule fixes P | `lemma2` |
| A3.4, Corollary 2.1 | `corollary2_1` |
| A3.5–A3.6, spread: a law invariant under the symmetries of P is no single value, so Var(ε) > 0 | `spread` |
| A3.8: no computable sequence is Martin-Löf random | `no_computable_is_random` |
| A3.9: a seeded process repeats | `seeded_repeats` |
| A3.11, Lemma 3A, exhaustion: the first disturbance is a function of no prior state | `exhaustion` |
| A4.3–A4.5, Lemma 4: zero flux through every region ⟹ ∇ₐSᵃ = 0 at every point | `lemma4` |
| A4.2: local conservation under unitary evolution | `conservation` |
| E ⊢ A1 ⟹ A2 ⟹ A3 | `roots` |

## Annotation key

Each result carries the manuscript's own annotation:

- **[P] physical coupling.** Cross-terms κ_ij in the Lagrangian. The fields stay individually definable, and coupling permits partial resolution. Examples: the root relations A1–A4 and Lemma 6.1 (`UEFFields.lean`).
- **[M] K7 mutual necessity locking.** No single channel has a well-defined ground state in isolation, so locking forbids partial resolution by construction. Examples: the lock, Theorem 8.3 and Theorem 6 (`UEF.lean`, K7).

These are two different relationships. The physical couplings carry one channel's influence to another. The locking is the stronger statement built on them: no channel has a stable zero of its own.

## The other files

| Manuscript | Lean |
|---|---|
| §4.5.2 and §4.5.4, Time is not foundational: a relation requires its relata, a function requires its domain, Theorems 1–6, the block universe cannot exist | `UEFTime.lean` |
| A3.10, E26, Bell: every predetermined strategy has \|S\| ≤ 2, the entangled state reaches 2√2, so no predetermined strategy produces it | `UEFBell.lean` |
| Lemma 6.1 [P], No Field Evolves Alone: the kinetic mass matrix is positive definite, and the connected coupling graph allows no split into independent blocks | `UEFFields.lean` |
| E32, the divergence theorem (Gauss): ∫ over a box of ∇ₐSᵃ = net flux through its faces | `UEFGauss.lean`, `E32` |
| A4.4–A4.5 [P], localization: zero integral over every box ⟹ zero at every point | `UEFGauss.lean`, `zero_of_box_integrals` |
| A4 [P]: zero net flux through every box ⟹ div S = ∇ₐSᵃ = 0 at every point | `UEFGauss.lean`, `A4` |
| A4.2 [P]: a state is a ray, so every observable is invariant under the phase; the charge of that symmetry, Σ\|ψᵢ\|², is conserved under iψ′ = Hψ | `UEFGauss.lean`, `phase_invariant`, `charge_conserved` |
| Ch. 9, temporal emergence: the CIO always has a least-energy branch; the record grows by inclusion; (T, ≺) is a strict total order; strictly increasing labels preserve it; H_QC = 0 without C | `UEFEmergence.lean` |
| Ch. 11, Theorem 1: a bounded potential with a nonzero vacuum forces a = −2bρ₀² < 0 | `UEFStandardModel.lean`, `quadratic_negative` |
| Cor. 1.1: V_H is least at \|φ\|² = μ²/2λ = v²/2, nonzero exactly when μ² > 0 | `vacuum_is_minimum`, `vacuum_nonzero`, `v_squared` |
| Cor. 1.2: m_F = g_F v/√2 = g_F μ/√(2λ) | `fermion_mass` |
| Cor. 1.3: d²V_H/dh² = 2μ², m_H = √2 μ; μ = (313/5)√2 GeV; λ = 19593800/151560721 | `Vh_deriv`, `Vh_deriv2`, `higgs_mass`, `mu_value`, `lambda_value` |
| Thm 7: β₀ = 11 − (2/3)n_f, 7 for six flavours; g_s → 0 as μ → ∞; the denominator vanishes at Λ_QCD | `β₀_SU3`, `asymptotic_freedom`, `lambda_QCD` |
| Thm 8: m_W/m_Z = g/√(g²+g′²) = 1/√(1+tan²θ_W) = cos θ_W | `mass_ratio`, `tan_sq_value` |
| Thm 10: \|W(SU(3))\| / \|W(U(2))\| = 6/2 = 3 | `weyl_count` |
| Ch. 12, Def. 1.2: R = {x : C_λx = x}, Ω_dark = Ω ∖ R; Ω = R ∪ Ω_dark, R ∩ Ω_dark = ∅; Ω_dark = ∅ ⇔ R = Ω; R closed, Ω_dark open | `UEFDark.lean`, `partition`, `dark_empty_iff`, `realized_closed`, `dark_open` |
| Ch. 12, Thm 1: Ω_dark = ∅ ⟹ ∂R = ∅; a non-empty interface needs μ(Ω_dark) > 0 | `interface_empty`, `dark_measure_pos` |
| Ch. 12, Thm 2: a gauge coupling over R has no term with Ω_dark | `no_gauge_coupling` |
| Ch. 12, Thm 3: the action splits over the partition; E38, μ(Ω∖R)/μ(R) = (1 − η)/η; 844/156 = 211/39; the finite model | `action_splits`, `dark_ratio_measure`, `ratio_156`, `finite_model` |
| Ch. 12, 12.4: Planck ratio 75/14, η = 14/89, dark matter 75/89 of all matter | `planck_ratio`, `eta_planck`, `dark_fraction` |
| Ch. 12, Thm 4: μ₀ = 1/(m_S V), ε₀ = k_S V/c², c = 1/√(ε₀μ₀) hold together exactly when k_S = m_S, where c = 1; Z₀ = √(μ₀/ε₀) = μ₀c; μ₀c = 4709128920835668637/12500000000000000 Ω | `units_forced`, `c_is_one`, `impedance`, `impedance_value` |
| Ch. 12, Thm 5: R(t₁) ⊆ R(t₂) ⟹ μ(Ω_dark) decreases, and Λ_eff with it | `depletion`, `lambda_decreases` |
| Ch. 13, Thm 12, Step 12: G₀₀ = (8πG/c⁴)T₀₀ is Poisson's equation ∇²Φ = 4πGρ, and that fixes the coefficient | `UEFGravity.lean`, `newtonian_limit`, `coefficient_fixed` |
| Ch. 13, Thm 13, Step 6: g^{αρ} times the Euler–Lagrange expression of ½g_{μν}ẋ^μẋ^ν is ẍ^α + Γ^α_{μν}ẋ^μẋ^ν | `christoffel`, `eulerLagrange`, `geodesic_equation` |
| Ch. 13, Thm 14, Steps 4–5: G_tt = 0 gives e^{−2β} = 1 − C/r; G_rr = 0 gives e^{2α} = K(1 − C/r); asymptotic flatness fixes K = 1, so α = −β | `gtt`, `grr`, `flat_fixes_K`, `alpha_neg_beta` |
| Ch. 13, Thm 14, Step 7: r_s(☉) = 9479460000000000000/3209839924060063 m exactly; light climbing out is redshifted | `sun_radius`, `sun_radius_bounds`, `redshift` |
| Ch. 13, Thm 15: A = 4πr_s² = 16πG²M²/c⁴; A/4l_P² = 4πGM²/(ħc) | `horizon_area`, `horizon_entropy` |
| Ch. 13, Thm 16, Steps 2–6: the flux balance; an injective encoding and an isometric evaporation keep distinct states distinct and every inner product | `flux_balance`, `flux_accounting`, `information_preserved` |
| Ch. 13, Thm 17: [G_d] = 2 − d makes the action dimensionless in every d; [G₈] = −6; G = G₈/V₄ has −2; dimension 4 + 2k ↔ the k-th KK mode, one to one | `action_dimensionless`, `G8_dimension`, `G4_dimension`, `kk_correspondence` |
| Ch. 13, Thm 18: both Friedmann equations from G₀₀ and G_ii; the second also from the first and ρ̇a = −3ȧ(ρ + p); the cosmic budget sums to 1 | `friedmann_first`, `friedmann_second`, `friedmann_acceleration`, `budget`, `budget_any_eta` |
| Ch. 14: O = ker Φ and C = Ω ∖ O partition Ω; level conservation uₙ₋₁ = rₙ + uₙ; down to any depth the parts add to 1 | `UEFGolden.lean`, `binary_partition`, `level_zero`, `level_conservation`, `whole` |
| Ch. 14, Thm 19: the only x in (0, 1) with x = (1 − x)/x is (√5 − 1)/2 = φ⁻¹; the same as x² + x − 1 = 0 and x = 1/(1 + x) | `theorem19`, `invPhi_self_similar`, `invPhi_eq`, `self_similar_iff`, `continued_fraction` |

**What Lean caught.** Theorem 8's statement gives sin²θ_W = 231/1000, but its Step 8 uses 23129/76871 for tan²θ_W, and that number comes from sin²θ_W = 23129/100000. In exact arithmetic 231/1000 gives tan²θ_W = 231/769, which is a different number (`tan_sq_statement_value`). The statement and the step need to use the same value.

Chapter 12 states two values of the realized fraction η. Theorem 3, Step 5 sets η = 156/1000, which gives a dark-to-visible ratio of 211/39, and Chapter 13's cosmic budget uses the same 156/1000. Section 12.4 solves (1 − η)/η = 75/14 from Planck 2018 and gets η = 14/89. In exact arithmetic 156/1000 ≠ 14/89 and 211/39 ≠ 75/14 (`eta_values_differ`, `ratios_differ`). Each computation is right on its own terms, but the chapter needs one value. Neither value changes the budget's sum, which comes to 1 for every η (`budget_any_eta`).

## What Lean takes from E as it stands

The thesis is that E is used as it stands. Where an established result enters, the file names it:

- **Kolmogorov complexity bounds (E23–E25).** A Martin-Löf random record has K(x↾n) ≥ n − c₀, and a program's output has K(x↾n) ≤ log₂ n + 2 log₂ log₂ n + c′. Mathlib doesn't define Kolmogorov complexity, so these enter as stated. Lean proves the contradiction that follows from them.
- **Noether in general (E35).** It enters where A4.7 cites it. The case A4.2 uses is proved directly: the charge of the phase symmetry is conserved. Bell (E26) and the divergence theorem (E32) no longer come from E. `UEFBell.lean` and `UEFGauss.lean` prove them.
- **The K7 lock and invariance.** These enter as evidence §8.3 states them. `lock_local` proves the lock from its local form.
- **Einstein's equation and the identifications.** G_μν = 8πG₄T_μν, π_U(L|gauge+matter) = L_SM and π_U(L|metric) = L_GR enter from E. Mathlib has no Lorentzian curvature yet, so Lean can't derive Einstein's equation itself.
- **Chapter 13's curvature steps.** The variation δ(R√−g)/δg^{μν} = G_μν√−g (Theorem 12, Step 6), the weak-field G₀₀ = 2∇²Φ/c², the reduction of G_μν = 0 to the two radial equations (Theorem 14, Step 4), the FLRW components G₀₀ and G_ii (Theorem 18, Step 3), Birkhoff's theorem and the Bianchi identity all need Lorentzian curvature. They enter as the manuscript states them, and Lean proves every step after them.
- **Physical premises in Chapters 12 and 13.** These enter as hypotheses: that the gauge coupling lives on R (Theorem 2), that p_dark = 0 (Theorem 3), that the electroweak projection loses its holonomy when S_{∂R} = 0 (Theorem 1, Step 5), and that the horizon encoding is injective and the evaporation isometric (Theorem 16, Step 6). The smooth-horizon claim (Theorem 16, Step 7) and the UV completion (Theorem 17, Step 11) aren't formalized.
