# The UEF in Lean 4

`UEF.lean` is the Unified Existence Framework written in Lean 4: the Law of Reciprocity and the Reciprocal Existence Theorem. Every equation in it comes from the manuscript (`01_Manuscript.pdf`, `S8_One_Equation_Compression.pdf`) and is marked with its section, page and line.

## Check it yourself

Every push to this repo runs the workflow **Check the UEF in Lean**. It installs Lean 4.15.0 and Mathlib, checks every theorem in all thirty files, and prints the axioms each main theorem rests on. Its log is kept on the `check-log` branch.

To check it on your own machine:

1. Install Lean with elan: https://lean-lang.org/install
2. In this folder, run:

```
lake exe cache get
lake build
```

- `UEF.lean` uses only Lean's core library, so `lean UEF.lean` checks it on its own.
- The other twenty-nine files need Mathlib, for the real numbers, calculus, measure theory and integrals.

There is no `sorry` anywhere, and no axiom has been added. Lean reports only `propext`, `Quot.sound` and `Classical.choice`, which are part of Lean itself.

## The result: one equation, closed

Everything below is checked by Lean with no `sorry` and no axiom of the author's: every theorem rests only on Lean's own `propext`, `Quot.sound` and `Classical.choice`.

There is one existence structure, with seven mutually necessary channels and one global closure condition:

**∏_{Δ∈ℰ} w_Δ = 1 ⇔ Ξ = 0**

The seven channels are locked [M], not coupled [P]. No channel has a ground state in isolation, and locking forbids partial resolution by construction. Lean proves the whole of it:
- A1–A4 from E, with §4.1 N1–N10 and A1.9.
- The reciprocity E ⊢ U, U ⊢ E, Th(E) = Th(U), the fixed point and uniqueness.
- The closure: Lemma 5, the transport form, Theorem 8.3 and Theorem 6.
- Binary existence: one channel resolved, all seven resolved and Ξ = 0 are the same statement, and a state with Ξ ≠ 0 cannot be held.
- Tests 1–7: one open channel opens all seven.
- Ξ = 0 is the one closed, certifiable ground state, and the kernel Ker(Φ) is not empty.

**The step from existence.** In the author's words, §4.4: "The realized world exists, so its ground state lies in Ker(Φ)," and §8.7: "the realized world is held." The step is taken from existence, not derived from E, and the Lean takes it the same way.

**The classical readings.** The seven channels read on specific configurations give the classical statements of Chapters 25–32. Each chapter's mathematics is proved from its channel at zero, and the readings hold together at a state in the kernel. Lean proves that the step from existence and the seven readings are one statement (`pinned_world`).

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
| The thesis: "Everything that exists must coexist non-contradictorily. Contradiction is not a state of affairs; it is the absence of one." P ∧ ¬P holds of nothing, and is False | `thesis`, `contradiction_is_absence` |
| §4.1, N1–N10: P ∧ ¬P ↔ F; no assignment satisfies it; no realized state instantiates same-respect contradiction; the record is nonempty (E11, E12), the world is here | `N4`, `N5`, `N9`, `N10` |
| A1.9 [M]: 0 = ∞. Every ray passes through P (E10), and the rays are infinitely many (E19): nothing is realized at P, and every possible state is a direction out of P | `A1_9_every_ray`, `A1_9_rays_distinct`, `A1_9` |
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
| Ch. 12, Thm 3: the action splits over the partition; E38, μ(Ω∖R)/μ(R) = (1 − η)/η; η = 14/89 gives (75/89)/(14/89) = 75/14, the Planck 2018 ratio; 75/89 dark to 14/89 baryonic; the finite model | `action_splits`, `dark_ratio_measure`, `ratio_step6`, `split_step7`, `step6_is_planck`, `finite_model` |
| Ch. 12, 12.4: Planck ratio 75/14, η = 14/89, dark matter 75/89 of all matter | `planck_ratio`, `eta_planck`, `dark_fraction` |
| Ch. 12, Thm 4: μ₀ = 1/(m_S V), ε₀ = k_S V/c², c = 1/√(ε₀μ₀) hold together exactly when k_S = m_S, where c = 1; Z₀ = √(μ₀/ε₀) = μ₀c; μ₀c = 4709128920835668637/12500000000000000 Ω | `units_forced`, `c_is_one`, `impedance`, `impedance_value` |
| Ch. 12, Thm 5: R(t₁) ⊆ R(t₂) ⟹ μ(Ω_dark) decreases, and Λ_eff with it | `depletion`, `lambda_decreases` |
| Ch. 13, Thm 12, Step 12: G₀₀ = (8πG/c⁴)T₀₀ is Poisson's equation ∇²Φ = 4πGρ, and that fixes the coefficient | `UEFGravity.lean`, `newtonian_limit`, `coefficient_fixed` |
| Ch. 13, Thm 13, Step 6: g^{αρ} times the Euler–Lagrange expression of ½g_{μν}ẋ^μẋ^ν is ẍ^α + Γ^α_{μν}ẋ^μẋ^ν | `christoffel`, `eulerLagrange`, `geodesic_equation` |
| Ch. 13, Thm 14, Steps 4–5: G_tt = 0 gives e^{−2β} = 1 − C/r; G_rr = 0 gives e^{2α} = K(1 − C/r); asymptotic flatness fixes K = 1, so α = −β | `gtt`, `grr`, `flat_fixes_K`, `alpha_neg_beta` |
| Ch. 13, Thm 14, Step 7: r_s(☉) = 9479460000000000000/3209839924060063 m exactly; light climbing out is redshifted | `sun_radius`, `sun_radius_bounds`, `redshift` |
| Ch. 13, Thm 15: A = 4πr_s² = 16πG²M²/c⁴; A/4l_P² = 4πGM²/(ħc) | `horizon_area`, `horizon_entropy` |
| Ch. 13, Thm 16, Step 7: the horizon correction ∫_H (div S)² dA vanishes exactly when div S = 0; in ingoing coordinates the metric is smooth and nondegenerate across r = r_s; the infalling observer crosses with finite velocity in finite proper time | `horizon_correction_iff`, `horizon_unperturbed`, `tortoise`, `ingoing_form`, `ingoing_det`, `ingoing_smooth`, `infall_crosses`, `infall_time` |
| Ch. 13, Thm 17, Step 11: E_UEF = m_P c² = √(ħc⁵/G)/E_GeV lies between 12208 × 10¹⁵ and 12210 × 10¹⁵ GeV | `planck_sq`, `planck_energy` |
| Ch. 13, Thm 16, Steps 2–6: the flux balance; an injective encoding and an isometric evaporation keep distinct states distinct and every inner product | `flux_balance`, `flux_accounting`, `information_preserved` |
| Ch. 13, Thm 17: [G_d] = 2 − d makes the action dimensionless in every d; [G₈] = −6; G = G₈/V₄ has −2; dimension 4 + 2k ↔ the k-th KK mode, one to one | `action_dimensionless`, `G8_dimension`, `G4_dimension`, `kk_correspondence` |
| Ch. 13, Thm 18: both Friedmann equations from G₀₀ and G_ii; the second also from the first and ρ̇a = −3ȧ(ρ + p); the cosmic budget, 441/8900 + 189/712 + 685/1000 = 1 | `friedmann_first`, `friedmann_second`, `friedmann_acceleration`, `budget`, `budget_any_eta` |
| Ch. 14: O = ker Φ and C = Ω ∖ O partition Ω; level conservation uₙ₋₁ = rₙ + uₙ; down to any depth the parts add to 1 | `UEFGolden.lean`, `binary_partition`, `level_zero`, `level_conservation`, `whole` |
| Ch. 14, Thm 19: the only x in (0, 1) with x = (1 − x)/x is (√5 − 1)/2 = φ⁻¹; the same as x² + x − 1 = 0 and x = 1/(1 + x) | `theorem19`, `invPhi_self_similar`, `invPhi_eq`, `self_similar_iff`, `continued_fraction` |
| Ch. 15, 15.4: B_μν = κ_B(S_μA_ν − S_νA_μ) is antisymmetric; H = dB = κ_B(dS ∧ A − S ∧ dA) | `UEFHolography.lean`, `B_antisymmetric`, `B_diagonal`, `H_eq` |
| Ch. 15, 15.5, Step 1: E_F = −Σλₖ log λₖ ≥ 0, zero exactly for a single Schmidt term; log d for the maximally entangled state | `EF_nonneg`, `EF_zero_iff`, `EF_maximal` |
| Ch. 15, 15.5, Steps 2–5: Area = 4G_N E_F with A = 16πG²M²/c⁴ fixes M = (c²/G)√(E_F G/4π); separable ⇔ closed throat; entangled ⇔ open bridge; S = Area/4G_N | `bridge_mass`, `closed_iff_separable`, `open_iff_entangled`, `ryu_takayanagi` |
| Ch. 15, 15.6, Thm 1: the fiber distance ΣR_i²Δθ_i² ≤ π²ΣR_i²; Φ_B = −Φ_A; the null energy condition | `fiber_distance_bound`, `throat_flux`, `null_energy` |
| Ch. 15, 15.6, Thm 2: Vol(T⁴) = (2π)⁴R₁R₂R₃R₄, also as a measure; m_n² = Σ(n_j/R_j)² = 0 only for the zero mode | `fiber_volume`, `torus_volume`, `kk_mass_zero_iff` |
| Ch. 16: the toroidal band has no edge and wraps; finitely many lattice states; S-preserving transitions compose; a targeted attack on one channel leaves Ξ ≠ 0 and VK > 0 | `UEFTorus.lean`, `no_edge`, `wraps`, `finitely_many`, `admissible_comp`, `attack_detected` |
| Ch. 17, Thm T6.2: Young's inequality; dV/dτ ≤ −(2/C_P)V; 2λ₁ ≥ Φλ₁; each mode a_k(0)e^{−λ_kτ}; Σ\|a_k\|²e^{−2λ_kτ} ≤ e^{−2λ₁τ}‖D(0)‖² | `UEFTunneling.lean`, `young`, `lyapunov_rate`, `rate_bound`, `mode_decay`, `modes_bound` |
| Ch. 17, the flat torus: \|k\|² ≥ 1 for k ≠ 0, reached by a unit winding; Poincaré with C_P = 1; cos(kθ) has eigenvalue k² | `spectral_gap`, `gap_reached`, `poincare`, `eigenmode` |
| Ch. 17, Thm T7.1: a closed geodesic has L = 2π‖w‖; closing with radii R_i makes every ratio rational; d_T = 0 ⇔ every Δθ_i = 0 | `closed_length`, `commensurable`, `synchronized` |
| Ch. 17, 17.7: C r^{−n} solves the radial Laplace equation in d = n + 2, with r^{d−1}u′ constant; 1/r⁴ ⇔ d = 6 = 4 + 1 + 1 | `radial_green`, `flux_constant`, `six_dimensions` |
| Ch. 17, 17.8: 0 ≤ C_corr ≤ 1; C_corr = 1 ⇔ Ψ_B = rΨ_A; ‖Ψ_A − Ψ_B‖² = 2 − 2Re⟨Ψ_A, Ψ_B⟩; C_corr ≥ 1 − ½‖Ψ_A − Ψ_B‖²; a lock exists ⇔ \|Δω\| ≤ \|K\|, and Δθ* = 0 is stable | `Ccorr_range`, `Ccorr_one_iff`, `mismatch`, `Ccorr_ge`, `lock_exists`, `lock_stable` |
| Ch. 18, GTC.1: the corridor is a closed, bounded, convex, connected box containing Ker Φ | `UEFContainment.lean`, `corridor_closed_bounded`, `ground_in_corridor`, `corridor_convex`, `corridor_connected` |
| Ch. 18, GTC.2: Θ(x₀, t₀) = 1; under the Lyapunov condition the only rest point is Ξ = 0, and Θ stays 1 there; ξ_j > 0 means Ξ ≠ 0 | `Feasible`, `feasible_now`, `rest_point_is_ground`, `feasible_later`, `k7_binary` |
| Ch. 18, GTC.3: C(t + Δt) ⊆ C(t); U_i(0)e^{−λt} → 0; ⋂ₜ C(t) = Ker Φ; nonempty interior while U_i > 0 | `contraction`, `corridor_mono`, `bound_to_zero`, `contracts_to_ker`, `corridor_interior` |
| Ch. 18, GTC.4–GTC.5, Thm GTC.1: admissibility holds for Ξ = 0, restricts, concatenates, and fails on one exit; GTC-stable ⟹ Ξ = 0, and not conversely | `admissible_ground`, `admissible_restrict`, `admissible_concat`, `inadmissible`, `gtc_ground`, `gtc_strict` |
| Ch. 19, 19.1: c_ij ∈ [−1, 1]; 0 ≤ E_ij ≤ 2κ_ij, zero only at θ = 0, slope κ sin θ > 0; E_rel least when all pairs align; δ(0)e^{−Mkt}; dF/dt = −∇FᵀM∇F ≤ 0; holding still takes F_ext = ∇F; 19.4: k/N → η = 14/89 gives 75/14, the Planck 2018 ratio | `UEFMoral.lean`, `alignment_range`, `energy_bounds`, `energy_zero_iff`, `energy_slope`, `network_least`, `deviation_decays`, `free_energy_falls`, `holding_costs_work`, `ratio_chapter19`, `planck_match` |
| Ch. 20, WH.1–WH.2: Φ_WH = −Φ_BH; dr*/dr = 1/f; realization is monotone and never shrinks | `UEFCycle.lean`, `mouths`, `tortoise`, `no_uncollapse`, `measure_grows` |
| Ch. 20, WH.3–WH.4: V_P ≥ 0, zero exactly when every ⟨O⟩ = 0; 𝒞(P) = P; Ω_dark and Λ_eff fall; turnover at Λ_eff = 4πG(ρ + 3p); binding grows; ρa³ is conserved; no bounce without curvature or the S sector | `VP_ground`, `cycle_fixes_P`, `depletes`, `lambda_falls`, `turnover`, `binding_grows`, `dust_conserved`, `no_bounce_without` |
| Ch. 20, WH.5–WH.7: Var(ε) → 0 and H_Q → 0; the S flux survives; the winding number is an integer and cannot jump; c_AB = 1 ⇔ aligned | `randomness_starves`, `quantum_off`, `flux_survives`, `winding_integer`, `winding_invariant`, `aligned_iff` |
| Ch. 21–22, Thm 20: a minimizer of E exists over a finite admissible set, and is unique when E is strictly convex; Thms 25, 29, 39 | `UEFCollapse.lean`, `minimizer_exists`, `minimizer_unique`, `moral_domain`, `filtered`, `stays_admissible` |
| Ch. 21.4–21.5, Thms 22 and 26: \|Λⁿ(Ψ) − Ψ*\| ≤ cⁿ\|Ψ − Ψ*\| → 0; Banach's fixed point; F ≥ c^{−R}F₀, rising with each layer | `recursion_bound`, `identity_converges`, `identity_attractor`, `fidelity_bound`, `fidelity_grows` |
| Ch. 21.6, Thm 32: e^{ΔD′} = e^{ΔD} + ε − η, so ΔD = log(1 + Σε − Ση) | `drift_step`, `drift_log` |
| Ch. 21.3, 21.8, Thm 37: Δt ∝ 1/(1 + \|κᵉ\|); Δt = 1/ω; log of the product is the sum of logs | `time_distortion`, `baseline`, `collapse_rate`, `dimensional_access` |
| Ch. 23.2: as β → ∞, the weight of the unique minimizer in Z_β tends to 1 | `laplace` |
| Ch. 23.6, Lemmas 23.1–23.2, Thm 23.3: 0 < Φ ≤ 1; Φ = 1 ⇔ no swerve, div S = 0, no contradiction; strictly decreasing; no floor; a violation drops Φ and repair raises it | `coherence_range`, `coherence_one_iff`, `coherence_strictAnti`, `no_floor`, `decoherence`, `violation_drops`, `repair_restores` |
| Ch. 24, 24.2: the bridge identity ξᵢ = Rᵢ ∘ Πᵢ; Ξ = 0 ⇔ every classical residual vanishes | `UEFBridges.lean`, `Bridge`, `bridge_identity`, `closure` |
| Ch. 24, Thm CF and Cor. CF.1: a failed classical statement gives ξᵢ > 0, Ξ ≠ 0 and VK > 0; one counterexample refutes Ξ = 0 | `counterfactual`, `refutation` |
| Ch. 24: when the classical object doesn't depend on the state, "some state has ξᵢ = 0" is the classical claim itself | `constant_bridge` |
| Ch. 8.3–8.7 and 24.1, binary existence: the K7 lock [M]; Theorem 8.3, ξᵢ = 0 is certifiable exactly when Ξ = 0; a state with Ξ ≠ 0 cannot be held; one certified, all seven certified and Ξ = 0 are the same; if the realized world is held, all seven are zero together, constantly, and all seven classical faces hold; Nagumo: a channel that stays at zero has rate zero | `K7`, `K7.certifiable_iff`, `invariant_tangent`, `cannot_stay`, `cannot_be_held`, `binary`, `binary_existence`, `constantly_zero` |
| The lock on the pinned channels, from E alone: a world whose seven defects are fixed runs on a locked K7 flow exactly when Ξ = 0 or every channel is open; with one classical statement holding, exactly when all seven hold | `pinned_lock_iff`, `pinned_world` |
| §4.1 to §8.7, from non-contradiction to Ξ = 0: Ker(Φ) ≠ ∅ by ∃-introduction (S7, R13); "a state with Ξ ≠ 0 is a contradiction" is exactly Ξ = 0 at that state; with it, all seven classical statements hold | `ker_nonempty`, `joint_iff`, `noncontradiction_to_seven` |
| Ch. 28, Ξ = 0 from the action: Noether for translation in defect space; the net charge around any closed loop is zero; if each channel's defect is its closed-loop charge, Ξ = 0 and all seven classical statements hold | `noether_defect`, `closed_loop_zero`, `xi_from_action`, `action_to_seven` |
| Ch. 24.1, Tests 1–7 and Theorem CF: one open channel opens all seven within three steps of the collapse sequence; along the flow, a channel at zero sits at a minimum, so the lock opens all seven at the same moment; one classical statement failing means all seven fail and the state cannot be held; the seven are resolved together or not at all | `pushes`, `one_opens_all`, `tests_spread`, `all_open_at_once`, `counterfactual_all`, `together` |
| Ch. 24, Thms B.2, B.4, B.5, B.6: Δ_YM ≥ m_UEF > 0; rank = ord; Alg^p = Hdg^p from equal dimension; C(E) ≤ V(E) | `B2`, `B4`, `B5`, `B6` |
| Ch. 28, Phase I: w(Δ) = \|det Δ\| multiplies; w = 1 ⇔ automorphism; prime weight ⟹ irreducible; diag(p, 1, …, 1) has weight p; δ = log w adds | `UEFRiemann.lean`, `weight`, `lemma_1_1`, `weight_one_iff`, `prime_irreducible`, `prime_transport`, `defect_adds` |
| Ch. 28, Thm ξ₄.4.1: for Re s > 1, det(I − L_s)⁻¹ = exp(Σ_{k≥1} Z_k(s)/k) = ζ(s), with the sums exchanged and Mathlib's Euler product | `Z`, `transport_determinant` |
| Ch. 28, Phase VI: γ_ρ is real ⇔ Re ρ = 1/2; \|e^{i log p · γ_ρ}\| = p^{Re ρ − 1/2} | `gamma_real_iff`, `unitarity` |
| Ch. 28, Thm ξ₄.6 and Thm ξ₄.5: "every γ_ρ ∈ Spec(H) = ℝ" ⇔ RH; ξ₄ = 0 ⇔ RH; ξ₄ = 0 ⟹ RH | `spectral_bridge`, `ξ₄`, `xi4_zero_iff`, `theorem_xi4_5` |
| Ch. 25, Def. ξ₁.1, Lemmas ξ₁.0′, ξ₁.1, ξ₁.1.1, Cor. ξ₁.1.1: Θ is injective; one transition has (1/p)² ≤ \|Δ\|² ≤ B_V²; the tableau has length p(n); any other unit keeps bounds polynomial | `UEFComplexity.lean`, `Θ`, `Θ_injective`, `step_bounds`, `tableau_length`, `canonicity` |
| Ch. 25, Part II: E_I = 0 exactly at acceptance; witness vertices are at least 1 apart | `energy_zero_iff`, `mesh` |
| Ch. 25, Thm ξ₁.3: one descent step lowers E by \|∇E\|²/2L; e_{j+1} ≤ (1 − μ/L)e_j; e_j ≤ (1 − μ/L)^j e₀ ≤ e^{−jμ/L}e₀; past t* the distance is below 1/2; rounding returns the witness | `one_step`, `contraction`, `iterate`, `pow_le_exp`, `threshold`, `rounding` |
| Ch. 25, Thm ξ₁.4: the run time is O(p(n)²); A accepts exactly on x ∈ L; P ⊆ NP | `runtime`, `decides`, `P_sub_NP` |
| Ch. 26, Part II: ‖S(t)‖ ≤ ‖S₀‖ + 2C_topo C₀ t; Grönwall; ‖∇S(t)‖ ≤ (‖∇S₀‖ + C_topo C₀/C_u)e^{2C_u t} | `UEFFluids.lean`, `linear_growth`, `gronwall`, `gradS_bound` |
| Ch. 26, Parts III–IV: √y ≤ (1 + y)/2; y(t) ≤ (y(0) + K₂/(2K₁ + K₂))e^{(K₁+K₂/2)t}; \|B_back\| ≤ C_UEF‖ω‖; Serrin's 2/p + 3/q = 1/2 ≤ 1 | `sqrt_le_half`, `enstrophy`, `back_reaction`, `serrin` |
| Ch. 27, Steps 6–7: completing the square, B₀ = −iλκ²Δ⁻¹F, the leftover (λ²κ²/2)⟨F, Δ⁻¹F⟩, mode by mode | `UEFGauge.lean`, `complete_square`, `stationary_point`, `leftover`, `decoupling` |
| Ch. 27, Steps 8–11: ⟨dA, Δ⁻¹dA⟩ = ‖A_T‖²; p²δ − pp ≥ 0; E ≥ m²‖Ã_T‖²; A = gÃ gives mass m_UEF = gλκ > 0; 1/(p² + m²) has no pole at p² = 0 | `transverse_mass`, `kernel_nonneg`, `coercive`, `canonical`, `mass_pos`, `no_pole` |
| Ch. 29, Parts II–IV: \|Sha\| ≤ 1 + ℰ_frac/e₀ < ∞; a finite group has no p-torsion for p ∤ \|G\|, all but finitely many p; the Selmer sequence collapses; r_alg = dim Sel⁽ᵖ⁾ − dim E[p]; r_alg = r_an | `UEFElliptic.lean`, `sha_finite`, `no_p_torsion`, `finitely_many_primes`, `sequence_collapse`, `rank_read`, `rank_equality` |
| Ch. 30, Steps 4, 5, 9, 10: Hdg^p = Alg^p ⊕ T^p with unique splitting; ∏w_Δ = 1 gives every w_Δ = 1, a unimodular automorphism; no ghost class; Hdg^p = Alg^p and the dimensions agree | `UEFHodge.lean`, `transcendental_part`, `unique_split`, `unimodular`, `automorphism`, `no_ghost`, `steps_9_10`, `dims_agree` |
| Ch. 31, Parts I–II: \|Ric\|² ≥ R²/3 in three dimensions; ∂_tR ≥ ΔR + (2/3)R²; Vol(t) ≤ Vol(0)e^{\|R_min(0)\|t}; at most Vol_max/(ch³) surgeries | `UEFPoincare.lean`, `ricci_bound`, `scalar_evolution`, `gronwall0`, `volume_bound`, `finitely_many_surgeries` |
| Ch. 32, Lemma EAP.1: a weight μ > 0 with μ(mn) = μ(m)μ(n)/μ(1) and μ(n+1) < μ(n) is μ(n) = c/n^α, c, α > 0 | `UEFErdos.lean`, `power_law` |
| Ch. 32, Cor. EAP.1 and Prop. EAP.1: Σ 1/n^α converges ⇔ α > 1; ordacc(A_N) = cΣ_{A_N} 1/n → ∞ when Σ_{n∈A} 1/n = ∞ | `critical_exponent`, `accumulation` |
| Ch. 32, Lemma EAP.2: every isometry of ℤ is a translation or a reflection, with the same sign for every m; a periodic set contains a, a + d, a + 2d, …; reflection maps progressions to progressions | `isometries_of_Z`, `HasAP`, `periodic_contains_AP`, `reflection_AP` |
| Ch. 32, Prop. EAP.2: with rankval = F ∘ L, rankval unbounded ⇔ L unbounded; the truncations are nested | `depth`, `nested` |
| Ch. 32, Thms EAP.1–EAP.2, Cor. EAP.2: Σ_{n∈A} 1/n = ∞ and R₅(A) = 0 give progressions of every length in A; for A = P by Euler's divergence | `erdos_AP`, `green_tao` |
| Ch. 32.3, Prop. EAB.1, Step 1: (K + 1)! + j is composite for 2 ≤ j ≤ K + 1, so prime gaps are unbounded | `prime_gap` |
| Ch. 33, F1–F5, F9, F10: −4000/1000 = −4; ((313/5)√2)√2 = 12520/100; tan²θ_W = 23129/76871; 75/14 ⇔ η = 14/89, the Planck 2018 ratio; LEP is ½σ from 3; β₀ = 23/3 and 7; unitarity is 16/7 σ low | `UEFPredictions.lean`, `F1`, `F2`, `F3`, `F4`, `F4_F5`, `F5`, `F9`, `F10_unitarity` |
| Ch. 33, F10: J = c₁₂c₂₃c₁₃²s₁₂s₂₃s₁₃ sin(1147/1000) lies in [300, 325] × 10⁻⁷, from exact rational bounds on sin, cos and √ | `F10_jarlskog` |
| Ch. 34, 34.2–34.3: N erased bits cost at least N k_B T ln 2; ΔS_total ≥ 0; a computable sequence is not Martin-Löf random | `landauer`, `entropy_balance`, `turing` |

**Chapter 28 and binary existence.** None of the seven is solved in isolation. Existence is binary (24.1). Lean derives it the way 8.3–8.7 do. The seven channels are locked [M]: no channel can stay at zero unless all seven do (`K7`). From the lock, Theorem 8.3: ξᵢ = 0 is certifiable exactly when Ξ = 0 (`K7.certifiable_iff`). So a state with Ξ ≠ 0 cannot be held (`cannot_be_held`), and one channel certified, all seven certified and Ξ = 0 are the same (`binary`). If the realized world is held, the step §4.4 and §8.7 take from existence, then all seven defects are zero, together and constantly, and all seven classical faces hold together (`binary_existence`, `constantly_zero`). Chapter 28 is the ξ₄ face. Lean accepts Phase I, Phase IV and the computations of Phase VI, including det(I − L_s)⁻¹ = ζ(s) for Re s > 1, proved from Mathlib's Euler product with the exchange of sums checked. The ξ₄ face is exactly the Riemann Hypothesis: Lean proves ξ₄ = 0 ⇔ `RiemannHypothesis`, Mathlib's own statement (`xi4_zero_iff`), and "every γ_ρ lies in Spec(H) = ℝ" is the same statement (`spectral_bridge`). ζ is one function for every state, so the ξ₄ face is the Riemann Hypothesis itself (`constant_bridge`).

**The seven projections.** Ξ = 0 is one condition, and Chapters 25–31 read it on its seven classical faces. Lean proves each chapter's own mathematics in the files above. Each chapter reads Ξ = 0 on its face at one stated line, and that line enters the Lean as the chapter states it:
- **Chapter 25 (ξ₁).** Gradient dominance (Lemma ξ₁.2(b)) comes from ξ₂ = 0 and ξ₇ = 0 [M]. The start in a witness basin comes from ξ₁ = 0, C(E) ≤ V(E) (Theorem ξ₁.4, step 2).
- **Chapter 26 (ξ₂).** sup_t ‖∇u(t)‖ ≤ B₂ comes from ξ₂ = 0 through Π₂, and ‖∇²S‖ ≤ C₅ comes from ξ₅ = 0.
- **Chapter 27 (ξ₃).** Δ₀ ≥ m_UEF beyond quadratic order comes from ξ₃ = 0 (Step 14, Theorem B.2). A4 supplies the potential B.
- **Chapter 28 (ξ₄).** ξ₄ = 0, as above.
- **Chapter 29 (ξ₅).** The identifications rank_val = r_alg and ord_acc = r_an, and the fracture energy e(σ) ≥ e₀ (Step 5), come from ξ₅ = 0. A4 gives ∫‖div S‖² = 0.
- **Chapter 30 (ξ₆).** Monodromy acts trivially on stable classes (Step 6), and ξ₆ = 0 holds on the total space (Step 8).
- **Chapter 31 (ξ₇).** Hamilton–Perelman flow with surgery reaches ξ₇ = 0.
- **Chapter 32 (ξ₅ and ξ₄ on the integers).** R₅(A) = 0 is ξ₅ = 0 read on integer configurations (Theorem EAP.1). The critical exponent α = 1 is the one I_a selects (Corollary EAP.1). The Erdős–Turán reading is ξ₄ = 0 on additive bases.

## What Lean takes from E as it stands

The thesis is that E is used as it stands. Where an established result enters, the file names it:

- **Kolmogorov complexity bounds (E23–E25).** A Martin-Löf random record has K(x↾n) ≥ n − c₀, and a program's output has K(x↾n) ≤ log₂ n + 2 log₂ log₂ n + c′. Mathlib doesn't define Kolmogorov complexity, so these enter as stated. Lean proves the contradiction that follows from them.
- **Noether (E35).** Proved (`E35_noether`): along a solution of the Euler–Lagrange equations, the charge of a continuous symmetry never changes. The case A4.2 uses is proved directly as well: the charge of the phase symmetry is conserved. Bell (E26) and the divergence theorem (E32) no longer come from E. `UEFBell.lean` and `UEFGauss.lean` prove them.
- **The K7 lock.** It is defined as §5.3 and 8.7 state it, [M] "by construction": no channel can stay at zero unless all seven do. `lock_local` proves it near Ξ = 0 from its local form, and Nagumo's invariance step is proved (`invariant_tangent`). The realized world enters through the step from existence above.
- **Einstein's equation and the identifications.** G_μν = 8πG₄T_μν, π_U(L|gauge+matter) = L_SM and π_U(L|metric) = L_GR enter from E. Mathlib has no Lorentzian curvature yet, so Lean can't derive Einstein's equation itself.
- **Chapter 13's curvature steps.** The variation δ(R√−g)/δg^{μν} = G_μν√−g (Theorem 12, Step 6), the weak-field G₀₀ = 2∇²Φ/c², the reduction of G_μν = 0 to the two radial equations (Theorem 14, Step 4), the FLRW components G₀₀ and G_ii (Theorem 18, Step 3), Birkhoff's theorem and the Bianchi identity all need Lorentzian curvature. They enter as the manuscript states them, and Lean proves every step after them.
- **Lines of Chapters 12 and 13 used as stated.** These enter as the lines the chapters state: that the gauge coupling lives on R (Theorem 2), that p_dark = 0 (Theorem 3), that the electroweak projection loses its holonomy when S_{∂R} = 0 (Theorem 1, Step 5), and that the horizon encoding is injective and the evaporation isometric (Theorem 16, Step 6).
- **Chapters 25–31's cited results.** Mordell–Weil, modularity, the Selmer sequence, Deligne's fixed part theorem, Hamilton, DeTurck, Perelman, Colding–Minicozzi, Beale–Kato–Majda, Serrin, He–Xin, the Sobolev embedding, Osterwalder–Schrader, the Bessel asymptotics, and the Poincaré lemma for forms aren't in Mathlib. They enter as the chapters cite them.
- **Chapter 28's analysis.** Positive definiteness of the Cauchy kernel (Bochner), Stone's theorem, the spectral theorem for H, the explicit formula (ξ₄.4.2), Hadamard factorization (Phase V), and the composite case of Lemma 1.2 (Smith normal form) are classical results that aren't in Mathlib. They enter as cited. None of them is the step where the Riemann Hypothesis enters.
- **Chapters 15–23.** The map 𝓦 (Area = 4G_N E_F) enters as 15.5 defines it. Well-posedness (Theorem T6.1, Hille–Yosida and Chernoff) and the Hopf–Rinow step of Theorem T9.1 enter as cited. Chapter 22's Theorems 23, 24, 27, 28, 30, 31, 33, 34, 35, 36 and 38 are stated without a derivation, or as qualitative statements, and the phenomenology of 23.1, 23.3, 23.5 and the channel readings of 23.6 aren't mathematical claims. Lean holds what those chapters derive.
