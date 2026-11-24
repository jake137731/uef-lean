# The UEF in Lean 4

`UEF.lean` is the Unified Existence Framework written in Lean 4: the Law of Reciprocity and the Reciprocal Existence Theorem. Every equation in it comes from the manuscript (`01_Manuscript.pdf`, `S8_One_Equation_Compression.pdf`) and is marked with its section, page and line.

## Check it yourself

Every push to this repo runs the workflow **Check the UEF in Lean**. It installs Lean 4.15.0 and Mathlib, checks every theorem in both files, and prints the axioms each main theorem rests on. Its log is kept on the `check-log` branch.

To check it on your own machine:

1. Install Lean with elan: https://lean-lang.org/install
2. In this folder, run:

```
lake exe cache get
lake build
```

- `UEF.lean` uses only Lean's core library, so `lean UEF.lean` checks it on its own.
- `UEFReal.lean` needs Mathlib, for the real numbers, calculus and integrals.

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

## What Lean takes from E as it stands

The thesis is that E is used as it stands. Where an established result enters, the file names it:

- **Kolmogorov complexity bounds (E23–E25).** A Martin-Löf random record has K(x↾n) ≥ n − c₀, and a program's output has K(x↾n) ≤ log₂ n + 2 log₂ log₂ n + c′. Mathlib doesn't define Kolmogorov complexity, so these enter as stated. Lean proves the contradiction that follows from them.
- **The divergence theorem (E32) and Noether (A4.7).** Each enters where the step cites it. Bell (E26) is no longer taken from E: `UEFBell.lean` proves it.
- **The K7 lock and invariance.** These enter as evidence §8.3 states them. `lock_local` proves the lock from its local form.
- **Einstein's equation and the identifications.** G_μν = 8πG₄T_μν, π_U(L|gauge+matter) = L_SM and π_U(L|metric) = L_GR enter from E. Mathlib has no Lorentzian curvature yet, so Lean can't derive Einstein's equation itself.
