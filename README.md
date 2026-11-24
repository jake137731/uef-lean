# The UEF in Lean 4

`UEF.lean` is the Unified Existence Framework written in Lean 4: the Law of Reciprocity and the Reciprocal Existence Theorem. Every equation in it comes from the manuscript (`01_Manuscript.pdf`, `S8_One_Equation_Compression.pdf`) and is marked with its section, page and line.

## Check it yourself

1. Install Lean with elan: https://lean-lang.org/install
2. In this folder, run:

```
lean UEF.lean
```

If nothing prints, every theorem was checked. The `lean-toolchain` file pins Lean 4.15.0.

The file uses only Lean's core library. There is no Mathlib, no `sorry`, and no axiom added. Lean's own `#print axioms` lists `propext`, `Quot.sound` and `Classical.choice` for `the_one_equation`. Those three are part of Lean itself, and every Lean proof uses them. All arithmetic is exact integers. There is no floating point.

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

## What Lean takes from E as it stands

The manuscript's thesis is that E is used as it stands. In Lean, these come in the same way: as what E establishes, stated where they enter.

- **The steps of the spine.** A1 is proved from E. A2, A3 and A4 are each derived from E together with the line before. The physics of those derivations (Noether, symmetry, continuity) is in E. Lean checks that the chain is derived from E. It does not re-derive the physics, because the physics isn't formalized in Lean.
- **The lock and invariance.** The lock (Gᵢ ≠ 0 on a face with another channel open) and Nagumo's tangency rule enter as stated in evidence §8.3. `lock_local` proves the lock from its local form: linear part at least c·|Ξ|, remainder at most K·|Ξ|², 0 < |Ξ| < c/K.
- **Lines that need real numbers and calculus.** Lean's core library has neither. These lines are not written in this file:
  - S_UEF = ∫ L dV
  - dV/dt = 2ΞᵀG
  - V(t) ≤ V(t₀)e^{−γ(t−t₀)}
  - δ_Δ = log w_Δ
  - the zero-mode reduction, G₄ = G₈/Vol(T⁴), G_μν = 8πG₄T_μν

  Writing them needs Mathlib's real analysis.
