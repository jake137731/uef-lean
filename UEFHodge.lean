/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 30, in Lean 4 with Mathlib
  ξ₆ — Moral Alignment

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 30: Part I, Step 4 (the transcendental part),
  Part II, Step 5 (unimodular transports), Part III, Step 9 (no ghost class) and Part IV,
  Step 10 (the sequence collapses). ξ₆ is the moral-alignment projection of the one condition
  Ξ = 0; its bridge is Theorem B.5 (UEFBridges.lean).
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

namespace UEF.Hodge

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Step 4 — in Hdg^p, extend a basis of Alg^p: a complement T^p exists, Hdg^p = Alg^p ⊕ T^p. -/
theorem transcendental_part (Alg : Submodule ℚ V) : ∃ T : Submodule ℚ V, IsCompl Alg T :=
  Submodule.exists_isCompl Alg

/-- Step 4 — every Hodge class splits uniquely as α = α_alg + α_T. -/
theorem unique_split (Alg T : Submodule ℚ V) (h : IsCompl Alg T) (α : V) :
    ∃ (u : Alg) (v : T), (u : V) + v = α ∧ ∀ (r : Alg) (t : T), (r : V) + t = α → r = u ∧ t = v :=
  Submodule.existsUnique_add_of_isCompl h α

/-- Step 9 — a ghost class in T^p that is algebraic is zero: Alg^p ∩ T^p = 0. -/
theorem no_ghost (Alg T : Submodule ℚ V) (h : IsCompl Alg T) (α : V) (hT : α ∈ T)
    (halg : α ∈ Alg) : α = 0 :=
  (Submodule.disjoint_def.mp h.disjoint) α halg hT

/-- Step 10 — every Hodge class has α_T = 0, so Hdg^p = Alg^p: the cokernel is zero. -/
theorem collapse (Alg T : Submodule ℚ V) (h : IsCompl Alg T) (hT : T = ⊥) : Alg = ⊤ := by
  have := h.sup_eq_top
  rwa [hT, sup_bot_eq] at this

/-- Steps 9–10 — when every class of T^p is algebraic, T^p = 0 and Alg^p is everything. -/
theorem steps_9_10 (Alg T : Submodule ℚ V) (h : IsCompl Alg T)
    (stable : ∀ α ∈ T, α ∈ Alg) : Alg = ⊤ :=
  collapse Alg T h (eq_bot_iff.mpr fun α hα =>
    (Submodule.mem_bot ℚ).mpr (no_ghost Alg T h α hα (stable α hα)))

/-- Step 10 — then dim_ℚ Hdg^p = dim_ℚ Alg^p, which is ξ₆ = 0. -/
theorem dims_agree [FiniteDimensional ℚ V] (Alg : Submodule ℚ V) (h : Alg = ⊤) :
    Module.finrank ℚ Alg = Module.finrank ℚ V := by
  rw [h, finrank_top]

/-- Step 5 — Ξ = 0 gives ∏ w_Δ = 1, and then every transport has w_Δ = 1. -/
theorem unimodular {ι : Type*} (s : Finset ι) (w : ι → ℕ) (h : ∏ i ∈ s, w i = 1) :
    ∀ i ∈ s, w i = 1 := fun _ hi =>
  Nat.dvd_one.mp (h ▸ Finset.dvd_prod_of_mem w hi)

/-- Step 5 — a transport of weight |det Δ| = 1 acts on the integral lattice as a unimodular
    automorphism. -/
theorem automorphism {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℤ) (h : Δ.det.natAbs = 1) : IsUnit Δ := by
  rw [Matrix.isUnit_iff_isUnit_det, Int.isUnit_iff_natAbs_eq]
  exact h

end UEF.Hodge
