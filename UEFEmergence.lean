/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 9, the Theorem of Temporal Emergence, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, evidence Chapter 9: time as a discrete
  sequence of perception events, T = {π₁, π₂, π₃, …}.
-/
import Mathlib

open MeasureTheory

namespace UEF.Emergence

/-! ## 9.2 — Time as a discrete sequence of perception events -/

/-- Each perception event is one application of the CIO, K(Ψₙ) = argmin_B E(B):
    among finitely many branches, one with the least energy is chosen. A finite,
    non-empty set of branches always has one. -/
theorem collapse_exists {β : Type*} (branches : Finset β) (hne : branches.Nonempty) (E : β → ℝ) :
    ∃ B ∈ branches, ∀ B' ∈ branches, E B ≤ E B' :=
  branches.exists_min_image E hne

/-- R(t+1) = R(t) ∪ {newly perceived state}. -/
def record {X : Type*} (R₀ : Set X) (r : ℕ → X) : ℕ → Set X
  | 0 => R₀
  | n + 1 => record R₀ r n ∪ {r (n + 1)}

/-- Since Rₙ₊₁ = Rₙ ∪ {rₙ₊₁}, the realized sets grow by inclusion: Rₘ ⊆ Rₙ for m < n. -/
theorem record_grows {X : Type*} (R₀ : Set X) (r : ℕ → X) {m n : ℕ} (h : m ≤ n) :
    record R₀ r m ⊆ record R₀ r n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans Set.subset_union_left

/-- Ordering events by their index, πᵢ ≺ πⱼ exactly when i < j. -/
def Precedes (i j : ℕ) : Prop := i < j

/-- (T, ≺) is a strict total order: irreflexive, transitive and total. -/
theorem strict_total_order :
    (∀ i, ¬ Precedes i i) ∧ (∀ i j k, Precedes i j → Precedes j k → Precedes i k) ∧
    (∀ i j, Precedes i j ∨ i = j ∨ Precedes j i) :=
  ⟨fun i => lt_irrefl i, fun _ _ _ => lt_trans, fun i j => lt_trichotomy i j⟩

/-- Before the first event the index set is empty: time comes after differentiation and
    realization, not before. -/
theorem before_the_first : IsEmpty (Fin 0) := inferInstance

/-- Continuous time represents the same order by any strictly increasing labels tₙ,
    n < m ⇒ tₙ < tₘ; the map n ↦ tₙ preserves the order, so the continuum adds no new
    causal structure. -/
theorem labels_preserve_order (t : ℕ → ℝ) (ht : StrictMono t) (i j : ℕ) :
    Precedes i j ↔ t i < t j :=
  ht.lt_iff_lt.symm

/-! ## 9.4 — Lagrangian proof of temporal dependence -/

/-- H_QC = ∫ S(x) · ⟨ψ|O|ψ⟩ dV. -/
noncomputable def H_QC {M : Type*} [MeasurableSpace M] (dV : Measure M) (S reading : M → ℝ) : ℝ :=
  ∫ x, S x * reading x ∂dV

/-- If the consciousness subspace C is removed, H_QC = 0. -/
theorem H_QC_without_C {M : Type*} [MeasurableSpace M] (dV : Measure M) (reading : M → ℝ) :
    H_QC dV (fun _ => 0) reading = 0 := by
  simp [H_QC]

end UEF.Emergence
