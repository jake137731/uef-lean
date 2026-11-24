/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 24, in Lean 4 with Mathlib
  Binary Existence: Counterfactual Tests and Bridge Theorems

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 24: 24.1 (Theorem CF, Corollary CF.1),
  24.2 (the bridge identity ξᵢ = Rᵢ ∘ Πᵢ, Theorems B.2, B.4, B.5, B.6) and 24.3.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

namespace UEF.Bridges

/-! ## 24.2 — the shape of every bridge -/

/-- A bridge for one channel: a map Π from states to classical objects, and a classical residual
    R ≥ 0 that vanishes exactly when the classical claim holds. -/
structure Bridge (State C : Type*) where
  proj : State → C
  R : C → ℝ
  claim : C → Prop
  R_nonneg : ∀ c, 0 ≤ R c
  R_zero_iff : ∀ c, R c = 0 ↔ claim c

variable {State : Type*}

/-- The bridge identity ξᵢ = Rᵢ ∘ Πᵢ. -/
def Bridge.ξ {C : Type*} (b : Bridge State C) : State → ℝ := b.R ∘ b.proj

/-- ξᵢ = 0 at a state is the classical claim for that state's classical object. -/
theorem bridge_identity {C : Type*} (b : Bridge State C) (s : State) :
    b.ξ s = 0 ↔ b.claim (b.proj s) :=
  b.R_zero_iff _

/-- The seven channels, each with its own classical objects. -/
def Ξ {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) : Fin 7 → ℝ :=
  fun i => (bs i).ξ s

/-- 24.2 and 24.3 — Ξ = 0 ⟺ every ξᵢ = 0 ⟺ every classical residual vanishes. -/
theorem closure {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) :
    Ξ bs s = 0 ↔ ∀ i, (bs i).claim ((bs i).proj s) := by
  constructor
  · intro h i
    exact (bridge_identity (bs i) s).mp (congrFun h i)
  · intro h
    funext i
    exact (bridge_identity (bs i) s).mpr (h i)

/-! ## 24.1 — counterfactual propagation -/

/-- Theorem CF, Steps 1–2 and 5 — if the classical statement of channel i fails, then ξᵢ > 0,
    Ξ ≠ 0, and VK = ΞᵀΞ > 0: the state is not the ground state. -/
theorem counterfactual {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) (i : Fin 7)
    (fails : ¬(bs i).claim ((bs i).proj s)) :
    0 < (bs i).ξ s ∧ Ξ bs s ≠ 0 ∧ 0 < ∑ j, Ξ bs s j ^ 2 := by
  have hne : (bs i).ξ s ≠ 0 := fun h => fails ((bridge_identity (bs i) s).mp h)
  have hpos : 0 < (bs i).ξ s := lt_of_le_of_ne ((bs i).R_nonneg _) (Ne.symm hne)
  refine ⟨hpos, fun h => hne (congrFun h i), ?_⟩
  calc (0 : ℝ) < Ξ bs s i ^ 2 := by
        show 0 < (bs i).ξ s ^ 2
        positivity
    _ ≤ ∑ j, Ξ bs s j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (Ξ bs s j)) (Finset.mem_univ i)

/-- Corollary CF.1 — one counterexample in any channel and no state has Ξ = 0. -/
theorem refutation {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State)
    (h : ∃ i, ¬(bs i).claim ((bs i).proj s)) : Ξ bs s ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact (counterfactual bs s i hi).2.1

/-- When a channel's classical object does not depend on the state (ζ(s) is one function, the set
    of NP languages is one set), "some state has ξᵢ = 0" is the classical claim itself, nothing
    more and nothing less. -/
theorem constant_bridge {C : Type*} [Nonempty State] (b : Bridge State C) (c : C)
    (hc : ∀ s, b.proj s = c) : (∃ s, b.ξ s = 0) ↔ b.claim c := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← hc s]
    exact (bridge_identity b s).mp hs
  · intro h
    obtain ⟨s⟩ := ‹Nonempty State›
    exact ⟨s, (bridge_identity b s).mpr (by rw [hc s]; exact h)⟩

/-! ## 24.2 — the bridge theorems whose last step is algebra -/

/-- Theorem B.2 — ξ₃ = max(0, m_UEF − Δ_YM) = 0 with m_UEF = gλκ > 0 gives Δ_YM ≥ m_UEF > 0. -/
theorem B2 (g lam κ ΔYM : ℝ) (hg : 0 < g) (hl : 0 < lam) (hk : 0 < κ)
    (h : max 0 (g * lam * κ - ΔYM) = 0) : g * lam * κ ≤ ΔYM ∧ 0 < ΔYM := by
  have h1 : g * lam * κ - ΔYM ≤ 0 := by
    have := le_max_right 0 (g * lam * κ - ΔYM)
    rw [h] at this
    exact this
  have h2 : 0 < g * lam * κ := by positivity
  constructor <;> linarith

/-- Theorem B.4 — with ∫‖div S‖² = 0 (A4), ξ₅ = |rank_val − ord_acc| = 0 says the rank equals the
    order of vanishing. -/
theorem B4 (rank ord : ℕ) (divS : ℝ) (hA4 : divS = 0)
    (h : |(rank : ℝ) - ord| + divS = 0) : rank = ord := by
  rw [hA4, add_zero, abs_eq_zero, sub_eq_zero] at h
  exact_mod_cast h

/-- Theorem B.5 — Alg^p ⊆ Hdg^p in a finite-dimensional ℚ-space; ξ₆ = 0 is the equality of
    dimensions, and then Alg^p = Hdg^p: every rational Hodge class is algebraic. -/
theorem B5 {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Alg Hdg : Submodule ℚ V) (hle : Alg ≤ Hdg)
    (hdim : Module.finrank ℚ Alg = Module.finrank ℚ Hdg) : Alg = Hdg :=
  Submodule.eq_of_le_of_finrank_eq hle hdim

/-- Theorem B.6, opening of Chapter 25 — ξ₁(E) = max(0, C(E) − V(E)) = 0 gives
    C(E) ≤ V(E): constructing costs no more than verifying. -/
theorem B6 (C V : ℝ) (h : max 0 (C - V) = 0) : C ≤ V := by
  have := le_max_right 0 (C - V)
  rw [h] at this
  linarith

/-! ## One condition, seven faces — none in isolation -/

/-- The Global Closure Theorem (8.4) with the seven bridges: when certifying any one channel is
    certifying Ξ = 0 (the K7 lock, Solve(i) ⇔ Solve(all) [M]), certifying channel i is
    certifying all seven classical statements together. No channel is solved alone. -/
theorem not_in_isolation {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i))
    (Certified : Fin 7 → State → Prop) (lock : ∀ i s, Certified i s ↔ Ξ bs s = 0)
    (i : Fin 7) (s : State) :
    Certified i s ↔ ∀ j, (bs j).claim ((bs j).proj s) :=
  (lock i s).trans (closure bs s)

/-- The seven stand or fall together: at the realized ground state Ξ = 0 all seven classical
    statements hold at once; a counterexample to any one of them, and Ξ ≠ 0 with no channel
    certifiable. -/
theorem the_seven {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i))
    (Certified : Fin 7 → State → Prop) (lock : ∀ i s, Certified i s ↔ Ξ bs s = 0)
    (s : State) :
    (Ξ bs s = 0 → ∀ j, (bs j).claim ((bs j).proj s)) ∧
      ((∃ j, ¬(bs j).claim ((bs j).proj s)) → Ξ bs s ≠ 0 ∧ ∀ i, ¬Certified i s) := by
  refine ⟨(closure bs s).mp, fun h => ⟨refutation bs s h, fun i hc => ?_⟩⟩
  exact refutation bs s h ((lock i s).mp hc)

end UEF.Bridges
