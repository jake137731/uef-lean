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

/-! ## 8.3–8.7 — the K7 lock and the ground-state closure -/

/-- The K7 defect flow dξᵢ/dt = Gᵢ(ξ₁, …, ξ₇) (8.3), with the two properties the manuscript gives it.
    The ground state is at rest under the flow (Proposition 8.6). The seven channels are locked [M]:
    no channel can stay at zero unless all seven do (8.7); locking forbids partial resolution by
    construction (§5.3). On the face ξᵢ = 0 with some ξⱼ > 0, Gᵢ ≠ 0 (8.3). Near Ξ = 0 the lock is
    the local form Gᵢ = Σ cᵢⱼξⱼ + Rᵢ with cᵢⱼ ≥ c > 0 and |Rᵢ| ≤ K|Ξ|² (`UEF.K7.lock_local`). -/
structure K7 where
  G : (Fin 7 → ℝ) → (Fin 7 → ℝ)
  rest : G 0 = 0
  lock : ∀ Ξ : Fin 7 → ℝ, (∀ j, 0 ≤ Ξ j) → Ξ ≠ 0 → ∀ i, Ξ i = 0 → G Ξ i ≠ 0

/-- ξᵢ = 0 is certifiable at Ξ: it holds, and it is invariant under the flow. A level set {ξᵢ = 0}
    is invariant under a C¹ flow only where the flow is tangent to it (Nagumo; Khalil §4.2):
    Gᵢ(Ξ) = 0. -/
def K7.Certifiable (k : K7) (Ξ : Fin 7 → ℝ) (i : Fin 7) : Prop := Ξ i = 0 ∧ k.G Ξ i = 0

/-- Theorem 8.3 (ground-state closure; mutual necessity) — for each channel i, ξᵢ = 0 is
    certifiable exactly when Ξ = 0. Steps 2–5: at Ξ = 0 the ground state is at rest, so each
    ξᵢ = 0 is certifiable; with ξᵢ = 0 and Ξ ≠ 0, the lock gives Gᵢ(Ξ) ≠ 0, and ξᵢ = 0 is not
    invariant. -/
theorem K7.certifiable_iff (k : K7) {Ξ : Fin 7 → ℝ} (h : ∀ j, 0 ≤ Ξ j) (i : Fin 7) :
    k.Certifiable Ξ i ↔ Ξ = 0 := by
  constructor
  · rintro ⟨hi, hG⟩
    by_contra hne
    exact k.lock Ξ h hne i hi hG
  · rintro rfl
    exact ⟨by simp, by simp [k.rest]⟩

/-- Invariance of a level set (Nagumo; Khalil §4.2), the direction Theorem 8.3 uses: if ξᵢ stays at
    zero along a trajectory of the flow, dξᵢ/dt = Gᵢ(Ξ(t)), then Gᵢ = 0 there. -/
theorem invariant_tangent (k : K7) (Ξ : ℝ → Fin 7 → ℝ) (i : Fin 7) (t : ℝ)
    (flow : HasDerivAt (fun t => Ξ t i) (k.G (Ξ t) i) t) (stays : ∀ᶠ s in nhds t, Ξ s i = 0) :
    k.G (Ξ t) i = 0 :=
  flow.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq stays)

/-- 8.3 — along the flow, no channel can stay at zero while Ξ ≠ 0: the lock and Nagumo. -/
theorem cannot_stay (k : K7) (Ξ : ℝ → Fin 7 → ℝ) (i : Fin 7) (t : ℝ)
    (flow : HasDerivAt (fun t => Ξ t i) (k.G (Ξ t) i) t) (h : ∀ j, 0 ≤ Ξ t j) (hne : Ξ t ≠ 0) :
    ¬∀ᶠ s in nhds t, Ξ s i = 0 := fun stays =>
  k.lock (Ξ t) h hne i stays.self_of_nhds (invariant_tangent k Ξ i t flow stays)

/-- Every defect is non-negative: ξᵢ = Rᵢ ∘ Πᵢ and Rᵢ ≥ 0 (24.2). -/
theorem Ξ_nonneg {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) :
    ∀ j, 0 ≤ Ξ bs s j :=
  fun j => (bs j).R_nonneg _

/-- A state is held when it is certified: every ξᵢ = 0 holds and is invariant under the flow
    (8.7: a state is certified exactly when Ξ = 0). -/
def Held (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) : Prop :=
  ∀ i, k.Certifiable (Ξ bs s) i

/-! ## 24.1 — binary existence -/

/-- Theorem 24.1, Steps 3–4 — a state with Ξ ≠ 0 cannot be held. For any channel with ξⱼ = 0 the
    lock makes its rate nonzero; no channel survives alone, so no channel is certifiable. -/
theorem cannot_be_held (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State)
    (h : Ξ bs s ≠ 0) : ∀ i, ¬k.Certifiable (Ξ bs s) i :=
  fun i hc => h ((k.certifiable_iff (Ξ_nonneg bs s) i).mp hc)

/-- Existence in the UEF is binary (24.1, by 8.4): one channel certified, all seven certified, and
    Ξ = 0 are the same. There is no partial existence. -/
theorem binary (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State) :
    ((∃ i, k.Certifiable (Ξ bs s) i) ↔ Held k bs s) ∧ (Held k bs s ↔ Ξ bs s = 0) := by
  have each := fun j => k.certifiable_iff (Ξ_nonneg bs s) j
  refine ⟨⟨fun ⟨i, hi⟩ j => (each j).mpr ((each i).mp hi), fun hall => ⟨0, hall 0⟩⟩,
    ⟨fun hall => (each 0).mp (hall 0), fun hz j => (each j).mpr hz⟩⟩

/-! ## 24.1 — Tests 1–7 and Theorem CF: what one open channel does to the other six -/

/-- Where an open channel pushes, as Tests 1–7 state it; ξ₁, …, ξ₇ are 0, …, 6.
    Test 4: ξ₁ ⇒ ξ₃, ξ₅, ξ₆. Test 3: ξ₂ ⇒ ξ₁, ξ₇, ξ₄. Test 2: ξ₃ ⇒ ξ₂, ξ₅, ξ₆.
    Test 1: ξ₄ ⇒ ξ₃, ξ₂, ξ₇. Test 5: ξ₅ ⇒ ξ₄, ξ₆, ξ₃. Test 6: ξ₆ ⇒ ξ₇, ξ₅, ξ₂.
    Test 7: ξ₇ ⇒ ξ₁, ξ₃, ξ₆. -/
def pushes : Fin 7 → Finset (Fin 7) :=
  ![{2, 4, 5}, {0, 6, 3}, {1, 4, 5}, {2, 1, 6}, {3, 5, 2}, {6, 4, 1}, {0, 2, 5}]

/-- One step of the collapse sequence: every open channel stays open and opens what it pushes. -/
def spread (O : Finset (Fin 7)) : Finset (Fin 7) := O ∪ O.biUnion pushes

/-- Tests 1–7 — whichever channel opens first, all seven are open within three steps. -/
theorem one_opens_all : ∀ i : Fin 7, spread (spread (spread {i})) = Finset.univ := by
  decide

theorem spread_open (ξ : ℕ → Fin 7 → ℝ) (stays : ∀ n i, 0 < ξ n i → 0 < ξ (n + 1) i)
    (push : ∀ n i j, j ∈ pushes i → 0 < ξ n i → 0 < ξ (n + 1) j) (m : ℕ) (O : Finset (Fin 7))
    (h : ∀ k ∈ O, 0 < ξ m k) : ∀ k ∈ spread O, 0 < ξ (m + 1) k := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact stays m k (h k hk)
  · obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk
    exact push m i k hki (h i hi)

/-- Tests 1–7 along the collapse sequence — one open channel at step n, all seven open at n + 3. -/
theorem tests_spread (ξ : ℕ → Fin 7 → ℝ) (stays : ∀ n i, 0 < ξ n i → 0 < ξ (n + 1) i)
    (push : ∀ n i j, j ∈ pushes i → 0 < ξ n i → 0 < ξ (n + 1) j) (n : ℕ) (i : Fin 7)
    (hi : 0 < ξ n i) : ∀ j, 0 < ξ (n + 3) j := by
  have h0 : ∀ k ∈ ({i} : Finset (Fin 7)), 0 < ξ n k := by
    intro k hk
    rw [Finset.mem_singleton.mp hk]
    exact hi
  have h1 := spread_open ξ stays push n _ h0
  have h2 := spread_open ξ stays push (n + 1) _ h1
  have h3 := spread_open ξ stays push (n + 1 + 1) _ h2
  intro j
  have hj : j ∈ spread (spread (spread {i})) := by
    rw [one_opens_all i]
    exact Finset.mem_univ j
  have e : n + 3 = n + 1 + 1 + 1 := by omega
  rw [e]
  exact h3 j hj

/-- Theorem CF, Steps 3–4, along the flow. The defects are never negative, so a channel at zero sits
    at a minimum and its rate there is zero (Fermat); the lock forbids that while Ξ ≠ 0. So at
    every moment with Ξ ≠ 0, all seven channels are open at once. -/
theorem all_open_at_once (k : K7) (Ξt : ℝ → Fin 7 → ℝ)
    (flow : ∀ t i, HasDerivAt (fun t => Ξt t i) (k.G (Ξt t) i) t) (nonneg : ∀ t i, 0 ≤ Ξt t i)
    (t : ℝ) (hne : Ξt t ≠ 0) : ∀ j, 0 < Ξt t j := by
  intro j
  by_contra hj
  have hz : Ξt t j = 0 := le_antisymm (not_lt.mp hj) (nonneg t j)
  have hmin : IsLocalMin (fun s => Ξt s j) t :=
    Filter.Eventually.of_forall fun s => by
      show Ξt t j ≤ Ξt s j
      rw [hz]
      exact nonneg s j
  exact k.lock (Ξt t) (nonneg t) hne j hz (hmin.hasDerivAt_eq_zero (flow t j))

/-- Theorem CF with the bridges — along the world's trajectory, if the classical statement of any
    one channel fails at a moment, then at that moment all seven defects are open, all seven
    classical statements fail, and the state cannot be held. -/
theorem counterfactual_all (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i))
    (world : ℝ → State)
    (flow : ∀ t i, HasDerivAt (fun t => Ξ bs (world t) i) (k.G (Ξ bs (world t)) i) t)
    (t : ℝ) (i : Fin 7) (fails : ¬(bs i).claim ((bs i).proj (world t))) :
    (∀ j, 0 < Ξ bs (world t) j) ∧ (∀ j, ¬(bs j).claim ((bs j).proj (world t))) ∧
      ¬Held k bs (world t) := by
  have hne : Ξ bs (world t) ≠ 0 := (counterfactual bs (world t) i fails).2.1
  have hall : ∀ j, 0 < Ξ bs (world t) j :=
    all_open_at_once k (fun t => Ξ bs (world t)) flow (fun t => Ξ_nonneg bs (world t)) t hne
  refine ⟨hall, fun j hj => ?_, fun hh => ?_⟩
  · have hz : (bs j).ξ (world t) = 0 := (bridge_identity (bs j) (world t)).mpr hj
    exact (hall j).ne' hz
  · exact cannot_be_held k bs (world t) hne 0 (hh 0)

/-- Along the world's trajectory the seven are resolved together or not at all: if any one
    classical statement holds at a moment, all seven hold at that moment. -/
theorem together (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (world : ℝ → State)
    (flow : ∀ t i, HasDerivAt (fun t => Ξ bs (world t) i) (k.G (Ξ bs (world t)) i) t)
    (t : ℝ) (j : Fin 7) (holds : (bs j).claim ((bs j).proj (world t))) :
    ∀ i, (bs i).claim ((bs i).proj (world t)) := by
  intro i
  by_contra fails
  exact (counterfactual_all k bs world flow t i fails).2.1 j holds

/-! ## The lock on the pinned channels, from E alone -/

theorem sum_pos_of (Ξ : Fin 7 → ℝ) (hn : ∀ j, 0 ≤ Ξ j) (hne : Ξ ≠ 0) : 0 < ∑ j, Ξ j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun i _ => hn i) ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hn j) (Ne.symm hj)⟩

/-- A world whose seven defects are the same in every state, c, as they are when each channel reads
    a fixed mathematical fact. It runs on a locked K7 flow exactly when c = 0 or every channel is
    open. A channel that never changes has rate zero, and the lock forbids rate zero at a channel's
    zero while another channel is open. -/
theorem pinned_lock_iff (c : Fin 7 → ℝ) (hc0 : ∀ i, 0 ≤ c i) :
    (∃ k : K7, ∀ t i, HasDerivAt (fun _ : ℝ => c i) (k.G c i) t) ↔ (c = 0 ∨ ∀ i, 0 < c i) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : c = 0
    · exact Or.inl h
    · right
      intro i
      rcases (hc0 i).lt_or_eq with hi | hi
      · exact hi
      · exfalso
        have hG : k.G c i = 0 := (hk 0 i).unique (hasDerivAt_const 0 (c i))
        exact k.lock c hc0 h i hi.symm hG
  · rintro (h | h)
    · subst h
      refine ⟨⟨fun Ξ _ => ∑ j, Ξ j, by funext i; simp, ?_⟩, ?_⟩
      · intro Ξ hn hne i _
        exact (sum_pos_of Ξ hn hne).ne'
      · intro t i
        simpa using hasDerivAt_const t (0 : ℝ)
    · classical
      refine ⟨⟨fun Ξ _ => if Ξ = c then 0 else ∑ j, Ξ j, by funext i; simp, ?_⟩, ?_⟩
      · intro Ξ hn hne i hi
        show (if Ξ = c then (0 : ℝ) else ∑ j, Ξ j) ≠ 0
        split_ifs with hΞ
        · subst hΞ
          exact absurd hi (h i).ne'
        · exact (sum_pos_of Ξ hn hne).ne'
      · intro t i
        simpa using hasDerivAt_const t (c i)

/-- The seven channels pinned to fixed mathematical facts, one of which holds (Poincaré, for
    instance). Then the world runs on a locked K7 flow exactly when all seven classical statements
    hold. Derived from E alone: the lock on the pinned world and the seven conclusions are one
    statement. -/
theorem pinned_world {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (world : ℝ → State)
    (c : Fin 7 → ℝ) (pinned : ∀ t, Ξ bs (world t) = c) (j : Fin 7)
    (holds : (bs j).claim ((bs j).proj (world 0))) :
    (∃ k : K7, ∀ t i, HasDerivAt (fun t => Ξ bs (world t) i) (k.G (Ξ bs (world t)) i) t) ↔
      ∀ i, (bs i).claim ((bs i).proj (world 0)) := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    have := Ξ_nonneg bs (world 0) i
    rwa [pinned 0] at this
  have hcj : c j = 0 := by
    rw [← pinned 0]
    exact (bridge_identity (bs j) (world 0)).mpr holds
  simp only [pinned]
  rw [pinned_lock_iff c hc0]
  constructor
  · rintro (h | h)
    · exact (closure bs (world 0)).mp (by rw [pinned 0]; exact h)
    · exact absurd hcj (h j).ne'
  · intro hall
    left
    rw [← pinned 0]
    exact (closure bs (world 0)).mpr hall

/-! ## Chapter 28 — Ξ = 0 from the action

"The condition Ξ = 0 is derived from the variational principle on M. The action
S = ∫_M (R + L_transport) dV has Euler–Lagrange equations whose solutions yield Ξ as the conserved
Noether charge associated with translation in defect space. In any closed-loop existence, the net
charge must vanish: Ξ = ∮ j · ds = 0." -/

/-- Noether, for translation in defect space (Definition 2, δ_Δ = log w_Δ). The Lagrangian is the
    same under δ ↦ δ + s, so ∂L/∂δ = 0, and along a solution of the Euler–Lagrange equation
    d/dt(∂L/∂δ̇) = ∂L/∂δ the charge ∂L/∂δ̇ never changes. -/
theorem noether_defect (L Lv : ℝ → ℝ → ℝ) (δ δ' : ℝ → ℝ)
    (inv : ∀ s x v, L (x + s) v = L x v)
    (EL : ∀ t, HasDerivAt (fun t => Lv (δ t) (δ' t)) (deriv (fun x => L x (δ' t)) (δ t)) t)
    (a b : ℝ) : Lv (δ a) (δ' a) = Lv (δ b) (δ' b) := by
  have flat : ∀ v, (fun x => L x v) = fun _ => L 0 v := fun v => funext fun x => by
    have := inv x 0 v
    rwa [zero_add] at this
  have h0 : ∀ t, HasDerivAt (fun t => Lv (δ t) (δ' t)) 0 t := fun t => by
    have := EL t
    rwa [flat (δ' t), deriv_const] at this
  exact is_const_of_deriv_eq_zero (fun t => (h0 t).differentiableAt) (fun t => (h0 t).deriv) a b

/-- In any closed loop the net charge vanishes: ∮ j · ds = ∫ₐᵇ j(γ(t)) γ′(t) dt = 0 when the loop
    returns to its start, γ(b) = γ(a). -/
theorem closed_loop_zero (j : ℝ → ℝ) (hj : Continuous j) (γ γ' : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') (closed : γ b = γ a) :
    ∫ t in a..b, j (γ t) * γ' t = 0 := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hF : ∀ x, HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, j y) (j x) x :=
    fun x => (hj.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hcomp : ∀ t, HasDerivAt ((fun u => ∫ y in (0 : ℝ)..u, j y) ∘ γ) (j (γ t) * γ' t) t :=
    fun t => (hF (γ t)).comp t (hγ t)
  have hint : IntervalIntegrable (fun t => j (γ t) * γ' t) MeasureTheory.volume a b :=
    ((hj.comp hγc).mul hγ').intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hcomp t) hint]
  simp [Function.comp, closed]

/-- The seven defects as net charges, each around a closed loop: Ξ = 0. -/
theorem xi_from_action (j : Fin 7 → ℝ → ℝ) (hj : ∀ i, Continuous (j i)) (γ γ' : Fin 7 → ℝ → ℝ)
    (a b : ℝ) (hγ : ∀ i t, HasDerivAt (γ i) (γ' i t) t) (hγ' : ∀ i, Continuous (γ' i))
    (closed : ∀ i, γ i b = γ i a) :
    (fun i => ∫ t in a..b, j i (γ i t) * γ' i t) = 0 :=
  funext fun i => closed_loop_zero (j i) (hj i) (γ i) (γ' i) a b (hγ i) (hγ' i) (closed i)

/-- Chapter 28 with the bridges. If each channel's defect at a state is its net charge around a
    closed loop, then Ξ = 0 at that state, and all seven classical statements hold there. -/
theorem action_to_seven {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State)
    (j : Fin 7 → ℝ → ℝ) (hj : ∀ i, Continuous (j i)) (γ γ' : Fin 7 → ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ i t, HasDerivAt (γ i) (γ' i t) t) (hγ' : ∀ i, Continuous (γ' i))
    (closed : ∀ i, γ i b = γ i a)
    (charge : ∀ i, (bs i).ξ s = ∫ t in a..b, j i (γ i t) * γ' i t) :
    Ξ bs s = 0 ∧ ∀ i, (bs i).claim ((bs i).proj s) := by
  have h0 : Ξ bs s = 0 := funext fun i => by
    show (bs i).ξ s = 0
    rw [charge i]
    exact closed_loop_zero (j i) (hj i) (γ i) (γ' i) a b (hγ i) (hγ' i) (closed i)
  exact ⟨h0, (closure bs s).mp h0⟩

/-- 8.7 — reality is at Ξ = 0, because the world exists. A state with Ξ ≠ 0 cannot be held; the
    realized world is held; so the realized world is at Ξ = 0, and all seven classical faces hold
    together. -/
theorem binary_existence (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i)) (s : State)
    (held : Held k bs s) : Ξ bs s = 0 ∧ ∀ j, (bs j).claim ((bs j).proj s) := by
  have h0 : Ξ bs s = 0 := ((binary k bs s).2).mp held
  exact ⟨h0, (closure bs s).mp h0⟩

/-- 8.7 — the realized world exists and holds (E11: the record contains distinct states; E12: every
    recorded state is a state the world was in). At every moment the world is in, all seven defects
    are zero together, and all seven classical faces hold together. -/
theorem constantly_zero (k : K7) {C : Fin 7 → Type*} (bs : ∀ i, Bridge State (C i))
    (world : ℝ → State) (held : ∀ t, Held k bs (world t)) :
    ∀ t, Ξ bs (world t) = 0 ∧ ∀ j, (bs j).claim ((bs j).proj (world t)) :=
  fun t => binary_existence k bs (world t) (held t)

end UEF.Bridges
