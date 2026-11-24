/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 18, in Lean 4 with Mathlib
  Geometric-Temporal Containment

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 18: Definitions GTC.1–GTC.5,
  Propositions GTC.1–GTC.4, Theorem GTC.1. All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Filter Topology

namespace UEF.Containment

/-- Defect coordinates ξ = (ξ₁, …, ξ₇). -/
abbrev Defects := Fin 7 → ℝ

/-! ## 18.1 — the canonical invariant corridor -/

/-- Definition GTC.1 — C(t) = {x | Lᵢ(t) ≤ ξᵢ(x) ≤ Uᵢ(t)}: in defect coordinates, a box. -/
def corridor (L U : ℝ → Defects) (t : ℝ) : Set Defects := Set.Icc (L t) (U t)

/-- Proposition GTC.1 (i) — C(t) is closed and bounded. -/
theorem corridor_closed_bounded (L U : ℝ → Defects) (t : ℝ) :
    IsClosed (corridor L U t) ∧ Bornology.IsBounded (corridor L U t) :=
  ⟨isClosed_Icc, isCompact_Icc.isBounded⟩

/-- Proposition GTC.1 (ii) — Ker Φ ⊂ C(t): with Lᵢ = 0 and Uᵢ ≥ 0, Ξ = 0 is always inside. -/
theorem ground_in_corridor (L U : ℝ → Defects) (hL : ∀ t, L t = 0) (hU : ∀ t, 0 ≤ U t)
    (t : ℝ) : (0 : Defects) ∈ corridor L U t :=
  ⟨(hL t).le, hU t⟩

/-- Proposition GTC.1 (iv) — C(t) is convex. -/
theorem corridor_convex (L U : ℝ → Defects) (t : ℝ) : Convex ℝ (corridor L U t) :=
  convex_Icc _ _

/-- Proposition GTC.1 (iii) — C(t) is connected. -/
theorem corridor_connected (L U : ℝ → Defects) (hL : ∀ t, L t = 0) (hU : ∀ t, 0 ≤ U t)
    (t : ℝ) : IsConnected (corridor L U t) :=
  ⟨⟨0, ground_in_corridor L U hL hU t⟩, (corridor_convex L U t).isPreconnected⟩

/-! ## 18.2 — the temporal feasibility functional -/

/-- Definition GTC.2 — Θ(x, t*) = 1: a path from the current state x₀ at t₀ reaches x at t*,
    stays in the corridor, and follows dξ/dt = G(ξ) between collapse events (a finite set E). -/
def Feasible (L U : ℝ → Defects) (G : Defects → Defects) (x₀ : Defects) (t₀ : ℝ)
    (x : Defects) (tstar : ℝ) : Prop :=
  ∃ (γ : ℝ → Defects) (E : Finset ℝ), γ t₀ = x₀ ∧ γ tstar = x ∧
    (∀ t ∈ Set.Icc t₀ tstar, γ t ∈ corridor L U t) ∧
    (∀ t ∈ Set.Ioo t₀ tstar, t ∉ E → HasDerivAt γ (G (γ t)) t)

/-- Proposition GTC.2 (ii) — Θ(x₀, t₀) = 1, by the zero-length trajectory. -/
theorem feasible_now (L U : ℝ → Defects) (G : Defects → Defects) (x₀ : Defects) (t₀ : ℝ)
    (h : x₀ ∈ corridor L U t₀) : Feasible L U G x₀ t₀ x₀ t₀ := by
  refine ⟨fun _ => x₀, ∅, rfl, rfl, ?_, ?_⟩
  · intro t ht
    rw [Set.Icc_self, Set.mem_singleton_iff] at ht
    rw [ht]
    exact h
  · intro t ht
    exact absurd (ht.1.trans ht.2) (lt_irrefl _)

/-- Under the Lyapunov condition dV/dt = 2Ξ·G(Ξ) ≤ −λ Ξ·Ξ, λ > 0, the only rest point of the
    defect dynamics is the ground state Ξ = 0. -/
theorem rest_point_is_ground (G : Defects → Defects) (lam : ℝ) (hlam : 0 < lam)
    (lyap : ∀ ξ, 2 * ∑ i, ξ i * G ξ i ≤ -lam * ∑ i, ξ i ^ 2) (x : Defects) (hx : G x = 0) :
    x = 0 := by
  have h := lyap x
  rw [hx] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have hnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hs : ∑ i, x i ^ 2 ≤ 0 := by nlinarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i)).mp (le_antisymm hs hnn)
  funext i
  exact pow_eq_zero_iff two_ne_zero |>.mp (hz i (Finset.mem_univ i))

/-- Proposition GTC.2 (i) — at the rest point Ξ = 0, Θ stays 1 at every later time: the path
    rests there, and the ground state lies in every corridor. -/
theorem feasible_later (L U : ℝ → Defects) (G : Defects → Defects) (hL : ∀ t, L t = 0)
    (hU : ∀ t, 0 ≤ U t) (hG : G 0 = 0) (x₀ : Defects) (t₀ tstar t : ℝ) (h0t : t₀ ≤ tstar)
    (htt : tstar ≤ t) (h : Feasible L U G x₀ t₀ 0 tstar) : Feasible L U G x₀ t₀ 0 t := by
  classical
  obtain ⟨γ, E, h0, h1, hC, hD⟩ := h
  refine ⟨fun s => if s ≤ tstar then γ s else 0, insert tstar E, ?_, ?_, ?_, ?_⟩
  · show (if t₀ ≤ tstar then γ t₀ else 0) = x₀
    rw [if_pos h0t, h0]
  · show (if t ≤ tstar then γ t else 0) = 0
    split_ifs with hle
    · rw [le_antisymm hle htt, h1]
    · rfl
  · intro s hs
    show (if s ≤ tstar then γ s else 0) ∈ corridor L U s
    split_ifs with hle
    · exact hC s ⟨hs.1, hle⟩
    · exact ground_in_corridor L U hL hU s
  · intro s hs hsE
    rw [Finset.mem_insert, not_or] at hsE
    rcases lt_or_gt_of_ne hsE.1 with hlt | hgt
    · have hγ := hD s ⟨hs.1, hlt⟩ hsE.2
      have heq : (fun s => if s ≤ tstar then γ s else 0) =ᶠ[𝓝 s] γ := by
        filter_upwards [Iio_mem_nhds hlt] with y hy
        simp only [if_pos (le_of_lt (show y < tstar from hy))]
      simp only [if_pos hlt.le]
      exact hγ.congr_of_eventuallyEq heq
    · have heq : (fun s => if s ≤ tstar then γ s else 0) =ᶠ[𝓝 s] fun _ => (0 : Defects) := by
        filter_upwards [Ioi_mem_nhds hgt] with y hy
        simp only [if_neg (not_le.mpr (show tstar < y from hy))]
      simp only [if_neg (not_le.mpr hgt), hG]
      exact (hasDerivAt_const s (0 : Defects)).congr_of_eventuallyEq heq

/-- Proposition GTC.2 (iv) — a state with some ξᵢ = 0 but ξⱼ > 0 does not have Ξ = 0. -/
theorem k7_binary (ξ : Defects) (j : Fin 7) (hj : 0 < ξ j) : ξ ≠ 0 :=
  fun h => hj.ne' (congrFun h j)

/-! ## 18.3 — the dynamic containment operator -/

/-- Definition GTC.3 and Proposition GTC.3 (i) — C(t + Δt) = C(t) ∩ ΔC ⊆ C(t). -/
theorem contraction (C ΔC : Set Defects) : C ∩ ΔC ⊆ C := Set.inter_subset_left

/-- With the bounds of GTC.1 the corridor shrinks whenever every Uᵢ does. -/
theorem corridor_mono (L U : ℝ → Defects) (hL : ∀ t, L t = 0) {s t : ℝ} (hU : U t ≤ U s) :
    corridor L U t ⊆ corridor L U s := by
  intro ξ hξ
  refine ⟨?_, hξ.2.trans hU⟩
  rw [hL s]
  have := hξ.1
  rw [hL t] at this
  exact this

/-- Step 4 — Uᵢ(t) ≤ Uᵢ(0)e^{−λt} with λ > 0 drives Uᵢ(t) → 0. -/
theorem bound_to_zero (U : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (h0 : ∀ t, 0 ≤ U t)
    (h : ∀ t, U t ≤ U 0 * Real.exp (-lam * t)) : Tendsto U atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => U 0 * Real.exp (-lam * t)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hlam)).const_mul (U 0)
    simpa [Function.comp_def, neg_mul] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 h0 h

/-- Proposition GTC.3 (ii) — when every Uᵢ(t) → 0 the corridors close on Ker Φ:
    ⋂ₜ C(t) = {Ξ = 0}. -/
theorem contracts_to_ker (L U : ℝ → Defects) (hL : ∀ t, L t = 0) (hU0 : ∀ t, 0 ≤ U t)
    (hU : ∀ i, Tendsto (fun t => U t i) atTop (𝓝 0)) : ⋂ t, corridor L U t = {0} := by
  ext ξ
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    apply le_antisymm
    · exact ge_of_tendsto' (hU i) fun t => (h t).2 i
    · have := (h 0).1 i
      rw [hL 0] at this
      exact this
  · rintro rfl t
    exact ground_in_corridor L U hL hU0 t

/-- Proposition GTC.3 (iii) — with every Uᵢ(t) > 0, C(t) has nonempty interior. -/
theorem corridor_interior (L U : ℝ → Defects) (t : ℝ) (hL : L t = 0) (hU : ∀ i, 0 < U t i) :
    (interior (corridor L U t)).Nonempty := by
  rw [corridor, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  refine ⟨fun i => U t i / 2, ?_⟩
  rw [Set.mem_univ_pi]
  intro i
  rw [interior_Icc, hL]
  refine ⟨?_, ?_⟩
  · show (0 : ℝ) < U t i / 2
    linarith [hU i]
  · show U t i / 2 < U t i
    linarith [hU i]

/-! ## 18.4 — trajectory admissibility -/

/-- Definition GTC.4 — γ is admissible on [t₀, t*] when γ(t) ∈ C(t) at every time. -/
def Admissible (L U : ℝ → Defects) (γ : ℝ → Defects) (t₀ tstar : ℝ) : Prop :=
  ∀ t ∈ Set.Icc t₀ tstar, γ t ∈ corridor L U t

/-- Proposition GTC.4 (i) — the constant trajectory at Ξ = 0 is admissible. -/
theorem admissible_ground (L U : ℝ → Defects) (hL : ∀ t, L t = 0) (hU : ∀ t, 0 ≤ U t)
    (t₀ tstar : ℝ) : Admissible L U (fun _ => 0) t₀ tstar :=
  fun t _ => ground_in_corridor L U hL hU t

/-- Proposition GTC.4 (ii) — admissibility is closed under restriction to a sub-interval. -/
theorem admissible_restrict {L U : ℝ → Defects} {γ : ℝ → Defects} {t₀ tstar a b : ℝ}
    (h : Admissible L U γ t₀ tstar) (ha : t₀ ≤ a) (hb : b ≤ tstar) : Admissible L U γ a b :=
  fun t ht => h t ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- Proposition GTC.4 (iii) — admissible before and after a collapse at t₁: admissible across. -/
theorem admissible_concat {L U : ℝ → Defects} {γ : ℝ → Defects} {t₀ t₁ t₂ : ℝ}
    (h1 : Admissible L U γ t₀ t₁) (h2 : Admissible L U γ t₁ t₂) : Admissible L U γ t₀ t₂ := by
  intro t ht
  rcases le_total t t₁ with h | h
  · exact h1 t ⟨ht.1, h⟩
  · exact h2 t ⟨h, ht.2⟩

/-- Proposition GTC.4 (iv) — one exit from the corridor and the trajectory is not admissible. -/
theorem inadmissible {L U : ℝ → Defects} {γ : ℝ → Defects} {t₀ tstar : ℝ} (t : ℝ)
    (ht : t ∈ Set.Icc t₀ tstar) (hout : γ t ∉ corridor L U t) : ¬Admissible L U γ t₀ tstar :=
  fun h => hout (h t ht)

/-! ## 18.5 — the complete geometric-temporal stability condition -/

/-- Definition GTC.5 — (I) Ξ(x) = 0, (II) x ∈ C(t*), (III) Θ(x, t*) = 1, and (IV) the path
    stayed in bounds, which Θ already requires of its path. -/
def GTCStable (L U : ℝ → Defects) (G : Defects → Defects) (x₀ : Defects) (t₀ : ℝ)
    (x : Defects) (tstar : ℝ) : Prop :=
  x = 0 ∧ x ∈ corridor L U tstar ∧ Feasible L U G x₀ t₀ x tstar

/-- Theorem GTC.1 (a) — every GTC-stable state satisfies Ξ = 0. -/
theorem gtc_ground {L U : ℝ → Defects} {G : Defects → Defects} {x₀ : Defects} {t₀ : ℝ}
    {x : Defects} {tstar : ℝ} (h : GTCStable L U G x₀ t₀ x tstar) : x = 0 :=
  h.1

/-- Theorem GTC.1 (b) — not every state with Ξ = 0 is GTC-stable: from a current state outside
    the corridor, no admissible path reaches it. -/
theorem gtc_strict : ∃ (L U : ℝ → Defects) (G : Defects → Defects) (x₀ : Defects),
    ¬GTCStable L U G x₀ 0 0 1 := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 2, ?_⟩
  rintro ⟨_, _, γ, E, h0, _, hC, _⟩
  have := (hC 0 ⟨le_refl 0, zero_le_one⟩).2 0
  rw [h0] at this
  norm_num at this

end UEF.Containment
