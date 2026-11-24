/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapters 21, 22 and 23, in Lean 4 with Mathlib
  Collapse Geometry: the Derivations, the Collapse Laws, and What It Feels Like

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 21 (21.1–21.8), Chapter 22 (Theorems 20, 22,
  25, 26, 29, 32, 37, 39) and Chapter 23 (23.2 and 23.6: Lemmas 23.1–23.2, Theorem 23.3).
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real Filter Topology

namespace UEF.Collapse

/-! ## Theorem 20 — consciousness is a collapse engine: K(Ψₙ) = argmin_B E(B) -/

/-- Over a finite non-empty set of admissible branches a minimizer of E exists. -/
theorem minimizer_exists {B : Type*} (D : Finset B) (hD : D.Nonempty) (E : B → ℝ) :
    ∃ b ∈ D, ∀ b' ∈ D, E b ≤ E b' :=
  D.exists_min_image E hD

/-- When E is strictly convex on the admissible set, the minimizer is unique. -/
theorem minimizer_unique {V : Type*} [AddCommGroup V] [Module ℝ V] (D : Set V) (E : V → ℝ)
    (hE : StrictConvexOn ℝ D E) {x y : V} (hx : x ∈ D) (hy : y ∈ D)
    (hxm : ∀ z ∈ D, E x ≤ E z) (hym : ∀ z ∈ D, E y ≤ E z) : x = y := by
  by_contra hne
  have hmid := hE.2 hx hy hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ D :=
    hE.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have h1 := hxm _ hm
  have h2 := hxm y hy
  have h3 := hym x hx
  simp only [smul_eq_mul] at hmid
  linarith

/-- Theorem 29 — a branch with a larger incompatibility than some admissible branch is never the
    minimizer: it is filtered out of the reachable set. -/
theorem filtered {B : Type*} (D : Set B) (E : B → ℝ) (b b' : B) (hb' : b' ∈ D) (h : E b' < E b) :
    ¬∀ z ∈ D, E b ≤ E z :=
  fun hmin => absurd (hmin b' hb') (not_le.mpr h)

/-- Theorem 39 — the collapse engine cannot leave its geometry: a minimizer over the admissible
    domain lies in that domain. -/
theorem stays_admissible {B : Type*} (D : Finset B) (hD : D.Nonempty) (E : B → ℝ) :
    ∃ b, b ∈ D ∧ ∀ b' ∈ D, E b ≤ E b' :=
  D.exists_min_image E hD

/-- Theorem 25 — the moral domain D = {B | ⟨S_s, B⟩ ≥ 0} is convex and closed. -/
theorem moral_domain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : E) :
    Convex ℝ {B : E | 0 ≤ @inner ℝ _ _ S B} ∧ IsClosed {B : E | 0 ≤ @inner ℝ _ _ S B} := by
  constructor
  · intro x hx y hy a b ha hb _
    simp only [Set.mem_setOf_eq, inner_add_right, real_inner_smul_right] at hx hy ⊢
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  · exact isClosed_le continuous_const (continuous_const.inner continuous_id)

/-! ## 21.4, 21.5 and Theorems 22, 26 — reflection and the identity fixed point -/

/-- 21.4 — if Λ is a contraction toward Ψ*, |Λ(Ψ) − Ψ*| ≤ c|Ψ − Ψ*|, then
    |Λⁿ(Ψ) − Ψ*| ≤ cⁿ|Ψ − Ψ*|. -/
theorem recursion_bound {X : Type*} [MetricSpace X] (Λ : X → X) (ψs : X) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, dist (Λ x) ψs ≤ c * dist x ψs) (x : X) (n : ℕ) :
    dist (Λ^[n] x) ψs ≤ c ^ n * dist x ψs := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc dist (Λ (Λ^[n] x)) ψs ≤ c * dist (Λ^[n] x) ψs := h _
      _ ≤ c * (c ^ n * dist x ψs) := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ n * c * dist x ψs := by ring

/-- 21.5 — δₙ ≤ cⁿδ₀ → 0. -/
theorem identity_converges (c δ0 : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun n : ℕ => c ^ n * δ0) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const δ0

/-- Theorem 22 — Banach: a contraction on a complete space has exactly one fixed point
    Ψ* = Kᵢ(Ψ*), and every iteration converges to it. -/
theorem identity_attractor {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) :
    (∃! x, f x = x) ∧ ∀ x, Tendsto (fun n => f^[n] x) atTop (𝓝 (ContractingWith.fixedPoint f hf)) :=
  ⟨⟨ContractingWith.fixedPoint f hf, ContractingWith.fixedPoint_isFixedPt hf,
      fun _ hy => hf.fixedPoint_unique hy⟩,
    fun x => hf.tendsto_iterate_fixedPoint x⟩

/-- Theorem 26 — with |Ψ_{R} − Ψ*| ≤ c^R|Ψ − Ψ*|, the fidelity F = |Ψ_R − Ψ*|⁻¹ is at least
    c^{−R}F₀. -/
theorem fidelity_bound (d0 dR c : ℝ) (R : ℕ) (hc0 : 0 < c) (hd0 : 0 < d0) (hdR : 0 < dR)
    (h : dR ≤ c ^ R * d0) : 1 / c ^ R * (1 / d0) ≤ 1 / dR := by
  rw [div_mul_div_comm, one_mul]
  exact one_div_le_one_div_of_le hdR h

/-- …and each added layer multiplies the bound by 1/c > 1. -/
theorem fidelity_grows (c : ℝ) (R : ℕ) (hc0 : 0 < c) (hc1 : c < 1) :
    1 / c ^ R < 1 / c ^ (R + 1) :=
  one_div_lt_one_div_of_lt (pow_pos hc0 (R + 1))
    (by rw [pow_succ]; exact mul_lt_of_lt_one_right (pow_pos hc0 R) hc1)

/-! ## 21.6 and Theorem 32 — drift evolves logarithmically -/

/-- One step: ΔD′ = ΔD + log(1 + (ε − η)e^{−ΔD}) gives e^{ΔD′} = e^{ΔD} + ε − η. -/
theorem drift_step (D e : ℝ) (h : 0 < 1 + e * Real.exp (-D)) :
    Real.exp (D + Real.log (1 + e * Real.exp (-D))) = Real.exp D + e := by
  rw [Real.exp_add, Real.exp_log h, Real.exp_neg, mul_add, mul_one, mul_left_comm,
    mul_inv_cancel₀ (Real.exp_pos D).ne', mul_one]

/-- From ΔD = 0: e^{ΔD} = 1 + Σεₙ − Σηₙ and ΔD = log(1 + Σεₙ − Σηₙ). -/
theorem drift_log (D ε η : ℕ → ℝ) (h0 : D 0 = 0)
    (pos : ∀ n, 0 < 1 + (ε n - η n) * Real.exp (-D n))
    (step : ∀ n, D (n + 1) = D n + Real.log (1 + (ε n - η n) * Real.exp (-D n))) (n : ℕ) :
    Real.exp (D n) = 1 + ∑ k ∈ Finset.range n, (ε k - η k) ∧
      D n = Real.log (1 + ∑ k ∈ Finset.range n, (ε k - η k)) := by
  have hexp : ∀ n, Real.exp (D n) = 1 + ∑ k ∈ Finset.range n, (ε k - η k) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [step n, drift_step _ _ (pos n), ih, Finset.sum_range_succ]
      ring
  refine ⟨hexp n, ?_⟩
  rw [← hexp n, Real.log_exp]

/-! ## 21.3, 21.8 and Theorem 37 — time distortion, dimensional access, collapse rate -/

/-- 21.3 — Δt ∝ 1/(1 + |κᵉ|): larger curvature, shorter objective span per experienced unit;
    at κᵉ = 0 the baseline. -/
theorem time_distortion (κ1 κ2 : ℝ) (h : |κ1| ≤ |κ2|) : 1 / (1 + |κ2|) ≤ 1 / (1 + |κ1|) :=
  one_div_le_one_div_of_le (by positivity) (by linarith)

theorem baseline : 1 / (1 + |(0 : ℝ)|) = 1 := by simp

/-- Theorem 37 — Δt = 1/ω: a higher collapse rate packs the collapses closer. -/
theorem collapse_rate (ω1 ω2 : ℝ) (h1 : 0 < ω1) (h : ω1 < ω2) : 1 / ω2 < 1 / ω1 :=
  one_div_lt_one_div_of_lt h1 h

/-- 21.8 and Theorem 35 — dim_access = log(Cᴾ × Rᵣ × ⟨S, Ψ⟩): the three factors add on the
    logarithmic scale. -/
theorem dimensional_access (C R M : ℝ) (hC : 0 < C) (hR : 0 < R) (hM : 0 < M) :
    Real.log (C * R * M) = Real.log C + Real.log R + Real.log M := by
  rw [Real.log_mul (by positivity) hM.ne', Real.log_mul hC.ne' hR.ne']

/-! ## 23.2 — collapse path integrals -/

/-- Z_β = Σ_B e^{−βE(B)}: as β → ∞ the weight of the unique minimizer tends to 1 (Laplace). -/
theorem laplace {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (b : ι) (hb : ∀ B, B ≠ b → E b < E B) :
    Tendsto (fun β : ℝ => Real.exp (-β * E b) / ∑ B, Real.exp (-β * E B)) atTop (𝓝 1) := by
  have key : ∀ β : ℝ, Real.exp (-β * E b) / ∑ B, Real.exp (-β * E B)
      = 1 / ∑ B, Real.exp (-β * (E B - E b)) := by
    intro β
    have hS : 0 < ∑ B, Real.exp (-β * E B) :=
      Finset.sum_pos (fun B _ => Real.exp_pos _) ⟨b, Finset.mem_univ b⟩
    have hs : ∑ B, Real.exp (-β * (E B - E b)) = (∑ B, Real.exp (-β * E B)) * Real.exp (β * E b) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : Real.exp (-β * E b) * Real.exp (β * E b) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hs, div_eq_div_iff hS.ne' (by positivity)]
    linear_combination (∑ B, Real.exp (-β * E B)) * h1
  have hlim : Tendsto (fun β : ℝ => ∑ B, Real.exp (-β * (E B - E b))) atTop
      (𝓝 (∑ B, if B = b then (1 : ℝ) else 0)) := by
    apply tendsto_finset_sum
    intro B _
    by_cases hB : B = b
    · subst hB
      simp
    · rw [if_neg hB]
      have hd : 0 < E B - E b := sub_pos.mpr (hb B hB)
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hd)).congr
        fun β => ?_
      simp [Function.comp, neg_mul]
  have h1 : (∑ B, if B = b then (1 : ℝ) else 0) = 1 := by simp
  rw [h1] at hlim
  have := hlim.inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr fun β => ?_
  rw [key β, one_div]

/-! ## 23.6 — when a channel opens -/

/-- Lemma 23.1 — Φ = e^{−X} with X ≥ 0 lies in (0, 1]. -/
theorem coherence_range (X : ℝ) (hX : 0 ≤ X) : 0 < Real.exp (-X) ∧ Real.exp (-X) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩

/-- Lemma 23.1 — Φ = 1 exactly when the being does not swerve, div S = 0, and no two fields
    contradict: X = α‖ε‖² + β∫‖div S‖² + Σγᵢⱼ Cᵢⱼ = 0 term by term. -/
theorem coherence_one_iff {ι : Type*} (s : Finset ι) (α β : ℝ) (γ C : ι → ℝ) (a b : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : ∀ i ∈ s, 0 < γ i) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : ∀ i ∈ s, 0 ≤ C i) :
    Real.exp (-(α * a + β * b + ∑ i ∈ s, γ i * C i)) = 1 ↔ a = 0 ∧ b = 0 ∧ ∀ i ∈ s, C i = 0 := by
  rw [Real.exp_eq_one_iff, neg_eq_zero]
  have hnn : ∀ i ∈ s, 0 ≤ γ i * C i := fun i hi => mul_nonneg (hγ i hi).le (hC i hi)
  have hs : 0 ≤ ∑ i ∈ s, γ i * C i := Finset.sum_nonneg hnn
  have hαa : 0 ≤ α * a := mul_nonneg hα.le ha
  have hβb : 0 ≤ β * b := mul_nonneg hβ.le hb
  constructor
  · intro h
    have h1 : α * a = 0 := by linarith
    have h2 : β * b = 0 := by linarith
    have h3 : ∑ i ∈ s, γ i * C i = 0 := by linarith
    refine ⟨(mul_eq_zero.mp h1).resolve_left hα.ne', (mul_eq_zero.mp h2).resolve_left hβ.ne',
      fun i hi => ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h3 i hi
    exact (mul_eq_zero.mp this).resolve_left (hγ i hi).ne'
  · rintro ⟨rfl, rfl, hc⟩
    rw [Finset.sum_eq_zero fun i hi => by rw [hc i hi, mul_zero]]
    ring

/-- Lemma 23.1, Step 4 — Φ strictly decreases as X grows. -/
theorem coherence_strictAnti : StrictAnti fun X : ℝ => Real.exp (-X) :=
  fun _ _ h => Real.exp_lt_exp.mpr (neg_lt_neg h)

/-- Lemma 23.2 — no floor: Φ < c exactly when X > −ln c, and Φ → 0 as X → ∞. -/
theorem no_floor (X c : ℝ) (hc : 0 < c) : Real.exp (-X) < c ↔ -Real.log c < X := by
  rw [← Real.lt_log_iff_exp_lt hc]
  constructor <;> intro h <;> linarith

theorem decoherence : Tendsto (fun X : ℝ => Real.exp (-X)) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero

/-- Theorem 23.3, Step 3 — a violation with β∫‖div S‖² > 0 drops coherence:
    ΔΦ = e^{−β∫‖div S‖²} − 1 < 0. -/
theorem violation_drops (β D : ℝ) (hβD : 0 < β * D) : Real.exp (-(β * D)) - 1 < 0 := by
  have := Real.exp_lt_exp.mpr (show -(β * D) < 0 by linarith)
  rw [Real.exp_zero] at this
  linarith

/-- Theorem 23.3, Step 5 — correction lowers X, and Φ rises. -/
theorem repair_restores (X X' : ℝ) (h : X' < X) : Real.exp (-X) < Real.exp (-X') :=
  coherence_strictAnti h

end UEF.Collapse
