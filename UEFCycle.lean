/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 20, in Lean 4 with Mathlib
  The Cosmological Cycle: Black Holes, White Holes, and the Return to P

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 20, WH.1–WH.8.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real Filter Topology MeasureTheory

namespace UEF.Cycle

/-! ## WH.1 — black-hole sink and white-hole source -/

/-- Flux balance: Φ_BH + Φ_WH + Φ_ext = 0 with Φ_ext = 0 gives Φ_WH = −Φ_BH. -/
theorem mouths (ΦBH ΦWH Φext : ℝ) (h : ΦBH + ΦWH + Φext = 0) (h0 : Φext = 0) : ΦWH = -ΦBH := by
  linarith

/-- The tortoise coordinate r* = r + 2GM log(r/2GM − 1) has dr*/dr = 1/f, f = 1 − 2GM/r,
    outside the horizon. -/
theorem tortoise (m r : ℝ) (hm : 0 < m) (hr : 2 * m < r) :
    HasDerivAt (fun r => r + 2 * m * Real.log (r / (2 * m) - 1)) (1 / (1 - 2 * m / r)) r := by
  have hr0 : r ≠ 0 := by linarith
  have hm0 : m ≠ 0 := hm.ne'
  have hrm : r - 2 * m ≠ 0 := by linarith
  have hpos : 0 < r / (2 * m) - 1 := by
    rw [sub_pos, one_lt_div (by positivity)]
    exact hr
  have h1 : HasDerivAt (fun r => r / (2 * m) - 1) (1 / (2 * m)) r :=
    ((hasDerivAt_id r).div_const (2 * m)).sub_const 1
  refine ((hasDerivAt_id r).add ((h1.log hpos.ne').const_mul (2 * m))).congr_deriv ?_
  field_simp

/-! ## WH.2 — no un-collapse -/

/-- R_{n+1} = R_n ∪ {r_{n+1}} makes realization monotone, and no step can shrink it. -/
theorem no_uncollapse {Ω : Type*} (R : ℕ → Set Ω) (r : ℕ → Ω)
    (rule : ∀ n, R (n + 1) = R n ∪ {r (n + 1)}) : Monotone R ∧ ∀ n, ¬R (n + 1) ⊂ R n := by
  have step : ∀ n, R n ⊆ R (n + 1) := fun n => by
    rw [rule n]
    exact Set.subset_union_left
  exact ⟨monotone_nat_of_le_succ step, fun n h => h.2 (step n)⟩

/-- For any measure, μ(R_n) ≤ μ(R_{n+1}). -/
theorem measure_grows {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : ℕ → Set Ω)
    (mono : Monotone R) : Monotone fun n => μ (R n) :=
  fun _ _ h => measure_mono (mono h)

/-! ## WH.3 — P as ground state, attractor, and restart point -/

/-- V_P(x) = Σ w_O ⟨O⟩_x² ≥ 0, and it vanishes exactly when every expectation value does, as
    at P by A1. -/
theorem VP_ground {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ o ∈ s, 0 < w o) (obs : ι → ℝ) :
    0 ≤ ∑ o ∈ s, w o * obs o ^ 2 ∧ (∑ o ∈ s, w o * obs o ^ 2 = 0 ↔ ∀ o ∈ s, obs o = 0) := by
  have hnn : ∀ o ∈ s, 0 ≤ w o * obs o ^ 2 := fun o ho => mul_nonneg (hw o ho).le (sq_nonneg _)
  refine ⟨Finset.sum_nonneg hnn, ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h o ho
    rcases mul_eq_zero.mp (h o ho) with h' | h'
    · exact absurd h' (hw o ho).ne'
    · exact pow_eq_zero_iff two_ne_zero |>.mp h'
  · intro h o ho
    rw [h o ho]
    ring

/-- The cycle map 𝒞 = 𝓡_P ∘ Flow ∘ ℬ, with 𝓡_P the terminal return, has 𝒞(P) = P. -/
theorem cycle_fixes_P {X : Type*} (P : X) (B Flow : X → X) :
    ((fun _ => P) ∘ Flow ∘ B) P = P := rfl

/-! ## WH.4 — depletion, turnover, contraction, and bounce -/

/-- Unrealized potential depletes: Ω_dark,n = Ω ∖ R_n can only shrink. -/
theorem depletes {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : ℕ → Set Ω)
    (mono : Monotone R) : Antitone fun n => μ (R n)ᶜ :=
  fun _ _ h => measure_mono (Set.compl_subset_compl.mpr (mono h))

/-- ρ_DE = F(μ(Ω_dark)) with F monotone, so Λ_eff = 8πGρ_DE falls with the dark measure. -/
theorem lambda_falls (F : ℝ → ℝ) (hF : Monotone F) (G : ℝ) (hG : 0 ≤ G) (m : ℕ → ℝ)
    (hm : Antitone m) : Antitone fun n => 8 * π * G * F (m n) :=
  fun _ _ h => mul_le_mul_of_nonneg_left (hF (hm h)) (by positivity)

/-- Turnover — with ä/a = −(4πG/3)(ρ + 3p) + Λ/3 and a > 0: ä = 0 exactly at
    Λ = 4πG(ρ + 3p), and ä < 0 exactly below it. -/
theorem turnover (a add ρ p G Λ : ℝ) (ha : 0 < a)
    (accel : add / a = -(4 * π * G / 3) * (ρ + 3 * p) + Λ / 3) :
    (add = 0 ↔ Λ = 4 * π * G * (ρ + 3 * p)) ∧ (add < 0 ↔ Λ < 4 * π * G * (ρ + 3 * p)) := by
  have e : add = a * (-(4 * π * G / 3) * (ρ + 3 * p) + Λ / 3) := by
    rw [← accel, mul_div_assoc', mul_div_cancel_left₀ _ ha.ne']
  rw [e]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' ha.ne'
    · linarith
  · rw [h]
    ring
  · rcases mul_neg_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
    · linarith
    · linarith
  · exact mul_neg_of_pos_of_neg ha (by linarith)

/-- Contraction deepens binding — |V_grav| = (3/5)GM²/R with R = R₀a grows as a falls. -/
theorem binding_grows (G M R0 a b : ℝ) (hG : 0 < G) (hM : 0 < M) (hR : 0 < R0) (ha : 0 < a)
    (hab : a < b) : 3 / 5 * G * M ^ 2 / (R0 * b) < 3 / 5 * G * M ^ 2 / (R0 * a) := by
  rw [div_lt_div_iff₀ (mul_pos hR (ha.trans hab)) (mul_pos hR ha)]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hab hR) (by positivity)

/-- No new mass — for dust, ρ̇ + 3(ȧ/a)ρ = 0 keeps ρa³ constant: contraction concentrates
    existing mass-energy and creates none. -/
theorem dust_conserved (a ρ a' ρ' : ℝ → ℝ) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hne : ∀ t, a t ≠ 0)
    (cont : ∀ t, ρ' t + 3 * (a' t / a t) * ρ t = 0) (s t : ℝ) :
    ρ s * a s ^ 3 = ρ t * a t ^ 3 := by
  have hd : ∀ t, HasDerivAt (fun t => ρ t * a t ^ 3) 0 t := by
    intro t
    refine ((hρ t).mul ((ha t).pow 3)).congr_deriv ?_
    have e : ρ' t = -(3 * (a' t / a t) * ρ t) := by linarith [cont t]
    have h0 := hne t
    rw [e]
    field_simp
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s t

/-- A smooth bounce needs dH/dt > 0 where H = 0. With dH/dt = −4πG(ρ + p) + k/a², there is
    none for k ≤ 0 and ρ + p ≥ 0: the bounce needs curvature or the S-sector stress-energy. -/
theorem no_bounce_without (G ρ p k a : ℝ) (hG : 0 ≤ G) (hk : k ≤ 0) (hρp : 0 ≤ ρ + p) :
    -4 * π * G * (ρ + p) + k / a ^ 2 ≤ 0 := by
  have h1 : 0 ≤ 4 * π * G * (ρ + p) := mul_nonneg (mul_nonneg (by positivity) hG) hρp
  have h2 : k / a ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hk (sq_nonneg a)
  linarith

/-! ## WH.5 — the randomness budget -/

/-- Var(ε) = G(μ(Ω_dark)) with G(0) = 0, G continuous at 0: μ(Ω_dark) → 0 gives Var(ε) → 0. -/
theorem randomness_starves (Gf : ℝ → ℝ) (hG0 : Gf 0 = 0) (hcont : ContinuousAt Gf 0)
    (m : ℝ → ℝ) (hm : Tendsto m atTop (𝓝 0)) : Tendsto (fun t => Gf (m t)) atTop (𝓝 0) := by
  have := hcont.tendsto.comp hm
  rwa [hG0] at this

/-- ‖H_Q‖ ≤ C Var(ε) and Var(ε) → 0 give H_Q → 0: the Hamiltonian turns classical. -/
theorem quantum_off (HQ V : ℝ → ℝ) (C : ℝ) (hb : ∀ t, |HQ t| ≤ C * V t)
    (hV : Tendsto V atTop (𝓝 0)) : Tendsto HQ atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => C * V t) atTop (𝓝 0) := by simpa using hV.const_mul C
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hb t) h1

/-- The S flux survives the bounce: Φ⁺ − Φ⁻ = ∫𝒱 d(*S) = 0. -/
theorem flux_survives (Φplus Φminus : ℝ) (h : Φplus - Φminus = 0) : Φplus = Φminus := by
  linarith

/-! ## WH.7 — one thread, one winding, and connectivity -/

/-- n[s] = (1/2π)∮dφ ∈ ℤ: a closed thread s(θ) = e^{iφ(θ)} has φ(2π) − φ(0) = 2πn. -/
theorem winding_integer (φ0 φ1 : ℝ)
    (closed : Complex.exp (φ1 * Complex.I) = Complex.exp (φ0 * Complex.I)) :
    ∃ n : ℤ, φ1 - φ0 = 2 * π * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp closed
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- Winding is a topological invariant: an integer that varies continuously along a homotopy
    s_t, t ∈ [0, 1], cannot jump. -/
theorem winding_invariant (n : ℝ → ℤ) (hn : ContinuousOn n (Set.Icc 0 1)) : n 0 = n 1 :=
  isPreconnected_Icc.constant hn ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩

/-- c_AB = ⟨S_A, S_B⟩/(‖S_A‖‖S_B‖) = 1 exactly when S_B is a positive multiple of S_A. -/
theorem aligned_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    @inner ℝ _ _ x y / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x :=
  real_inner_div_norm_mul_norm_eq_one_iff x y

end UEF.Cycle
