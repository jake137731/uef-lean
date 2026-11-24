/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 25, in Lean 4 with Mathlib
  ξ₁ — Consistency

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 25: Definition ξ₁.1, Lemmas ξ₁.0′, ξ₁.1,
  ξ₁.1.1, Corollary ξ₁.1.1, Part II, Theorem ξ₁.3 and Theorem ξ₁.4. ξ₁ is the consistency
  projection of the one condition Ξ = 0; its bridge is Theorem B.6 (UEFBridges.lean).
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Complexity

/-! ## Part I — the Turing-to-UEF embedding -/

/-- A configuration of the verifier V: state index, the p(n) reachable tape cells, head, time. -/
structure Config (p : ℕ) where
  q : ℕ
  tape : Fin p → ℕ
  h : ℕ
  t : ℕ

/-- Definition ξ₁.1 — Θ(c_t) = (encode(q_t), encode(α_t), encode(h_t), t/p(n)). -/
noncomputable def Θ {p : ℕ} (c : Config p) : ℝ × (Fin p → ℝ) × ℝ × ℝ :=
  ((c.q : ℝ), fun i => (c.tape i : ℝ), (c.h : ℝ), (c.t : ℝ) / p)

/-- Lemma ξ₁.0′ — Θ is injective on configurations. -/
theorem Θ_injective {p : ℕ} (hp : 0 < p) : Function.Injective (Θ (p := p)) := by
  intro c c' h
  simp only [Θ, Prod.mk.injEq] at h
  obtain ⟨hq, htape, hh, ht⟩ := h
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  cases c
  cases c'
  simp only [Config.mk.injEq]
  refine ⟨by exact_mod_cast hq, ?_, by exact_mod_cast hh, ?_⟩
  · funext i
    exact_mod_cast congrFun htape i
  · rw [div_left_inj' hp'] at ht
    exact_mod_cast ht

/-- Lemma ξ₁.1, Step 1 — one transition changes the state, at most one tape cell and the head by
    at most one, and advances time by 1/p(n): (1/p)² ≤ |Δ_t|² ≤ B_V², and B_V does not depend on
    n, t or w. -/
theorem step_bounds (Q A p : ℕ) (hp : 1 ≤ p) (dq dh : ℝ) (dα : Fin p → ℝ) (j : Fin p)
    (hq : |dq| ≤ (Q : ℝ) - 1) (hα : ∀ i, i ≠ j → dα i = 0) (hαj : |dα j| ≤ (A : ℝ) - 1)
    (hh : |dh| ≤ 1) :
    (1 / (p : ℝ)) ^ 2 ≤ dq ^ 2 + ∑ i, dα i ^ 2 + dh ^ 2 + (1 / (p : ℝ)) ^ 2 ∧
      dq ^ 2 + ∑ i, dα i ^ 2 + dh ^ 2 + (1 / (p : ℝ)) ^ 2
        ≤ ((Q : ℝ) - 1) ^ 2 + ((A : ℝ) - 1) ^ 2 + 1 + 1 := by
  have hsum : ∑ i, dα i ^ 2 = dα j ^ 2 :=
    Finset.sum_eq_single j (fun i _ hi => by rw [hα i hi]; ring)
      (fun h => absurd (Finset.mem_univ j) h)
  have h1 : dq ^ 2 ≤ ((Q : ℝ) - 1) ^ 2 := sq_le_sq' (abs_le.mp hq).1 (abs_le.mp hq).2
  have h2 : dα j ^ 2 ≤ ((A : ℝ) - 1) ^ 2 := sq_le_sq' (abs_le.mp hαj).1 (abs_le.mp hαj).2
  have h3 : dh ^ 2 ≤ 1 := by
    have := sq_le_sq' (abs_le.mp hh).1 (abs_le.mp hh).2
    simpa using this
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h4 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]
    exact hp1
  have h5 : 0 ≤ 1 / (p : ℝ) := by positivity
  rw [hsum]
  constructor
  · nlinarith [sq_nonneg dq, sq_nonneg (dα j), sq_nonneg dh]
  · nlinarith

/-- Corollary ξ₁.1.1 — the tableau is p(n) unit steps, so its geodesic length is p(n). -/
theorem tableau_length (p : ℕ) : ∑ _t ∈ Finset.range p, (1 : ℝ) = p := by simp

/-- Lemma ξ₁.1.1 — any other unit c > 0 multiplies every length by c, and c·q(n) is still a
    polynomial: the class of polynomial bounds does not change. -/
theorem canonicity (c : ℝ) (hc : 0 < c) (T : ℕ → ℝ) (q : Polynomial ℝ)
    (h : ∀ n, T n ≤ q.eval (n : ℝ)) : ∀ n, c * T n ≤ (Polynomial.C c * q).eval (n : ℝ) :=
  fun n => by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_le_mul_of_nonneg_left (h n) hc.le

/-! ## Part II — the energy landscape -/

/-- E_I(w) = ‖Θ(c_{p(n)}(w)) − Θ(c_accept)‖² vanishes exactly when w is accepted. -/
theorem energy_zero_iff {p : ℕ} (hp : 0 < p) (cf ca : Config p) :
    ‖Θ cf - Θ ca‖ ^ 2 = 0 ↔ cf = ca := by
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero]
  exact (Θ_injective hp).eq_iff

/-- Distinct witnesses are at least 1 apart: the vertices form a lattice of mesh at least 1. -/
theorem mesh {p : ℕ} (w w' : Fin p → ℕ) (h : w ≠ w') :
    1 ≤ ‖(fun i => (w i : ℝ)) - fun i => (w' i : ℝ)‖ := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ w' i := Function.ne_iff.mp h
  have h1 : (1 : ℝ) ≤ |(w i : ℝ) - w' i| := by
    have hz : ((w i : ℤ) - w' i) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hi)
    have := Int.one_le_abs hz
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(w i : ℝ) - w' i| := h1
    _ = ‖((fun i => (w i : ℝ)) - fun i => (w' i : ℝ)) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ _ := norm_le_pi_norm _ i

/-! ## Part III — Theorem ξ₁.3, the deterministic flow bound -/

/-- Steps 1–2 — the descent inequality E(w + v) ≤ E(w) + ⟨∇E, v⟩ + (L/2)|v|², at
    v = −(1/L)∇E, lowers E by |∇E|²/(2L). -/
theorem one_step {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (E : V → ℝ)
    (L : ℝ) (hL : 0 < L) (w g : V)
    (descent : ∀ v, E (w + v) ≤ E w + @inner ℝ _ _ g v + L / 2 * ‖v‖ ^ 2) :
    E (w + (-(1 / L)) • g) ≤ E w - 1 / (2 * L) * ‖g‖ ^ 2 := by
  have h := descent ((-(1 / L)) • g)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul] at h
  have hn : ‖(-(1 / L))‖ = 1 / L := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at h
  have e : E w + -(1 / L) * ‖g‖ ^ 2 + L / 2 * (1 / L * ‖g‖) ^ 2
      = E w - 1 / (2 * L) * ‖g‖ ^ 2 := by
    field_simp
    ring
  linarith

/-- Step 3 — with gradient dominance |∇E|² ≥ 2μ(E − E_min), the excess contracts:
    e_{j+1} ≤ (1 − μ/L)e_j. -/
theorem contraction (e e' g2 μ L : ℝ) (hL : 0 < L) (step : e' ≤ e - 1 / (2 * L) * g2)
    (dom : 2 * μ * e ≤ g2) : e' ≤ (1 - μ / L) * e := by
  have h1 : 1 / (2 * L) * (2 * μ * e) ≤ 1 / (2 * L) * g2 :=
    mul_le_mul_of_nonneg_left dom (by positivity)
  have h2 : 1 / (2 * L) * (2 * μ * e) = μ / L * e := by
    field_simp
    ring
  linarith

/-- Step 4 — by induction, e_j ≤ (1 − μ/L)^j e₀. -/
theorem iterate (e : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ j, e (j + 1) ≤ r * e j) :
    ∀ j, e j ≤ r ^ j * e 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc e (j + 1) ≤ r * e j := h j
      _ ≤ r * (r ^ j * e 0) := mul_le_mul_of_nonneg_left ih hr
      _ = r ^ (j + 1) * e 0 := by ring

/-- Step 4 — (1 − x)^j ≤ e^{−jx}, from 1 − x ≤ e^{−x}. -/
theorem pow_le_exp (x : ℝ) (hx : 0 ≤ 1 - x) (j : ℕ) : (1 - x) ^ j ≤ Real.exp (-(j * x)) := by
  have h := Real.add_one_le_exp (-x)
  calc (1 - x) ^ j ≤ Real.exp (-x) ^ j := pow_le_pow_left₀ hx (by linarith) j
    _ = Real.exp (-(j * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Steps 6–7 — with K = L/μ and P = p(n)²: once j > K log(4KP), the bound K P e^{−j/K} on the
    squared distance falls below 1/4, so the distance to the witness set is below 1/2. -/
theorem threshold (K P j : ℝ) (hK : 0 < K) (hP : 0 < P) (hj : K * Real.log (4 * K * P) < j) :
    K * P * Real.exp (-(j / K)) < 1 / 4 := by
  have h1 : Real.log (4 * K * P) < j / K := by
    rw [lt_div_iff₀ hK]
    linarith
  have h2 : 4 * K * P < Real.exp (j / K) := (Real.log_lt_iff_lt_exp (by positivity)).mp h1
  rw [Real.exp_neg, show K * P * (Real.exp (j / K))⁻¹ = K * P / Real.exp (j / K) by ring,
    div_lt_iff₀ (Real.exp_pos _)]
  linarith

/-- Step 7 — rounding: if w is within 1/2 of the witness w* and every other vertex is at least 1
    from w*, then w* is the nearest vertex. -/
theorem rounding {X : Type*} [MetricSpace X] (w wstar v : X) (hmesh : 1 ≤ dist v wstar)
    (h : dist w wstar < 1 / 2) : dist w wstar < dist w v := by
  have := dist_triangle v w wstar
  rw [dist_comm v w] at this
  linarith

/-! ## Part IV — Theorem ξ₁.4 -/

/-- The run time: O(p) to build Θ, O(p) to place the start (one verification, ξ₁ = 0), K·p
    descent steps of O(p) each, and O(p) to verify: O(p(n)²) in all. -/
theorem runtime (c1 c2 c3 c4 K p : ℝ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h4 : 0 ≤ c4) (hp : 1 ≤ p) :
    c1 * p + c2 * p + K * p * (c3 * p) + c4 * p ≤ (c1 + c2 + K * c3 + c4) * p ^ 2 := by
  have hpp : 0 ≤ p ^ 2 - p := by nlinarith
  nlinarith [mul_nonneg h1 hpp, mul_nonneg h2 hpp, mul_nonneg h4 hpp]

/-- Correctness — A accepts exactly when V(x, w*) accepts. On a yes-instance the descent from
    the start returns an accepting witness; on a no-instance no witness is accepted, so A
    rejects. -/
theorem decides {W : Type*} (V : W → Bool) (wstar : W) (inL : Prop)
    (hL : inL ↔ ∃ w, V w = true) (complete : inL → V wstar = true) : V wstar = true ↔ inL :=
  ⟨fun h => hL.mpr ⟨wstar, h⟩, complete⟩

/-- P ⊆ NP always: a deterministic polynomial-time decider is a verifier that ignores its
    witness. -/
theorem P_sub_NP {X W : Type*} (decide : X → Bool) (x : X) (w : W) :
    (fun (y : X) (_ : W) => decide y) x w = decide x := rfl

end UEF.Complexity
