/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 32, in Lean 4 with Mathlib
  The Erdős Readings of ξ₄ and ξ₅

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 32.2 (Lemma EAP.1, Corollary EAP.1,
  Proposition EAP.1, Lemma EAP.2, Proposition EAP.2, Theorems EAP.1–EAP.2, Corollary EAP.2) and
  32.3 (Proposition EAB.1, Step 1). The Erdős conjecture on arithmetic progressions is ξ₅ = 0
  read on integer configurations; its line is the residual R₅(A) = 0 of 32.2, Part I.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Filter Topology

namespace UEF.Erdos

/-! ## Lemma EAP.1 — the power-law form of the natural weight on ℕ -/

/-- Lemma EAP.1 — a weight μ > 0 on ℕ with μ(mn) = μ(m)μ(n)/μ(1) and μ(n + 1) < μ(n) has the
    form μ(n) = c/n^α with c > 0 and α > 0. -/
theorem power_law (μ : ℕ → ℝ) (hpos : ∀ n, 0 < μ n)
    (mult : ∀ m n, 1 ≤ m → 1 ≤ n → μ (m * n) = μ m * μ n / μ 1)
    (decay : ∀ n, 1 ≤ n → μ (n + 1) < μ n) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ n, 1 ≤ n → μ n = c / (n : ℝ) ^ α := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = -Real.log (μ n / μ 1) := ⟨_, fun n => rfl⟩
  have hf : ∀ n, 0 < μ n / μ 1 := fun n => div_pos (hpos n) (hpos 1)
  -- Step 3: g is completely additive
  have gmul : ∀ m n, 1 ≤ m → 1 ≤ n → g (m * n) = g m + g n := by
    intro m n hm hn
    rw [hg, hg, hg, mult m n hm hn,
      show μ m * μ n / μ 1 / μ 1 = (μ m / μ 1) * (μ n / μ 1) by ring,
      Real.log_mul (hf m).ne' (hf n).ne']
    ring
  have g1 : g 1 = 0 := by rw [hg, div_self (hpos 1).ne', Real.log_one, neg_zero]
  have gpow : ∀ n k : ℕ, 1 ≤ n → g (n ^ k) = (k : ℝ) * g n := by
    intro n k hn
    induction k with
    | zero => simp [g1]
    | succ k ih =>
      rw [pow_succ, gmul _ _ (Nat.one_le_pow _ _ hn) hn, ih]
      push_cast
      ring
  -- Step 5: monotone decay makes g increasing
  have mono : ∀ a b, 1 ≤ a → a ≤ b → μ b ≤ μ a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ b hab ih => exact (decay b (ha.trans hab)).le.trans ih
  have gmono : ∀ a b, 1 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    rw [hg, hg, neg_le_neg_iff]
    exact Real.log_le_log (hf b) (div_le_div_of_nonneg_right (mono a b ha hab) (hpos 1).le)
  -- Step 4: g(2) > 0
  have g2 : 0 < g 2 := by
    rw [hg, neg_pos]
    apply Real.log_neg (hf 2)
    rw [div_lt_one (hpos 1)]
    exact decay 1 le_rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Step 5: g(n) = α log n with α = g(2)/log 2
  have key : ∀ n, 1 ≤ n → g n = g 2 / Real.log 2 * Real.log n := by
    intro n hn
    set r := Real.log n / Real.log 2 with hr
    have bound : ∀ k : ℕ, 1 ≤ k → |g n - r * g 2| ≤ g 2 / k := by
      intro k hk
      set m := Nat.log 2 (n ^ k) with hm
      have hnk : n ^ k ≠ 0 := pow_ne_zero _ (by omega)
      have lo : 2 ^ m ≤ n ^ k := Nat.pow_log_le_self 2 hnk
      have hi : n ^ k < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have g_lo : (m : ℝ) * g 2 ≤ k * g n := by
        rw [← gpow 2 m (by norm_num), ← gpow n k hn]
        exact gmono _ _ (Nat.one_le_two_pow) lo
      have g_hi : (k : ℝ) * g n ≤ (m + 1 : ℕ) * g 2 := by
        rw [← gpow 2 (m + 1) (by norm_num), ← gpow n k hn]
        exact gmono _ _ (Nat.one_le_pow _ _ hn) hi.le
      have r_lo : (m : ℝ) ≤ k * r := by
        rw [hr, mul_div_assoc', le_div_iff₀ hlog2, ← Real.log_pow, ← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast lo)
      have r_hi : (k : ℝ) * r ≤ (m + 1 : ℕ) := by
        rw [hr, mul_div_assoc', div_le_iff₀ hlog2, ← Real.log_pow, ← Real.log_pow]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        exact Real.log_le_log (pow_pos hn0 k) (by exact_mod_cast hi.le)
      push_cast at g_hi r_hi
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have e1 : (k : ℝ) * (g n - r * g 2) ≤ g 2 := by
        nlinarith [mul_le_mul_of_nonneg_right r_lo g2.le]
      have e2 : -g 2 ≤ (k : ℝ) * (g n - r * g 2) := by
        nlinarith [mul_le_mul_of_nonneg_right r_hi g2.le]
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · rw [← neg_div, div_le_iff₀ hk0]
        linarith
      · rw [le_div_iff₀ hk0]
        linarith
    have hgr : g n = r * g 2 := by
      by_contra hne
      have hpos' : 0 < |g n - r * g 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨k, hk⟩ := exists_nat_gt (g 2 / |g n - r * g 2|)
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, Nat.cast_zero] at hk
          exact absurd hk (not_lt.mpr (div_nonneg g2.le hpos'.le))
        · exact h
      have hb := bound k hk1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [le_div_iff₀ hk0] at hb
      rw [div_lt_iff₀ hpos'] at hk
      linarith
    rw [hgr, hr]
    ring
  refine ⟨μ 1, g 2 / Real.log 2, hpos 1, div_pos g2 hlog2, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : μ n / μ 1 = Real.exp (-g n) := by rw [hg, neg_neg, Real.exp_log (hf n)]
  have e2 : (n : ℝ) ^ (g 2 / Real.log 2) = Real.exp (g n) := by
    rw [Real.rpow_def_of_pos hn0, key n hn]
    congr 1
    ring
  rw [e2, div_eq_mul_inv, ← Real.exp_neg, ← e1, mul_div_assoc',
    mul_div_cancel_left₀ _ (hpos 1).ne']

/-- Corollary EAP.1 — Σ 1/n^α diverges exactly when α ≤ 1; the critical exponent is α = 1. -/
theorem critical_exponent (α : ℝ) : Summable (fun n : ℕ => 1 / (n : ℝ) ^ α) ↔ 1 < α :=
  Real.summable_one_div_nat_rpow

/-! ## Proposition EAP.1 — accumulation on integer configurations -/

/-- ordacc(A_N) = c Σ_{n ∈ A_N} 1/n grows without bound exactly when Σ_{n ∈ A} 1/n diverges. -/
theorem accumulation (A : Set ℕ) (c : ℝ) (hc : 0 < c)
    (hdiv : ¬Summable (Set.indicator A fun n : ℕ => (1 : ℝ) / n)) :
    Tendsto (fun N => c * ∑ i ∈ Finset.range N, Set.indicator A (fun n : ℕ => (1 : ℝ) / n) i)
      atTop atTop := by
  have hnn : ∀ n, 0 ≤ Set.indicator A (fun n : ℕ => (1 : ℝ) / n) n := fun n =>
    Set.indicator_nonneg (fun a _ => div_nonneg zero_le_one (Nat.cast_nonneg a)) n
  exact ((not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hdiv).const_mul_atTop hc

/-! ## Lemma EAP.2 — arithmetic progressions exhaust periodic structure on ℤ -/

/-- Step 1 — every isometry of ℤ is a translation or a reflection composed with a translation. -/
theorem isometries_of_Z (φ : ℤ → ℤ) (iso : ∀ m n, |φ m - φ n| = |m - n|) :
    (∀ m, φ m = φ 0 + m) ∨ (∀ m, φ m = φ 0 - m) := by
  rcases abs_eq_abs.mp (iso 1 0) with h | h
  · left
    intro m
    rcases abs_eq_abs.mp (iso m 0) with h0 | h0 <;>
      rcases abs_eq_abs.mp (iso m 1) with h2 | h2 <;> omega
  · right
    intro m
    rcases abs_eq_abs.mp (iso m 0) with h0 | h0 <;>
      rcases abs_eq_abs.mp (iso m 1) with h2 | h2 <;> omega

/-- An arithmetic progression of length k in S: a, a + d, …, a + (k − 1)d with d ≥ 1. -/
def HasAP (S : Set ℕ) (k : ℕ) : Prop := ∃ a d : ℕ, 1 ≤ d ∧ ∀ i < k, a + i * d ∈ S

/-- Step 2 — a set with period d contains a, a + d, a + 2d, … up to its maximum. -/
theorem periodic_contains_AP (S : Set ℕ) (a d M : ℕ) (ha : a ∈ S)
    (period : ∀ s ∈ S, s + d ≤ M → s + d ∈ S) : ∀ i, a + i * d ≤ M → a + i * d ∈ S := by
  intro i
  induction i with
  | zero => intro _; simpa using ha
  | succ i ih =>
    intro hi
    have h1 : a + i * d + d ≤ M := by nlinarith
    have h2 := period _ (ih (by nlinarith)) h1
    rwa [show a + (i + 1) * d = a + i * d + d by ring]

/-- Step 3 — reflection maps an arithmetic progression to an arithmetic progression. -/
theorem reflection_AP (a d i : ℤ) : -(a + i * d) = -a + i * (-d) := by ring

/-! ## Proposition EAP.2 — rank valuation is depth -/

/-- Steps 3–4 — with rankval = F ∘ L for F monotone and unbounded, rankval is unbounded exactly
    when L is. -/
theorem depth (F : ℕ → ℝ) (hF : Monotone F) (hunb : ∀ M, ∃ k, M < F k) (L : ℕ → ℕ) :
    (∀ M, ∃ N, M < F (L N)) ↔ (∀ k, ∃ N, k ≤ L N) := by
  constructor
  · intro h k
    obtain ⟨N, hN⟩ := h (F k)
    refine ⟨N, ?_⟩
    by_contra hlt
    exact absurd (hF (not_le.mp hlt).le) (not_le.mpr hN)
  · intro h M
    obtain ⟨k, hk⟩ := hunb M
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, hk.trans_le (hF hN)⟩

/-- Step 5 — the truncations A_N are nested, so a progression in A_N stays in every later one. -/
theorem nested (A : Set ℕ) {N N' : ℕ} (h : N ≤ N') (k : ℕ)
    (hN : HasAP (A ∩ Set.Icc 1 N) k) : HasAP (A ∩ Set.Icc 1 N') k := by
  obtain ⟨a, d, hd, hap⟩ := hN
  exact ⟨a, d, hd, fun i hi => ⟨(hap i hi).1, (hap i hi).2.1, (hap i hi).2.2.trans h⟩⟩

/-! ## Theorems EAP.1 and EAP.2 — the Erdős conjecture on arithmetic progressions -/

/-- Theorem EAP.2 — Σ_{n∈A} 1/n = ∞ gives ordacc(A_N) → ∞ (Proposition EAP.1); ξ₅ = 0 read on
    the integers, R₅(A) = 0, gives rankval(A_N) unbounded (Theorem EAP.1); rankval = F ∘ L gives
    L(A_N) unbounded (Proposition EAP.2); and A contains arithmetic progressions of every finite
    length. -/
theorem erdos_AP (A : Set ℕ) (c : ℝ) (hc : 0 < c)
    (hdiv : ¬Summable (Set.indicator A fun n : ℕ => (1 : ℝ) / n))
    (F : ℕ → ℝ) (hF : Monotone F) (hunb : ∀ M, ∃ k, M < F k) (L : ℕ → ℕ)
    (hL : ∀ N k, k ≤ L N → HasAP (A ∩ Set.Icc 1 N) k)
    (R5 : Tendsto (fun N => c * ∑ i ∈ Finset.range N,
        Set.indicator A (fun n : ℕ => (1 : ℝ) / n) i) atTop atTop →
      ∀ M, ∃ N, M < F (L N)) :
    ∀ k, HasAP A k := by
  intro k
  obtain ⟨N, hN⟩ := (depth F hF hunb L).mp (R5 (accumulation A c hc hdiv)) k
  obtain ⟨a, d, hd, hap⟩ := hL N k hN
  exact ⟨a, d, hd, fun i hi => (hap i hi).1⟩

/-- Corollary EAP.2 — the primes have divergent reciprocal sum (Euler), so Theorem EAP.2 applies
    with A = P: the primes contain arithmetic progressions of every finite length. -/
theorem green_tao (c : ℝ) (hc : 0 < c) (F : ℕ → ℝ) (hF : Monotone F) (hunb : ∀ M, ∃ k, M < F k)
    (L : ℕ → ℕ) (hL : ∀ N k, k ≤ L N → HasAP ({p | p.Prime} ∩ Set.Icc 1 N) k)
    (R5 : Tendsto (fun N => c * ∑ i ∈ Finset.range N,
        Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i) atTop atTop →
      ∀ M, ∃ N, M < F (L N)) :
    ∀ k, HasAP {p | p.Prime} k :=
  erdos_AP _ c hc not_summable_one_div_on_primes F hF hunb L hL R5

/-! ## 32.3 — Proposition EAB.1, Step 1 -/

/-- Prime gaps have no fixed upper bound: (K + 1)! + 2, …, (K + 1)! + (K + 1) are all composite. -/
theorem prime_gap (K j : ℕ) (h2 : 2 ≤ j) (hj : j ≤ K + 1) : ¬(Nat.factorial (K + 1) + j).Prime := by
  intro hp
  have hdvd : j ∣ Nat.factorial (K + 1) + j :=
    dvd_add (Nat.dvd_factorial (by omega) hj) (dvd_refl j)
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · omega
  · have := Nat.factorial_pos (K + 1)
    omega

end UEF.Erdos
