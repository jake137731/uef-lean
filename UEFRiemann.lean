/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 28, in Lean 4 with Mathlib
  ξ₄ — Boundedness

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 28: Phase I (Lemmas 1.1–1.2), Phase II
  (Definition 2), Phase IV (Theorem ξ₄.4.1), Phase VI (Theorem ξ₄.6) and Theorem ξ₄.5.
  The Riemann Hypothesis is Mathlib's own statement `RiemannHypothesis`.
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Complex

namespace UEF.Riemann

/-! ## Phase I — the transports are the primes -/

/-- Definition 1, Step 1 — in a basis, the weight of a transport is w(Δ) = [Λ : Δ(Λ)] = |det Δ|. -/
def weight {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℤ) : ℕ := Δ.det.natAbs

/-- Lemma 1.1 — weights multiply under composition. -/
theorem lemma_1_1 {r : ℕ} (Δ₁ Δ₂ : Matrix (Fin r) (Fin r) ℤ) :
    weight (Δ₁ * Δ₂) = weight Δ₁ * weight Δ₂ := by
  simp [weight, Matrix.det_mul, Int.natAbs_mul]

/-- Lemma 1.2, Step 1 — w(Δ) = 1 exactly when Δ is an automorphism. -/
theorem weight_one_iff {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℤ) : weight Δ = 1 ↔ IsUnit Δ := by
  rw [Matrix.isUnit_iff_isUnit_det, Int.isUnit_iff_natAbs_eq]
  rfl

/-- Irreducible: not an automorphism, and every factorization has an automorphism factor. -/
def Irred {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  ¬IsUnit Δ ∧ ∀ Δ₁ Δ₂, Δ = Δ₁ * Δ₂ → IsUnit Δ₁ ∨ IsUnit Δ₂

/-- Lemma 1.2, Step 2 — a transport of prime weight is irreducible. -/
theorem prime_irreducible {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℤ) (hp : (weight Δ).Prime) :
    Irred Δ := by
  refine ⟨fun hu => ?_, fun Δ₁ Δ₂ h => ?_⟩
  · rw [← weight_one_iff] at hu
    rw [hu] at hp
    exact Nat.not_prime_one hp
  · have hw := lemma_1_1 Δ₁ Δ₂
    rw [← h] at hw
    rw [hw] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h2⟩
    · exact Or.inr ((weight_one_iff Δ₂).mp h1)
    · exact Or.inl ((weight_one_iff Δ₁).mp h2)

/-- Lemma 1.2, Step 5 — every prime is a weight: Δ_p = diag(p, 1, …, 1) has w(Δ_p) = p. -/
theorem prime_transport (r p : ℕ) :
    weight (Matrix.diagonal fun i : Fin (r + 1) => if i = 0 then (p : ℤ) else 1) = p := by
  simp [weight, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- Definition 2 — δ_Δ = log w_Δ adds under composition. -/
theorem defect_adds {r : ℕ} (Δ₁ Δ₂ : Matrix (Fin r) (Fin r) ℤ) (h₁ : weight Δ₁ ≠ 0)
    (h₂ : weight Δ₂ ≠ 0) :
    Real.log (weight (Δ₁ * Δ₂)) = Real.log (weight Δ₁) + Real.log (weight Δ₂) := by
  rw [lemma_1_1, Nat.cast_mul, Real.log_mul (by exact_mod_cast h₁) (by exact_mod_cast h₂)]

/-! ## Phase IV — the transport determinant is ζ -/

/-- The weight p^{−s} of the prime transport p. -/
noncomputable def primeWeight (s : ℂ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

/-- Z_k(s) = Σ_p (p^{−s})^k: the total weight of the closed transports of k repetitions. -/
noncomputable def Z (k : ℕ) (s : ℂ) : ℂ := ∑' p : Nat.Primes, primeWeight s p ^ k

/-- Theorem ξ₄.4.1 — with −log det(I − L_s) = Σ_{k≥1} Z_k(s)/k, for Re s > 1:
    det(I − L_s)⁻¹ = exp(Σ_{k≥1} Z_k(s)/k) = Π_p (1 − p^{−s})⁻¹ = ζ(s). -/
theorem transport_determinant (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (∑' k : ℕ, Z (k + 1) s / ((k + 1 : ℕ) : ℂ)) = riemannZeta s := by
  have hnorm : ∀ p : Nat.Primes, ‖primeWeight s p‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    intro p
    unfold primeWeight
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  have hhalf : ∀ p : Nat.Primes, ‖primeWeight s p‖ ≤ 1 / 2 := by
    intro p
    rw [hnorm]
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    calc ((p : ℕ) : ℝ) ^ (-s.re) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  have hlt : ∀ p : Nat.Primes, ‖primeWeight s p‖ < 1 := fun p => (hhalf p).trans_lt (by norm_num)
  have hsum_p : Summable fun p : Nat.Primes => ‖primeWeight s p‖ := by
    simp only [hnorm]
    exact Nat.Primes.summable_rpow.mpr (by linarith)
  have hinner : ∀ p : Nat.Primes, Summable fun k : ℕ => ‖primeWeight s p‖ ^ (k + 1) := fun p =>
    ((summable_geometric_of_lt_one (norm_nonneg _) (hlt p)).mul_left ‖primeWeight s p‖).congr
      fun k => (pow_succ' _ _).symm
  have houter : Summable fun p : Nat.Primes => ∑' k : ℕ, ‖primeWeight s p‖ ^ (k + 1) := by
    refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun k => by positivity) (fun p => ?_)
      (hsum_p.mul_left 2)
    have e : (fun k : ℕ => ‖primeWeight s p‖ ^ (k + 1))
        = fun k : ℕ => ‖primeWeight s p‖ * ‖primeWeight s p‖ ^ k :=
      funext fun k => pow_succ' _ _
    rw [e, tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) (hlt p), ← div_eq_mul_inv,
      div_le_iff₀ (by linarith [hlt p])]
    nlinarith [norm_nonneg (primeWeight s p), hhalf p]
  have hU : Summable (Function.uncurry fun (p : Nat.Primes) (k : ℕ) =>
      primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by
    refine Summable.of_norm_bounded (fun q : Nat.Primes × ℕ => ‖primeWeight s q.1‖ ^ (q.2 + 1))
      ((summable_prod_of_nonneg fun q => by positivity).mpr ⟨hinner, houter⟩) ?_
    rintro ⟨p, k⟩
    show ‖primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖ ≤ ‖primeWeight s p‖ ^ (k + 1)
    rw [norm_div, norm_pow]
    apply div_le_self (by positivity)
    simp
  have hZ : ∀ k : ℕ, Z (k + 1) s / ((k + 1 : ℕ) : ℂ)
      = ∑' p : Nat.Primes, primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
    intro k
    unfold Z
    rw [tsum_div_const]
  have hlog : ∀ p : Nat.Primes, ∑' k : ℕ, primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)
      = -Complex.log (1 - primeWeight s p) := by
    intro p
    have h := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log (hlt p))
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
      sub_zero] at h
    exact h.tsum_eq
  calc Complex.exp (∑' k : ℕ, Z (k + 1) s / ((k + 1 : ℕ) : ℂ))
      = Complex.exp (∑' k : ℕ, ∑' p : Nat.Primes,
          primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by rw [tsum_congr hZ]
    _ = Complex.exp (∑' p : Nat.Primes, ∑' k : ℕ,
          primeWeight s p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) := by rw [tsum_comm hU]
    _ = Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - primeWeight s p)) := by
          rw [tsum_congr hlog]
    _ = riemannZeta s := riemannZeta_eulerProduct_exp_log hs

/-! ## Phase VI and Theorem ξ₄.5 — the spectral bridge -/

/-- A non-trivial zero of ζ, as in Mathlib's `RiemannHypothesis`. -/
def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- γ_ρ = −i(ρ − 1/2). -/
noncomputable def γ (ρ : ℂ) : ℂ := -I * (ρ - ((1 / 2 : ℝ) : ℂ))

/-- Phase VI, Step 3 — γ_ρ is real exactly when Re ρ = 1/2. -/
theorem gamma_real_iff (ρ : ℂ) : (γ ρ).im = 0 ↔ ρ.re = 1 / 2 := by
  simp [γ, Complex.mul_im, sub_eq_zero]

/-- Unitarity and the critical line — |e^{i log p · γ_ρ}| = p^{Re ρ − 1/2}: modulus 1 exactly
    on the line. -/
theorem unitarity (p : ℕ) (hp : 0 < p) (ρ : ℂ) :
    Complex.abs (Complex.exp (I * (Real.log p : ℂ) * γ ρ)) = (p : ℝ) ^ (ρ.re - 1 / 2) := by
  rw [Complex.abs_exp, Real.rpow_def_of_pos (by exact_mod_cast hp)]
  congr 1
  simp [γ, Complex.mul_re, Complex.mul_im] <;> ring

/-- Theorem ξ₄.6 — Spec(H) = ℝ, so "every γ_ρ lies in Spec(H)" says every γ_ρ is real, and that
    is exactly the Riemann Hypothesis. -/
theorem spectral_bridge : (∀ ρ, NontrivialZero ρ → (γ ρ).im = 0) ↔ RiemannHypothesis := by
  unfold RiemannHypothesis
  constructor
  · intro h s hz ht h1
    exact (gamma_real_iff s).mp (h s ⟨hz, ht, h1⟩)
  · rintro h ρ ⟨hz, ht, h1⟩
    exact (gamma_real_iff ρ).mpr (h ρ hz ht h1)

/-- ξ₄ = sup |Re ρ − 1/2| over the non-trivial zeros (in [0, ∞], so the supremum always exists). -/
noncomputable def ξ₄ : ENNReal := ⨆ (s : ℂ) (_ : NontrivialZero s), ENNReal.ofReal |s.re - 1 / 2|

/-- ξ₄ = 0 is the Riemann Hypothesis, exactly. -/
theorem xi4_zero_iff : ξ₄ = 0 ↔ RiemannHypothesis := by
  unfold ξ₄ RiemannHypothesis
  simp only [ENNReal.iSup_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero]
  constructor
  · intro h s hz ht h1
    exact h s ⟨hz, ht, h1⟩
  · rintro h s ⟨hz, ht, h1⟩
    exact h s hz ht h1

/-- Theorem ξ₄.5 — from ξ₄ = 0, every non-trivial zero lies on Re s = 1/2. -/
theorem theorem_xi4_5 (h : ξ₄ = 0) : RiemannHypothesis := xi4_zero_iff.mp h

end UEF.Riemann
