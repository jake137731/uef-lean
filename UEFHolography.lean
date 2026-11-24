/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 15, in Lean 4 with Mathlib
  M-Theory, String Theory, and Holography

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 15: 15.4 (the B-field), 15.5 (ER = EPR,
  Steps 1–6), and 15.6 (Theorems 1 and 2). All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Holography

/-! ## 15.4 — the Kalb–Ramond field B = κ_B S ∧ A -/

/-- B_μν = κ_B(S_μA_ν − S_νA_μ). -/
def B (κ : ℝ) (S A : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ := κ * (S μ * A ν - S ν * A μ)

/-- B_μν = −B_νμ: an antisymmetric 2-form, the tensor type the Kalb–Ramond field must have. -/
theorem B_antisymmetric (κ : ℝ) (S A : Fin 4 → ℝ) (μ ν : Fin 4) : B κ S A μ ν = -B κ S A ν μ := by
  unfold B
  ring

theorem B_diagonal (κ : ℝ) (S A : Fin 4 → ℝ) (μ : Fin 4) : B κ S A μ μ = 0 := by
  unfold B
  ring

/-- The exterior derivative of a 1-form, (dS)_λμ = ∂_λS_μ − ∂_μS_λ; dS l μ stands for ∂_l S_μ. -/
def ext (dS : Fin 4 → Fin 4 → ℝ) (l μ : Fin 4) : ℝ := dS l μ - dS μ l

/-- ∂_λB_μν by the Leibniz rule, ∂_λ(S_μA_ν) = (∂_λS_μ)A_ν + S_μ(∂_λA_ν). -/
def dB (κ : ℝ) (S A : Fin 4 → ℝ) (dS dA : Fin 4 → Fin 4 → ℝ) (l μ ν : Fin 4) : ℝ :=
  κ * (dS l μ * A ν + S μ * dA l ν - (dS l ν * A μ + S ν * dA l μ))

/-- H = dB, the cyclic sum of ∂_λB_μν. -/
def H (κ : ℝ) (S A : Fin 4 → ℝ) (dS dA : Fin 4 → Fin 4 → ℝ) (l μ ν : Fin 4) : ℝ :=
  dB κ S A dS dA l μ ν + dB κ S A dS dA μ ν l + dB κ S A dS dA ν l μ

/-- H = dB = κ_B(dS ∧ A − S ∧ dA). -/
theorem H_eq (κ : ℝ) (S A : Fin 4 → ℝ) (dS dA : Fin 4 → Fin 4 → ℝ) (l μ ν : Fin 4) :
    H κ S A dS dA l μ ν
      = κ * ((ext dS l μ * A ν + ext dS μ ν * A l + ext dS ν l * A μ)
          - (S l * ext dA μ ν + S μ * ext dA ν l + S ν * ext dA l μ)) := by
  unfold H dB ext
  ring

/-! ## 15.5 — ER = EPR -/

/-- Step 1 — for a pure state in Schmidt form, E_F = S(ρ_A) = −Σ λₖ log λₖ. -/
noncomputable def EF {d : ℕ} (p : Fin d → ℝ) : ℝ := ∑ k, Real.negMulLog (p k)

theorem negMulLog_zero_iff {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  simp only [Real.negMulLog, mul_eq_zero, neg_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
    · linarith
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

/-- Step 1 — E_F ≥ 0. -/
theorem EF_nonneg {d : ℕ} (p : Fin d → ℝ) (h0 : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) : 0 ≤ EF p := by
  apply Finset.sum_nonneg
  intro k _
  exact Real.negMulLog_nonneg (h0 k)
    ((Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ k)).trans h1.le)

/-- Step 1 — E_F = 0 exactly when there is a single Schmidt term: the state is a product. -/
theorem EF_zero_iff {d : ℕ} (p : Fin d → ℝ) (h0 : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) :
    EF p = 0 ↔ ∃ k, p k = 1 ∧ ∀ j, j ≠ k → p j = 0 := by
  have hle : ∀ k, p k ≤ 1 := fun k =>
    (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ k)).trans h1.le
  constructor
  · intro h
    have hterm : ∀ k, p k = 0 ∨ p k = 1 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.negMulLog_nonneg (h0 j) (hle j))).mp h k (Finset.mem_univ k)
      exact (negMulLog_zero_iff (h0 k)).mp this
    obtain ⟨k, hk⟩ : ∃ k, p k ≠ 0 := by
      by_contra hne
      push_neg at hne
      rw [Finset.sum_eq_zero (fun j _ => hne j)] at h1
      exact zero_ne_one h1
    have hk1 : p k = 1 := (hterm k).resolve_left hk
    refine ⟨k, hk1, fun j hj => ?_⟩
    rcases hterm j with h' | h'
    · exact h'
    · exfalso
      have hpair : p j + p k ≤ ∑ i, p i := by
        rw [← Finset.sum_pair hj]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => h0 i)
      linarith
  · rintro ⟨k, hk, hj⟩
    unfold EF
    apply Finset.sum_eq_zero
    intro j _
    by_cases hjk : j = k
    · rw [hjk, hk]
      simp
    · rw [hj j hjk]
      simp

/-- Theorem 1 — the maximally entangled state, λₖ = 1/d, has E_F = log d. -/
theorem EF_maximal (d : ℕ) (hd : 0 < d) : EF (fun _ : Fin d => (1 : ℝ) / d) = Real.log d := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp only [EF, Real.negMulLog, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [one_div, Real.log_inv, neg_mul_neg, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

/-- Step 2 — Area(H) = 4G_N E_F and, by Theorem 14, A = 16πG_N²M²/c⁴. Together they fix the
    bridge mass M = (c²/G_N)√(E_F G_N/4π). -/
theorem bridge_mass (G c E M : ℝ) (hG : 0 < G) (hc : 0 < c) (hE : 0 ≤ E) (hM : 0 ≤ M) :
    16 * π * G ^ 2 * M ^ 2 / c ^ 4 = 4 * G * E ↔ M = c ^ 2 / G * Real.sqrt (E * G / (4 * π)) := by
  have area : 16 * π * G ^ 2 * M ^ 2 / c ^ 4 = 4 * G * E ↔ M ^ 2 = c ^ 4 * E / (4 * π * G) := by
    rw [div_eq_iff (by positivity), eq_div_iff (by positivity)]
    constructor
    · intro h
      apply mul_left_cancel₀ (show 4 * G ≠ 0 by positivity)
      linear_combination h
    · intro h
      linear_combination 4 * G * h
  have hsq : c ^ 2 / G * Real.sqrt (E * G / (4 * π)) = Real.sqrt (c ^ 4 * E / (4 * π * G)) := by
    rw [show c ^ 4 * E / (4 * π * G) = (c ^ 2 / G) ^ 2 * (E * G / (4 * π)) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have key : M = Real.sqrt (c ^ 4 * E / (4 * π * G)) ↔ M ^ 2 = c ^ 4 * E / (4 * π * G) := by
    constructor
    · intro h
      rw [h, Real.sq_sqrt (by positivity)]
    · intro h
      rw [← h, Real.sqrt_sq hM]
  rw [area, hsq, key]

/-- Step 3 — separable ⟺ the throat is closed: M = 0 exactly when E_F = 0. -/
theorem closed_iff_separable (G c E : ℝ) (hG : 0 < G) (hc : 0 < c) (hE : 0 ≤ E) :
    c ^ 2 / G * Real.sqrt (E * G / (4 * π)) = 0 ↔ E = 0 := by
  have hc2 : c ^ 2 / G ≠ 0 := by positivity
  rw [mul_eq_zero, Real.sqrt_eq_zero (by positivity)]
  simp [hc2, hG.ne', hc.ne', Real.pi_ne_zero]

/-- Step 4 — entangled ⟺ the bridge is open: M > 0 exactly when E_F > 0. -/
theorem open_iff_entangled (G c E : ℝ) (hG : 0 < G) (hc : 0 < c) (hE : 0 ≤ E) :
    0 < c ^ 2 / G * Real.sqrt (E * G / (4 * π)) ↔ 0 < E := by
  have hM : 0 ≤ c ^ 2 / G * Real.sqrt (E * G / (4 * π)) := by positivity
  constructor
  · intro h
    exact lt_of_le_of_ne hE fun h0 => h.ne' ((closed_iff_separable G c E hG hc hE).mpr h0.symm)
  · intro h
    exact lt_of_le_of_ne hM fun h0 => h.ne' ((closed_iff_separable G c E hG hc hE).mp h0.symm)

/-- Step 5 — S_ent(A) = Area(H)/4G_N when Area(H) = 4G_N E_F. -/
theorem ryu_takayanagi (G E : ℝ) (hG : 0 < G) : 4 * G * E / (4 * G) = E := by
  field_simp

/-! ## 15.6 — Theorem 1 (ER = EPR) and Theorem 2 (brane-world localization) -/

/-- Theorem 1 — the fiber distance d²(y_A, y_B) = Σ R_i²Δθ_i², Δθ_i = Arg e^{i(θ_A,i − θ_B,i)},
    is at most π²ΣR_i², however far apart x_A and x_B lie in U. -/
theorem fiber_distance_bound (R θA θB : Fin 4 → ℝ) :
    ∑ i, R i ^ 2 * (Complex.arg (Complex.exp (((θA i - θB i : ℝ) : ℂ) * Complex.I))) ^ 2
      ≤ π ^ 2 * ∑ i, R i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := abs_le.mp (Complex.abs_arg_le_pi (Complex.exp (((θA i - θB i : ℝ) : ℂ) * Complex.I)))
  have h2 := sq_le_sq' h.1 h.2
  rw [mul_comm (π ^ 2)]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- Theorem 1 — the throat fluxes: Φ_A + Φ_B + Φ_∞ = 0 and Φ_∞ = 0 give Φ_B = −Φ_A. -/
theorem throat_flux (ΦA ΦB Φinf : ℝ) (h : ΦA + ΦB + Φinf = 0) (h0 : Φinf = 0) : ΦB = -ΦA := by
  linarith

/-- Theorem 1 — the null energy condition: T^dark_μν k^μ k^ν = ρ_dark(u·k)² ≥ 0. -/
theorem null_energy (ρ uk : ℝ) (hρ : 0 < ρ) : 0 ≤ ρ * uk ^ 2 := by positivity

/-- Theorem 2 — Vol(T⁴) = (2π)⁴R₁R₂R₃R₄, the product of the four circles. -/
theorem fiber_volume (R : Fin 4 → ℝ) : ∏ i, (2 * π * R i) = (2 * π) ^ 4 * ∏ i, R i := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Theorem 2 — the same volume as a measure: the box [0, 2πR₁] × ⋯ × [0, 2πR₄]. -/
theorem torus_volume (R : Fin 4 → ℝ) (hR : ∀ i, 0 < R i) :
    MeasureTheory.volume (Set.Icc (0 : Fin 4 → ℝ) (fun i => 2 * π * R i))
      = ENNReal.ofReal ((2 * π) ^ 4 * ∏ i, R i) := by
  rw [Real.volume_Icc_pi, ← fiber_volume,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := hR i; positivity)]
  simp

/-- Theorem 2 — the Kaluza–Klein masses m_n² = Σ_j (n_j/R_j)² vanish exactly for the zero mode. -/
theorem kk_mass_zero_iff (n : Fin 4 → ℤ) (R : Fin 4 → ℝ) (hR : ∀ j, 0 < R j) :
    ∑ j, ((n j : ℝ) / R j) ^ 2 = 0 ↔ n = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  constructor
  · intro h
    funext j
    have := h j (Finset.mem_univ j)
    simp [(hR j).ne'] at this
    simpa using this
  · rintro rfl j _
    simp

end UEF.Holography
