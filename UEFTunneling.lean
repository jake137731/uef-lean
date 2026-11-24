/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 17, in Lean 4 with Mathlib
  Information Tunneling

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 17: Theorem T6.2 and Corollary T6.2.1,
  Theorem T7.1, 17.7 (the 1/r⁴ law) and 17.8 (correlation and synchronization).
  All arithmetic is exact. No floating point anywhere.
-/
import Mathlib

open Real

namespace UEF.Tunneling

/-! ## Theorem T6.2 — Lyapunov stability -/

/-- Step 3 — Young's inequality: ab ≤ (λ/2)a² + (1/2λ)b². -/
theorem young (a b l : ℝ) (hl : 0 < l) : a * b ≤ l / 2 * a ^ 2 + 1 / (2 * l) * b ^ 2 := by
  have h : 0 ≤ (l * a - b) ^ 2 / (2 * l) := by positivity
  have e : l / 2 * a ^ 2 + 1 / (2 * l) * b ^ 2 - a * b = (l * a - b) ^ 2 / (2 * l) := by
    field_simp
    ring
  linarith

/-- Step 6 — dV/dτ ≤ −2‖∇D‖² and the Poincaré inequality ‖D‖² ≤ C_P‖∇D‖² give
    dV/dτ ≤ −(2/C_P)V. -/
theorem lyapunov_rate (dV V G CP : ℝ) (hCP : 0 < CP) (h1 : dV ≤ -2 * G) (h2 : V ≤ CP * G) :
    dV ≤ -(2 / CP) * V := by
  have h3 : 2 / CP * V ≤ 2 / CP * (CP * G) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 2 / CP * (CP * G) = 2 * G := by
    rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hCP.ne']
  rw [neg_mul]
  linarith

/-- Corollary T6.2.1 — the decay rate 2λ₁ is at least Φλ₁, because Φ ≤ 1. -/
theorem rate_bound (Φ l1 : ℝ) (hΦ : Φ ≤ 1) (hl : 0 < l1) : Φ * l1 ≤ 2 * l1 := by
  nlinarith

/-- Mode by mode — a_k(τ) = a_k(0)e^{−λ_kτ} solves da_k/dτ = −λ_k a_k. -/
theorem mode_decay (a0 l τ : ℝ) :
    HasDerivAt (fun t => a0 * Real.exp (-l * t)) (-l * (a0 * Real.exp (-l * τ))) τ := by
  exact (((hasDerivAt_id τ).const_mul (-l)).exp.const_mul a0).congr_deriv
    (by simp only [id_eq]; ring)

/-- On the mean-zero subspace, with λ_k ≥ λ₁ for every mode:
    ‖D(τ)‖² = Σ|a_k|²e^{−2λ_kτ} ≤ e^{−2λ₁τ}‖D(0)‖². -/
theorem modes_bound {ι : Type*} (s : Finset ι) (a l : ι → ℝ) (l1 τ : ℝ) (hτ : 0 ≤ τ)
    (hl : ∀ k ∈ s, l1 ≤ l k) :
    ∑ k ∈ s, a k ^ 2 * Real.exp (-2 * l k * τ) ≤ Real.exp (-2 * l1 * τ) * ∑ k ∈ s, a k ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [hl k hk]

/-- The flat torus — for k ∈ ℤⁿ, k ≠ 0, the eigenvalue |k|² = Σkᵢ² is at least 1. -/
theorem spectral_gap {n : ℕ} (k : Fin n → ℤ) (hk : k ≠ 0) : 1 ≤ ∑ i, (k i : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    have h2 : 1 ≤ |k i| := Int.one_le_abs hi
    have h3 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast h2
    nlinarith [abs_nonneg ((k i : ℝ)), sq_abs ((k i : ℝ))]
  calc (1 : ℝ) ≤ (k i : ℝ) ^ 2 := h1
    _ ≤ ∑ j, (k j : ℝ) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i)

/-- …and |k|² = 1 is reached by a unit winding, so λ₁ = 1 and the decay rate is λ = 2. -/
theorem gap_reached (n : ℕ) (i : Fin n) : ∑ j, ((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℝ) ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Step 5 on the flat torus — with a₀ = 0, ‖D‖² = Σ|a_k|² ≤ Σ|k|²|a_k|² = ‖∇D‖²: C_P = 1/λ₁ = 1. -/
theorem poincare {n : ℕ} (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℝ) (h0 : ∀ k ∈ s, k ≠ 0) :
    ∑ k ∈ s, a k ^ 2 ≤ ∑ k ∈ s, (∑ i, (k i : ℝ) ^ 2) * a k ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  nlinarith [spectral_gap k (h0 k hk), sq_nonneg (a k)]

/-- The modes on each circle: −d²/dθ² cos(kθ) = k² cos(kθ). -/
theorem eigenmode (k θ : ℝ) :
    HasDerivAt (fun t => Real.cos (k * t)) (-k * Real.sin (k * θ)) θ ∧
      HasDerivAt (fun t => -k * Real.sin (k * t)) (-k ^ 2 * Real.cos (k * θ)) θ := by
  constructor
  · exact ((Real.hasDerivAt_cos (k * θ)).comp θ ((hasDerivAt_id θ).const_mul k)).congr_deriv
      (by ring)
  · exact (((Real.hasDerivAt_sin (k * θ)).comp θ ((hasDerivAt_id θ).const_mul k)).const_mul
      (-k)).congr_deriv (by ring)

/-! ## Theorem T7.1 — periodic geodesics and synchronization -/

/-- Step 4 — a closed unit-speed geodesic with Lv = 2πw, w ∈ ℤⁿ, has length L = 2π‖w‖. -/
theorem closed_length {n : ℕ} (v : Fin n → ℝ) (w : Fin n → ℤ) (L : ℝ) (hL : 0 ≤ L)
    (unit : ∑ i, v i ^ 2 = 1) (closes : ∀ i, L * v i = 2 * π * w i) :
    L = 2 * π * Real.sqrt (∑ i, (w i : ℝ) ^ 2) := by
  have h : L ^ 2 = (2 * π) ^ 2 * ∑ i, (w i : ℝ) ^ 2 := by
    calc L ^ 2 = L ^ 2 * ∑ i, v i ^ 2 := by rw [unit, mul_one]
      _ = ∑ i, (L * v i) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, (2 * π * w i) ^ 2 := by simp only [closes]
      _ = (2 * π) ^ 2 * ∑ i, (w i : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [← Real.sqrt_sq hL, h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- General radii — a geodesic y₀ + vt that closes at T > 0, v_iT = 2πR_ik_i, has every ratio
    (v_i/R_i)/(v_j/R_j) = k_i/k_j rational: periodicity is exact commensurability. -/
theorem commensurable {n : ℕ} (v R : Fin n → ℝ) (k : Fin n → ℤ) (T : ℝ) (hT : 0 < T)
    (hR : ∀ i, 0 < R i) (closes : ∀ i, v i * T = 2 * π * R i * k i) (i j : Fin n)
    (hj : k j ≠ 0) :
    (v i / R i) / (v j / R j) = ((k i / k j : ℚ) : ℝ) := by
  have hv : ∀ m, v m / R m = 2 * π * k m / T := by
    intro m
    rw [div_eq_div_iff (hR m).ne' hT.ne']
    linear_combination closes m
  have hj' : (k j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  rw [hv i, hv j]
  push_cast
  field_simp
  ring

/-- Synchronization — the wrapped distance d_T² = ΣR_i²Δθ_i² is zero exactly when every phase
    difference is. -/
theorem synchronized {n : ℕ} (R Δ : Fin n → ℝ) (hR : ∀ i, 0 < R i) :
    ∑ i, R i ^ 2 * Δ i ^ 2 = 0 ↔ ∀ i, Δ i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)]
  constructor
  · intro h i
    have := h i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h') (hR i).ne'
    · exact pow_eq_zero_iff two_ne_zero |>.mp h'
  · intro h i _
    rw [h i]
    ring

/-! ## 17.7 — why the potential falls as 1/r⁴ -/

/-- u(r) = C r^{−n} solves the radial Laplace equation u″ + ((d − 1)/r)u′ = 0 in d = n + 2
    dimensions, with r^{d−1}u′ constant. -/
theorem radial_green (C : ℝ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => C * r ^ (-(n : ℤ))) (C * (-(n : ℝ)) * r ^ (-(n : ℤ) - 1)) r ∧
    HasDerivAt (fun r : ℝ => C * (-(n : ℝ)) * r ^ (-(n : ℤ) - 1))
      (C * (-(n : ℝ)) * (-(n : ℝ) - 1) * r ^ (-(n : ℤ) - 1 - 1)) r ∧
    C * (-(n : ℝ)) * (-(n : ℝ) - 1) * r ^ (-(n : ℤ) - 1 - 1)
      + ((n + 2 : ℝ) - 1) / r * (C * (-(n : ℝ)) * r ^ (-(n : ℤ) - 1)) = 0 := by
  refine ⟨((hasDerivAt_zpow (-(n : ℤ)) r (Or.inl hr)).const_mul C).congr_deriv
      (by push_cast; ring),
    ((hasDerivAt_zpow (-(n : ℤ) - 1) r (Or.inl hr)).const_mul (C * (-(n : ℝ)))).congr_deriv
      (by push_cast; ring), ?_⟩
  rw [zpow_sub_one₀ hr (-(n : ℤ) - 1)]
  ring

/-- r^{d−1}u′ is constant: r^{n+1} · C(−n)r^{−n−1} = −nC. -/
theorem flux_constant (C : ℝ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r ^ ((n : ℤ) + 1) * (C * (-(n : ℝ)) * r ^ (-(n : ℤ) - 1)) = -(n : ℝ) * C := by
  have : r ^ ((n : ℤ) + 1) * r ^ (-(n : ℤ) - 1) = 1 := by
    rw [← zpow_add₀ hr]
    simp
  calc r ^ ((n : ℤ) + 1) * (C * (-(n : ℝ)) * r ^ (-(n : ℤ) - 1))
      = C * (-(n : ℝ)) * (r ^ ((n : ℤ) + 1) * r ^ (-(n : ℤ) - 1)) := by ring
    _ = -(n : ℝ) * C := by rw [this]; ring

/-- A potential falling as 1/r⁴ belongs to d − 2 = 4, d = 6 = 4 + 1 + 1; a 1/r³ potential
    belongs to five. -/
theorem six_dimensions : (∀ d : ℕ, 2 < d → (d - 2 = 4 ↔ d = 6)) ∧ 4 + 1 + 1 = 6 ∧
    (∀ d : ℕ, 2 < d → (d - 2 = 3 ↔ d = 5)) := by
  refine ⟨fun d _ => by omega, rfl, fun d _ => by omega⟩

/-! ## 17.8 — correlation, communication, and causality -/

section Correlation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- C_corr(A, B) = |⟨Ψ_A, Ψ_B⟩| / (‖Ψ_A‖‖Ψ_B‖). -/
noncomputable def Ccorr (x y : E) : ℝ := ‖@inner ℂ _ _ x y‖ / (‖x‖ * ‖y‖)

/-- By Cauchy–Schwarz, 0 ≤ C_corr ≤ 1. -/
theorem Ccorr_range (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) : 0 ≤ Ccorr x y ∧ Ccorr x y ≤ 1 := by
  have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  refine ⟨by unfold Ccorr; positivity, ?_⟩
  unfold Ccorr
  rw [div_le_one hpos]
  exact norm_inner_le_norm x y

/-- C_corr = 1 exactly when Ψ_B = rΨ_A for some r ≠ 0, r = c e^{iθ}: the same state up to phase. -/
theorem Ccorr_one_iff (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    Ccorr x y = 1 ↔ ∃ r : ℂ, r ≠ 0 ∧ y = r • x := by
  have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  unfold Ccorr
  rw [div_eq_one_iff_eq hpos.ne']
  exact norm_inner_eq_norm_iff hx hy

/-- For normalized states, ‖Ψ_A − Ψ_B‖² = 2 − 2Re⟨Ψ_A, Ψ_B⟩. -/
theorem mismatch (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * RCLike.re (@inner ℂ _ _ x y) := by
  rw [@norm_sub_sq ℂ, hx, hy]
  ring

/-- For normalized states, C_corr ≥ 1 − ½‖Ψ_A − Ψ_B‖²: correlation tends to 1 as the mismatch
    tends to 0. -/
theorem Ccorr_ge (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    1 - 1 / 2 * ‖x - y‖ ^ 2 ≤ Ccorr x y := by
  unfold Ccorr
  rw [mismatch x y hx hy, hx, hy, mul_one, div_one]
  have := RCLike.re_le_norm (@inner ℂ _ _ x y)
  linarith

end Correlation

/-- Synchronization — a locked state Δω = K sin Δθ* exists exactly when |Δω| ≤ |K|. -/
theorem lock_exists (Δω K : ℝ) (hK : K ≠ 0) : (∃ θ, Δω = K * Real.sin θ) ↔ |Δω| ≤ |K| := by
  constructor
  · rintro ⟨θ, rfl⟩
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg K) (Real.abs_sin_le_one θ)
  · intro h
    refine ⟨Real.arcsin (Δω / K), ?_⟩
    have h1 : |Δω / K| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hK)]
      exact h
    rw [Real.sin_arcsin (abs_le.mp h1).1 (abs_le.mp h1).2, mul_div_assoc']
    exact (mul_div_cancel_left₀ Δω hK).symm

/-- For equal frequencies and K > 0 the lock Δθ* = 0 is stable: dΔθ/dt = −K sin Δθ vanishes
    there and its slope is −K < 0. -/
theorem lock_stable (K : ℝ) (hK : 0 < K) :
    (0 : ℝ) - K * Real.sin 0 = 0 ∧ HasDerivAt (fun x => (0 : ℝ) - K * Real.sin x) (-K) 0 ∧
      -K < 0 := by
  refine ⟨by simp, ?_, by linarith⟩
  exact (((Real.hasDerivAt_sin 0).const_mul K).const_sub 0).congr_deriv (by simp)

end UEF.Tunneling
