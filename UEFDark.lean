/-
  THE UNIFIED EXISTENCE FRAMEWORK — Chapter 12, in Lean 4 with Mathlib
  The Dark Sector as the Ontological Substrate

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Chapter 12: Definitions 1.1–1.2, Theorems 1–5, and 12.4.
  All arithmetic is exact (ℚ and ℝ). There is no floating point anywhere.
-/
import Mathlib

open MeasureTheory

namespace UEF.Dark

variable {Ω : Type*}

/-! ## Definition 1.2 — the realized domain and the dark sector -/

/-- R := { x ∈ Ω | C_λ(x) = x }: the states the Collapse Interface Operator leaves fixed. -/
def realized (C : Ω → Ω) : Set Ω := {x | C x = x}

/-- Ω_dark := { x ∈ Ω | C_λ(x) ≠ x }: the uncollapsed potential. -/
def dark (C : Ω → Ω) : Set Ω := {x | C x ≠ x}

theorem dark_eq_compl (C : Ω → Ω) : dark C = (realized C)ᶜ := Set.ext fun _ => Iff.rfl

/-- Ω = R ∪ Ω_dark and R ∩ Ω_dark = ∅: mutually exclusive and exhaustive. -/
theorem partition (C : Ω → Ω) : realized C ∪ dark C = Set.univ ∧ realized C ∩ dark C = ∅ := by
  rw [dark_eq_compl]
  exact ⟨Set.union_compl_self _, Set.inter_compl_self _⟩

/-- Ω_dark = ∅ exactly when R = Ω. -/
theorem dark_empty_iff (C : Ω → Ω) : dark C = ∅ ↔ realized C = Set.univ := by
  rw [dark_eq_compl]
  exact Set.compl_empty_iff

/-- R is closed and Ω_dark is open, for a continuous collapse operator on a Hausdorff space. -/
theorem realized_closed [TopologicalSpace Ω] [T2Space Ω] {C : Ω → Ω} (hC : Continuous C) :
    IsClosed (realized C) :=
  isClosed_eq hC continuous_id

theorem dark_open [TopologicalSpace Ω] [T2Space Ω] {C : Ω → Ω} (hC : Continuous C) :
    IsOpen (dark C) := by
  rw [dark_eq_compl]
  exact (realized_closed hC).isOpen_compl

/-! ## Theorem 1 — the ontological substrate -/

/-- ∂R = R̄ ∩ Ω̄_dark, the interface between collapsed reality and uncollapsed potential. -/
def interface [TopologicalSpace Ω] (C : Ω → Ω) : Set Ω := closure (realized C) ∩ closure (dark C)

/-- Step 4 — with no uncollapsed potential the interface vanishes: Ω_dark = ∅ ⟹ ∂R = ∅. -/
theorem interface_empty [TopologicalSpace Ω] (C : Ω → Ω) (h : dark C = ∅) : interface C = ∅ := by
  simp [interface, h]

/-- Step 6 — a non-empty interface needs a strictly positive measure of uncollapsed potential:
    μ(Ω_dark) > 0, for any measure that charges open sets. -/
theorem dark_measure_pos [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] (μ : Measure Ω)
    [μ.IsOpenPosMeasure] {C : Ω → Ω} (hC : Continuous C) (h : (interface C).Nonempty) :
    0 < μ (dark C) := by
  apply (dark_open hC).measure_pos μ
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [interface_empty C hne] at h
  exact Set.not_nonempty_empty h

/-! ## Theorem 2 — no gauge coupling to the dark sector -/

/-- Step 4 — a gauge coupling defined over the realized domain has no term between realized
    matter and the dark sector: L_gauge[R, Ω_dark] = 0. -/
theorem no_gauge_coupling {C : Ω → Ω} (L : Ω → Ω → ℝ)
    (supp : ∀ x y, L x y ≠ 0 → x ∈ realized C ∧ y ∈ realized C) {x y : Ω} (hy : y ∈ dark C) :
    L x y = 0 := by
  by_contra h
  exact (show C y ≠ y from hy) (supp x y h).2

/-! ## Theorem 3 — the dark sector gravitates -/

/-- Step 1 — the action splits over the partition: ∫_Ω L = ∫_R L + ∫_{Ω_dark} L. -/
theorem action_splits [MeasurableSpace Ω] (μ : Measure Ω) {C : Ω → Ω}
    (hR : MeasurableSet (realized C)) (L : Ω → ℝ) (hL : Integrable L μ) :
    ∫ x, L x ∂μ = (∫ x in realized C, L x ∂μ) + ∫ x in dark C, L x ∂μ := by
  rw [dark_eq_compl]
  exact (integral_add_compl hR hL).symm

/-- Step 6 (E38) — with η = μ(R)/μ(Ω), the dark-to-visible ratio is (1 − η)/η. -/
theorem dark_ratio (mR mΩ : ℝ) (hR : 0 < mR) (hΩ : 0 < mΩ) :
    (mΩ - mR) / mR = (1 - mR / mΩ) / (mR / mΩ) := by
  field_simp

/-- E38 for a finite measure: μ(Ω ∖ R)/μ(R) = (1 − η)/η. -/
theorem dark_ratio_measure [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {C : Ω → Ω}
    (hR : MeasurableSet (realized C)) (hpos : 0 < (μ (realized C)).toReal) :
    (μ (dark C)).toReal / (μ (realized C)).toReal
      = (1 - (μ (realized C)).toReal / (μ Set.univ).toReal)
          / ((μ (realized C)).toReal / (μ Set.univ).toReal) := by
  have hle : μ (realized C) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  have hc : (μ (dark C)).toReal = (μ Set.univ).toReal - (μ (realized C)).toReal := by
    rw [dark_eq_compl, measure_compl hR (measure_ne_top μ _),
      ENNReal.toReal_sub_of_le hle (measure_ne_top μ _)]
  have hU : 0 < (μ Set.univ).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top μ _) hle)
  rw [hc]
  exact dark_ratio _ _ hpos hU

/-- The finite model Ω = {1, …, N}, R = {1, …, k}: the ratio is (1 − k/N)/(k/N). -/
theorem finite_model (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    ((N - k : ℕ) : ℚ) / k = (1 - (k : ℚ) / N) / ((k : ℚ) / N) := by
  have hN : (0 : ℚ) < N := by exact_mod_cast lt_of_lt_of_le hk hkN
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  rw [Nat.cast_sub hkN]
  field_simp

/-- Theorem 3, Step 6 — η = 156/1000 gives (1 − η)/η = 844/156 = 211/39. -/
theorem ratio_156 : (1 - (156 : ℚ) / 1000) / (156 / 1000) = 211 / 39 := by norm_num

theorem ratio_844 : (844 : ℚ) / 156 = 211 / 39 := by norm_num

/-- 12.4 — Planck 2018: Ω_c h² = 120/1000 against Ω_b h² = 224/10000, a ratio of 75/14. -/
theorem planck_ratio : ((120 : ℚ) / 1000) / (224 / 10000) = 75 / 14 := by norm_num

/-- 12.4 — (1 − η)/η = 75/14 holds exactly at η = 14/89. -/
theorem eta_planck (η : ℚ) (h : η ≠ 0) : (1 - η) / η = 75 / 14 ↔ η = 14 / 89 := by
  constructor
  · intro e
    rw [div_eq_div_iff h (by norm_num)] at e
    linarith
  · rintro rfl
    norm_num

/-- 12.4 — dark matter is 75/89 of all matter. -/
theorem dark_fraction : 1 - (14 : ℚ) / 89 = 75 / 89 := by norm_num

/-- Chapter 12 states two values of η: 156/1000 (Theorem 3, Step 5) and 14/89 (12.4).
    They are not equal, and neither are the ratios they give. -/
theorem eta_values_differ : (156 : ℚ) / 1000 ≠ 14 / 89 := by norm_num

theorem ratios_differ : (211 : ℚ) / 39 ≠ 75 / 14 := by norm_num

/-! ## Theorem 4 — ε₀, μ₀ and c -/

/-- Steps 4–6 — μ₀ = 1/(m_S V), ε₀ = k_S V/c² and c = 1/√(ε₀μ₀) hold together exactly when
    k_S = m_S: the units the manuscript sets for Theorems 4 and 5. -/
theorem units_forced (mS kS V c : ℝ) (hm : 0 < mS) (hk : 0 < kS) (hV : 0 < V) (hc : 0 < c) :
    c = 1 / Real.sqrt ((kS * V / c ^ 2) * (1 / (mS * V))) ↔ kS = mS := by
  have e : (kS * V / c ^ 2) * (1 / (mS * V)) = (Real.sqrt (kS / mS) / c) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (div_pos hk hm).le]
    field_simp
    ring
  have hs : 0 < Real.sqrt (kS / mS) := Real.sqrt_pos.mpr (div_pos hk hm)
  rw [e, Real.sqrt_sq (div_pos hs hc).le, one_div_div]
  constructor
  · intro h
    rw [eq_div_iff hs.ne'] at h
    have h1 : Real.sqrt (kS / mS) = 1 := mul_left_cancel₀ hc.ne' (h.trans (mul_one c).symm)
    have h2 : kS / mS = 1 := by
      have := Real.sq_sqrt (div_pos hk hm).le
      rw [h1, one_pow] at this
      exact this.symm
    rwa [div_eq_one_iff_eq hm.ne'] at h2
  · intro h
    rw [h, div_self hm.ne', Real.sqrt_one, div_one]

/-- Step 6 — in those units c = √(k_S/m_S) = 1. -/
theorem c_is_one (m : ℝ) (hm : 0 < m) : Real.sqrt (m / m) = 1 := by
  rw [div_self hm.ne', Real.sqrt_one]

/-- Step 7 — in those units Z₀ = √(μ₀/ε₀) = 1/(V√(m_S k_S)) = μ₀c. -/
theorem impedance (m V : ℝ) (hm : 0 < m) (hV : 0 < V) :
    Real.sqrt ((1 / (m * V)) / (m * V / 1 ^ 2)) = 1 / (V * Real.sqrt (m * m)) ∧
      1 / (V * Real.sqrt (m * m)) = 1 / (m * V) * 1 := by
  rw [Real.sqrt_mul_self hm.le]
  refine ⟨?_, by ring⟩
  rw [show (1 / (m * V)) / (m * V / 1 ^ 2) = (1 / (m * V)) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  ring

/-- Step 7 — the stated value: μ₀c = 4709128920835668637/12500000000000000 Ω, with
    μ₀ = 125663706212 × 10⁻¹⁷ N/A² and c = 299792458 m/s, exactly. -/
theorem impedance_value :
    (125663706212 / 10 ^ 17 : ℚ) * 299792458 = 4709128920835668637 / 12500000000000000 := by
  norm_num

/-! ## Theorem 5 — depletion -/

/-- Steps 1–2 — collapsed states never un-collapse, R(t₁) ⊆ R(t₂) for t₁ ≤ t₂, so the measure
    of the dark sector only decreases. -/
theorem depletion [MeasurableSpace Ω] (μ : Measure Ω) (R : ℝ → Set Ω) (mono : Monotone R) :
    Antitone fun t => μ (R t)ᶜ :=
  fun _ _ h => measure_mono (Set.compl_subset_compl.mpr (mono h))

/-- Step 3 — Λ_eff = (8πG/c²)ρ_dark decreases with the dark density. -/
theorem lambda_decreases (κ : ℝ) (hκ : 0 ≤ κ) (ρ : ℝ → ℝ) (h : Antitone ρ) :
    Antitone fun t => κ * ρ t :=
  fun _ _ hst => mul_le_mul_of_nonneg_left (h hst) hκ

end UEF.Dark
