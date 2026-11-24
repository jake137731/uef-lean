/-
  THE UNIFIED EXISTENCE FRAMEWORK — A4 through the divergence theorem (E32), in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, §4.5.3, A4.3–A4.5 [P]: local conservation
  is zero net flux of Sᵃ through the boundary of every region; by the divergence
  theorem (E32) the integral of ∇ₐSᵃ over the region is zero; by localization
  ∇ₐSᵃ = 0 at every point. Here E32 is Mathlib's divergence theorem, proved, not cited.
-/
import Mathlib
import UEFRoots

open MeasureTheory Set Finset

namespace UEF.Gauss

variable {n : ℕ}

/-- ∇ₐSᵃ: the divergence of the current S. -/
noncomputable def div (S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, fderiv ℝ S x (Pi.single i 1) i

/-- The net flux of S out of the box [a, b], through each pair of opposite faces. -/
noncomputable def flux (S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (a b : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i), S (Fin.insertNth i (b i) x) i) -
      ∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i), S (Fin.insertNth i (a i) x) i)

theorem div_continuous (S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (hS : ContDiff ℝ 1 S) :
    Continuous (div S) := by
  unfold div
  refine continuous_finset_sum _ fun i _ => ?_
  have h := hS.continuous_fderiv le_rfl
  exact (continuous_apply i).comp ((h.clm_apply continuous_const))

/-- E32 [P] — The divergence theorem (Gauss): the integral of ∇ₐSᵃ over a box is the
    net flux of S through its boundary. -/
theorem E32 (S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (hS : ContDiff ℝ 1 S)
    (a b : Fin (n + 1) → ℝ) (hle : a ≤ b) :
    ∫ x in Icc a b, div S x = flux S a b := by
  have hd : ∀ x, HasFDerivAt S (fderiv ℝ S x) x :=
    fun x => ((hS.differentiable le_rfl) x).hasFDerivAt
  exact integral_divergence_of_hasFDerivWithinAt_off_countable a b hle S (fun x => fderiv ℝ S x)
    ∅ countable_empty hS.continuous.continuousOn (fun x _ => hd x)
    ((div_continuous S hS).continuousOn.integrableOn_compact isCompact_Icc)

/-- Localization: a continuous function that is positive at a point has a box around
    the point on which its integral is positive. -/
theorem box_pos (g : (Fin (n + 1) → ℝ) → ℝ) (hg : Continuous g) (x₀ : Fin (n + 1) → ℝ)
    (hpos : 0 < g x₀) : ∃ a b, a ≤ b ∧ 0 < ∫ x in Icc a b, g x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := x₀)) (g x₀ / 2) (by linarith)
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set a : Fin (n + 1) → ℝ := fun i => x₀ i - ε
  set b : Fin (n + 1) → ℝ := fun i => x₀ i + ε
  have hab : a ≤ b := fun i => by simp only [a, b]; linarith
  have hsub : ∀ y ∈ Icc a b, g x₀ / 2 ≤ g y := by
    intro y hy
    have hd : dist y x₀ ≤ ε := (dist_pi_le_iff hε0.le).mpr fun i => by
      have h1 := hy.1 i
      have h2 := hy.2 i
      simp only [a, b] at h1 h2
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    have := hball (lt_of_le_of_lt hd (by linarith))
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hvol : 0 < (volume (Icc a b)).toReal := by
    rw [Real.volume_Icc_pi, ENNReal.toReal_prod]
    apply Finset.prod_pos
    intro i _
    simp only [a, b]
    rw [ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hge := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (isCompact_Icc.measure_lt_top).ne hsub (hg.continuousOn.integrableOn_compact isCompact_Icc)
  exact ⟨a, b, hab, lt_of_lt_of_le (mul_pos (by linarith) hvol) hge⟩

/-- Lemma 4 [P] (A4.4–A4.5) — A continuous function whose integral over every box is
    zero is zero at every point. -/
theorem zero_of_box_integrals (g : (Fin (n + 1) → ℝ) → ℝ) (hg : Continuous g)
    (h : ∀ a b, a ≤ b → ∫ x in Icc a b, g x = 0) : g = 0 := by
  funext x₀
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨a, b, hab, hpos⟩ := box_pos (fun x => -g x) hg.neg x₀ (by simp at hlt ⊢; linarith)
    rw [integral_neg, h a b hab] at hpos
    simp at hpos
  · obtain ⟨a, b, hab, hpos⟩ := box_pos g hg x₀ hgt
    rw [h a b hab] at hpos
    exact lt_irrefl 0 hpos

/-- A4 [P] — div S = ∇ₐSᵃ = 0. Local conservation is zero net flux of Sᵃ through the
    boundary of every box (A4.2–A4.3); by the divergence theorem (E32) the integral of
    ∇ₐSᵃ over every box is zero; by localization (A4.4) ∇ₐSᵃ = 0 at every point (A4.5). -/
theorem A4 (S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (hS : ContDiff ℝ 1 S)
    (conserved : ∀ a b, a ≤ b → flux S a b = 0) : div S = 0 :=
  zero_of_box_integrals (div S) (div_continuous S hS)
    fun a b hab => (E32 S hS a b hab).trans (conserved a b hab)

/-! ## A4.2 [P] — the charge of the phase symmetry is conserved -/

/-- A4.2 [P] — A state is a ray (E10): x and e^{iα}x are the same state. Every
    observable reads the same on both: the dynamics is invariant under the phase α. -/
theorem phase_invariant {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (O : ℋ →L[ℂ] ℋ) (x : ℋ) (α : ℝ) :
    inner (Complex.exp (α * Complex.I) • x) (O (Complex.exp (α * Complex.I) • x)) =
      (inner x (O x) : ℂ) := by
  have h : (starRingEnd ℂ) (Complex.exp (α * Complex.I)) * Complex.exp (α * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, h, one_mul]

/-- A4.2 [P] — The charge of the phase symmetry is the norm ⟨x, x⟩ (E9), and unitary
    evolution keeps it (E6, E27): under iψ′ = Hψ with H Hermitian, Σᵢ|ψᵢ|² is the same
    at every time. The current of that symmetry is conserved on solutions. -/
theorem charge_conserved {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ψ : ℝ → ι → ℂ)
    (schrodinger : ∀ t i, HasDerivAt (fun s => ψ s i) (-Complex.I * ∑ j, H i j * ψ t j) t)
    (t₀ t : ℝ) : ∑ i, Complex.normSq (ψ t i) = ∑ i, Complex.normSq (ψ t₀ i) := by
  simp only [Complex.normSq_eq_norm_sq]
  have hd : ∀ s, HasDerivAt (fun s => ∑ i, ‖ψ s i‖ ^ 2)
      (∑ i, 2 * inner (ψ s i) (-Complex.I * ∑ j, H i j * ψ s j)) s := by
    intro s
    have := HasDerivAt.sum (u := Finset.univ) fun i _ => (schrodinger s i).norm_sq
    simpa using this
  have hzero : ∀ s, ∑ i, (2 : ℝ) * inner (ψ s i) (-Complex.I * ∑ j, H i j * ψ s j) = 0 := by
    intro s
    have := UEF.Roots.conservation H hH (ψ s)
    simpa [Complex.inner, Complex.star_def] using this
  have hconst := is_const_of_deriv_eq_zero (f := fun s => ∑ i, ‖ψ s i‖ ^ 2)
    (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, hzero s])
  exact hconst t t₀

end UEF.Gauss
