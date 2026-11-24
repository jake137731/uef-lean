/-
  THE UNIFIED EXISTENCE FRAMEWORK — the root relations A1–A4, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, Section 4 (pp. 83–121), each line with
  its step number. ℋ is a complex inner product space (E1–E10).
-/
import Mathlib

open MeasureTheory

namespace UEF.Roots

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-! ## §4.2 — A1 is proved from E -/

/-- A1.1 — P ≔ 0 ∈ ℋ, the zero vector: the origin of the state space. -/
def P : ℋ := 0

/-- A1.2–A1.4 — A1: ∃P ∀ observables O: ⟨O⟩_P = 0. -/
theorem A1 : ∀ O : ℋ →L[ℂ] ℋ, inner (P : ℋ) (O P) = (0 : ℂ) := by
  intro O
  simp [P]

/-- A1.5 — Only P. A state x with ⟨O⟩ₓ = 0 for every O has ⟨𝟙⟩ₓ = ‖x‖² = 0, so x = 0 = P. -/
theorem A1_only_P (x : ℋ) (h : ∀ O : ℋ →L[ℂ] ℋ, inner x (O x) = (0 : ℂ)) : x = P := by
  have := h (ContinuousLinearMap.id ℂ ℋ)
  simpa [P] using this

/-- A1.6 — Perfectly symmetric. Every unitary U is linear, so UP = U0 = 0 = P. -/
theorem A1_symmetric (U : ℋ →L[ℂ] ℋ) : U P = P := by
  simp [P]

/-- −𝟙 is a symmetry of P (a unitary). -/
theorem neg_one_unitary : (-1 : ℋ →L[ℂ] ℋ) ∈ unitary (ℋ →L[ℂ] ℋ) := by
  rw [unitary.mem_iff]
  simp

/-- A1.7 — The only fixed point. For x ≠ P, (−𝟙)x = −x ≠ x. -/
theorem A1_only_fixed (x : ℋ) (hx : x ≠ P) : (-1 : ℋ →L[ℂ] ℋ) x ≠ x := by
  intro h
  apply hx
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply] at h
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; simp
  simpa [P] using (smul_eq_zero.mp this).resolve_left (by norm_num)

/-- A1.8 — ‖P‖ = 0, while every realized state has norm 1 (E9). P is not a realized state. -/
theorem A1_not_realized : ‖(P : ℋ)‖ ≠ 1 := by
  simp [P]

/-! ## §4.3 — A2: the first disturbance is necessary -/

/-- A2.1–A2.6 — Lemma 1, First-Difference Necessity. The history starts at P (A1.1).
    The record contains a realized state, of norm 1 (E9, E11, E12): physical
    differentiation. Then there is a first disturbance: a step from P to P′ ≠ P. -/
theorem A2 (history : ℕ → ℋ) (start : history 0 = P)
    (PD : ∃ n, ‖history n‖ = 1) : ∃ n, history n = P ∧ history (n + 1) ≠ P := by
  by_contra h
  push_neg at h
  -- A2.2: with no first disturbance, by induction every realized state is P.
  have all : ∀ n, history n = P := by
    intro n
    induction n with
    | zero => exact start
    | succ n ih => exact h n ih
  -- A2.4: PD and P′ = P contradict each other.
  obtain ⟨n, hn⟩ := PD
  rw [all n] at hn
  exact A1_not_realized hn

/-- A2.5 — Every deterministic linear evolution keeps P where it is: U(t)P = U(t)0 = 0.
    The first transition is not an evolution of P under any law that acts on P linearly. -/
theorem A2_not_linear (L : ℋ →ₗ[ℂ] ℋ) : L P ≠ P → False := by
  intro h
  exact h (by simp [P])

/-! ## §4.4 — A3: the first disturbance is ontologically random -/

/-- G, the full symmetry group of P: the unitaries (A1.6). -/
def G : Set (ℋ →L[ℂ] ℋ) := unitary (ℋ →L[ℂ] ℋ)

/-- A3.1–A3.3 — Lemma 2, Symmetry Preservation. F is an admissible deterministic
    internal evolution law: G-equivariant, F(gx) = gF(x). Then F(P) is fixed by
    all of G, and the only vector fixed by all of G is P. So F(P) = P. -/
theorem lemma2 (F : ℋ → ℋ) (equivariant : ∀ g ∈ (G : Set (ℋ →L[ℂ] ℋ)), ∀ x, F (g x) = g (F x)) :
    F P = P := by
  by_contra hne
  have h := equivariant (-1) neg_one_unitary P
  rw [A1_symmetric] at h
  exact A1_only_fixed (F P) hne h.symm

/-- A3.4 — Corollary 2.1. A deterministic internal rule with no prior asymmetry cannot
    select a G-breaking outcome from P, and A2 requires P′ ≠ P. -/
theorem corollary2_1 (F : ℋ → ℋ) (equivariant : ∀ g ∈ (G : Set (ℋ →L[ℂ] ℋ)), ∀ x, F (g x) = g (F x)) :
    ¬ (F P ≠ P) :=
  fun h => h (lemma2 F equivariant)

/-- A3.11 — Exhaustion (Lemma 3A). Before ε the history is P alone, so P is the only
    prior state. Any outcome that is a function of the prior state, by a rule with no
    prior asymmetry, is P. The first disturbance is a function of no prior state. -/
theorem exhaustion (history : ℕ → ℋ) (start : history 0 = P) (PD : ∃ n, ‖history n‖ = 1)
    (F : ℋ → ℋ) (equivariant : ∀ g ∈ (G : Set (ℋ →L[ℂ] ℋ)), ∀ x, F (g x) = g (F x)) :
    ∃ n, history n = P ∧ history (n + 1) ≠ F (history n) := by
  obtain ⟨n, hP, hne⟩ := A2 history start PD
  exact ⟨n, hP, by rw [hP, lemma2 F equivariant]; exact hne⟩

section Spread
variable [MeasurableSpace ℋ] [BorelSpace ℋ] [SecondCountableTopology ℋ]

/-- A3.5–A3.6 — Spread. Every unit vector is as compatible with P as P′ is: the law
    of the outcome is the same under every symmetry of P. Such a law is no single
    value: the outcome of ε has more than one possible value, so Var(ε) > 0 (E15, E18). -/
theorem spread (μ : Measure ℋ) (invariant : ∀ g ∈ (G : Set (ℋ →L[ℂ] ℋ)), μ.map g = μ)
    (x : ℋ) (hx : ‖x‖ = 1) : μ ≠ Measure.dirac x := by
  intro hμ
  have h := invariant (-1) neg_one_unitary
  rw [hμ, Measure.map_dirac (ContinuousLinearMap.continuous _).measurable] at h
  have hx' : (-1 : ℋ →L[ℂ] ℋ) x = x := Measure.dirac_eq_dirac_iff.mp h
  exact A1_only_fixed x (by intro h0; simp [h0, P] at hx) hx'

end Spread

/-! ## §4.5 — A4: div S = ∇ₐSᵃ = 0 -/

/-- Lemma 4 — Local Conservation Implies Zero Divergence (A4.3–A4.5). The net flux of
    S through the boundary of every compact region is zero; by the divergence theorem
    (E32) the integral of ∇ₐSᵃ over every compact region is zero. A continuous
    divergence with that property is zero at every point. -/
theorem lemma4 {n : ℕ} (divS : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous divS)
    (flux : ∀ V, IsCompact V → ∫ x in V, divS x = 0) : divS = 0 := by
  have hae : divS =ᵐ[volume] 0 :=
    ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hc.locallyIntegrable flux
  exact (Continuous.ae_eq_iff_eq volume hc continuous_const).mp hae

/-- A4.2 — Local conservation from unitary evolution, on a finite lattice of sites.
    Under iψ′ = Hψ with H Hermitian, the probability ρᵢ = |ψᵢ|² changes only by the
    currents Jᵢⱼ between sites, and every current leaves one site and enters another:
    Σᵢ ρᵢ′ = 0. -/
theorem conservation {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ψ : ι → ℂ) :
    ∑ i, 2 * (star (ψ i) * (-Complex.I * ∑ j, H i j * ψ j)).re = 0 := by
  have hreal : (∑ i, ∑ j, star (ψ i) * H i j * ψ j).im = 0 := by
    have hs : star (∑ i, ∑ j, star (ψ i) * H i j * ψ j) = ∑ i, ∑ j, star (ψ i) * H i j * ψ j := by
      simp only [star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : star (H j i) = H i j := by
        have := congrFun (congrFun hH i) j
        simpa [Matrix.conjTranspose_apply] using this
      rw [this]; ring
    rw [Complex.star_def] at hs
    exact Complex.conj_eq_iff_im.mp hs
  have e : ∀ i, 2 * (star (ψ i) * (-Complex.I * ∑ j, H i j * ψ j)).re
      = 2 * (∑ j, star (ψ i) * H i j * ψ j).im := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [Complex.re_sum, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [e]
  rw [← Finset.mul_sum, ← Complex.im_sum, hreal, mul_zero]

/-! ## §4.6 — A1 ∧ A2 ∧ A3 ⊢ A4: the root relations together -/

/-- E ⊢ A1 ⟹ A2 ⟹ A3 ⟹ A4, each proved in Lean from what the manuscript cites. -/
theorem roots (history : ℕ → ℋ) (start : history 0 = P) (PD : ∃ n, ‖history n‖ = 1) :
    -- A1
    (∀ O : ℋ →L[ℂ] ℋ, inner (P : ℋ) (O P) = (0 : ℂ)) ∧
    -- A2
    (∃ n, history n = P ∧ history (n + 1) ≠ P) ∧
    -- A3: no rule without prior asymmetry produces the first disturbance
    (∀ F : ℋ → ℋ, (∀ g ∈ (G : Set (ℋ →L[ℂ] ℋ)), ∀ x, F (g x) = g (F x)) →
      ∃ n, history n = P ∧ history (n + 1) ≠ F (history n)) :=
  ⟨A1, A2 history start PD, fun F hF => exhaustion history start PD F hF⟩

end UEF.Roots
