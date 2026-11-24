/-
  THE UNIFIED EXISTENCE FRAMEWORK — No field evolves alone, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, §5.2 (p. 126) and evidence Lemma 6.1:
  the cross-coupled kinetic mass matrix m_ab = m_aδ_ab + κ_ab is positive definite
  under the diagonal dominance condition, and the connected coupling graph prevents
  a nontrivial partition of the seven fields into independently evolving blocks.
-/
import Mathlib

open Finset

namespace UEF.Coupling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Σ_{b≠a} |m_ab|: the couplings of field a to every other field. -/
def offRow (M : Matrix ι ι ℝ) (a : ι) : ℝ := ∑ b, if b = a then 0 else |M a b|

/-- The kinetic energy T(v) = Σ_ab m_ab v_a v_b (twice the usual ½). -/
def T (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := ∑ a, ∑ b, M a b * v a * v b

theorem pair_bound (m x y : ℝ) : -(|m| * (x ^ 2 + y ^ 2) / 2) ≤ m * x * y := by
  have hxy : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have h1 : |m * x * y| ≤ |m| * (x ^ 2 + y ^ 2) / 2 := by
    rw [abs_mul, abs_mul, mul_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hxy (abs_nonneg m)
  linarith [neg_abs_le (m * x * y)]

/-- Each row split into its diagonal term and its couplings. -/
theorem row_split (f : ι → ℝ) (a : ι) :
    ∑ b, f b = f a + ∑ b, (if b = a then 0 else f b) := by
  have : ∀ b, f b = (if b = a then f b else 0) + (if b = a then 0 else f b) := by
    intro b; split_ifs <;> simp
  conv_lhs => rw [Finset.sum_congr rfl fun b _ => this b]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ a f]
  simp

/-- T(v) ≥ Σ_a (m_a − Σ_{b≠a} |m_ab|) v_a². -/
theorem T_lower (M : Matrix ι ι ℝ) (hsym : ∀ a b, M a b = M b a) (v : ι → ℝ) :
    ∑ a, (M a a - offRow M a) * v a ^ 2 ≤ T M v := by
  unfold T
  have hrow : ∀ a, ∑ b, M a b * v a * v b
      = M a a * v a ^ 2 + ∑ b, (if b = a then 0 else M a b * v a * v b) := by
    intro a
    rw [row_split (fun b => M a b * v a * v b) a]
    ring
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  -- the couplings are bounded below, pair by pair
  have hoff : ∑ a, ∑ b, (if b = a then (0 : ℝ) else -(|M a b| * (v a ^ 2 + v b ^ 2) / 2))
      ≤ ∑ a, ∑ b, (if b = a then 0 else M a b * v a * v b) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    split_ifs
    · exact le_refl _
    · exact pair_bound _ _ _
  -- and by symmetry the bound is −Σ_a (Σ_{b≠a} |m_ab|) v_a²
  have hsplit : ∀ a b, (if b = a then (0 : ℝ) else -(|M a b| * (v a ^ 2 + v b ^ 2) / 2))
      = -((if b = a then 0 else |M a b| * v a ^ 2) / 2) - (if b = a then 0 else |M a b| * v b ^ 2) / 2 := by
    intro a b; split_ifs <;> ring
  have hswap : ∑ a, ∑ b, (if b = a then (0 : ℝ) else |M a b| * v b ^ 2)
      = ∑ a, ∑ b, (if b = a then 0 else |M a b| * v a ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), hsym b a]
  have hrows : ∀ a, ∑ b, (if b = a then (0 : ℝ) else |M a b| * v a ^ 2) = offRow M a * v a ^ 2 := by
    intro a
    unfold offRow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hbound : ∑ a, ∑ b, (if b = a then (0 : ℝ) else -(|M a b| * (v a ^ 2 + v b ^ 2) / 2))
      = -∑ a, offRow M a * v a ^ 2 := by
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_div, hswap, hrows]
    ring
  rw [hbound] at hoff
  have : ∑ a, (M a a - offRow M a) * v a ^ 2 = ∑ a, M a a * v a ^ 2 - ∑ a, offRow M a * v a ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [this]
  linarith

/-- Lemma 6.1 (i) — Positive definite. Every m_a > Σ_{b≠a} |κ_ab|: T > 0 for every
    non-zero velocity. -/
theorem positive_definite (M : Matrix ι ι ℝ) (hsym : ∀ a b, M a b = M b a)
    (dominant : ∀ a, offRow M a < M a a) (v : ι → ℝ) (hv : v ≠ 0) : 0 < T M v := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  have hpos : 0 < ∑ a, (M a a - offRow M a) * v a ^ 2 := by
    apply Finset.sum_pos'
    · intro b _
      exact mul_nonneg (by linarith [dominant b]) (sq_nonneg _)
    · exact ⟨a, mem_univ a, mul_pos (by linarith [dominant a]) (by positivity)⟩
  exact lt_of_lt_of_le hpos (T_lower M hsym v)

/-- The coupling graph: an edge between a and b whenever κ_ab ≠ 0. -/
def couplingGraph (M : Matrix ι ι ℝ) : SimpleGraph ι where
  Adj a b := a ≠ b ∧ (M a b ≠ 0 ∨ M b a ≠ 0)
  symm _ _ h := ⟨Ne.symm h.1, h.2.symm⟩
  loopless _ h := h.1 rfl

/-- Lemma 6.1 (ii) — The kinetic energy does not split. For every splitting of the
    fields into two non-empty groups J and J′, the coupling graph is connected, so
    some edge joins J to J′: there are a ∈ J, b ∈ J′ with κ_ab ≠ 0. -/
theorem no_split (M : Matrix ι ι ℝ) (hsym : ∀ a b, M a b = M b a)
    (connected : (couplingGraph M).Connected) (J : Set ι) {a b : ι} (ha : a ∈ J) (hb : b ∉ J) :
    ∃ a' ∈ J, ∃ b' ∉ J, M a' b' ≠ 0 := by
  obtain ⟨p⟩ := connected.preconnected a b
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart J ha hb
  refine ⟨d.fst, hd1, d.snd, hd2, ?_⟩
  rcases d.adj.2 with h | h
  · exact h
  · rwa [hsym]

end UEF.Coupling
