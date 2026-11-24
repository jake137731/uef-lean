/-
  THE UNIFIED EXISTENCE FRAMEWORK: THE LAW OF RECIPROCITY
  AND THE RECIPROCAL EXISTENCE THEOREM — in Lean 4

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf and S8_One_Equation_Compression.pdf.
  Every equation is the manuscript's, with its section, page and line.

  Lean 4.15.0, core library only: no Mathlib, no axioms added, no `sorry`.
  Arithmetic is exact (integers); no floating point anywhere.

  There is no closure operator here. Derivability is G12, a finite derivation
  from premises under the stated inference rules, and Th(X) is the set of
  statements derivable from X. Its properties E29 and E30 are not put into it
  by definition: each is proved below from what a derivation is. Everything
  after that is the Law of Reciprocity.
-/

namespace UEF

universe u

/-! ## Section 2 — G1, G11, G12 -/

/-- G11 — Statements are the sentences of one formal language `S`.
    G1 — A set of statements is given by its membership. -/
abbrev Stmts (S : Type u) := S → Prop

variable {S : Type u}

instance : HasSubset (Stmts S) := ⟨fun X Y => ∀ φ, X φ → Y φ⟩

/-- Extensionality (G1): sets with the same members are equal. -/
theorem ext {X Y : Stmts S} (h₁ : X ⊆ Y) (h₂ : Y ⊆ X) : X = Y :=
  funext fun φ => propext ⟨h₁ φ, h₂ φ⟩

theorem sub_refl (X : Stmts S) : X ⊆ X := fun _ h => h

theorem sub_trans {X Y Z : Stmts S} (h₁ : X ⊆ Y) (h₂ : Y ⊆ Z) : X ⊆ Z :=
  fun φ h => h₂ φ (h₁ φ h)

/-- An inference rule: finitely many premises and one conclusion. -/
structure Rule (S : Type u) where
  premises : List S
  conclusion : S

/-- G12 — Derivability. `Derives R Γ φ`: a finite derivation of `φ` exists from
    premises `Γ` under the inference rules `R`. A derivation is either a premise
    or one rule of `R` applied to statements already derived. -/
inductive Derives (R : Rule S → Prop) (Γ : Stmts S) : S → Prop
  | premise {φ : S} : Γ φ → Derives R Γ φ
  | infer (r : Rule S) : R r → (∀ p, p ∈ r.premises → Derives R Γ p) → Derives R Γ r.conclusion

variable (R : Rule S → Prop)

/-- Th(X): the statements derivable from `X` (written Cn(X) in E29 and E30). -/
def Th (X : Stmts S) : Stmts S := fun φ => Derives R X φ

/-- E29 — Every member of a theory is derivable from it: X ⊆ Cn(X).
    (Tarski; MIT 24.241) Proved: a premise is a derivation. -/
theorem E29 (X : Stmts S) : X ⊆ Th R X :=
  fun _ h => Derives.premise h

/-- Substitution of derivations: whatever is derivable from statements that are
    each derivable from `X` is derivable from `X`. -/
theorem substitute {X Y : Stmts S} (hY : Y ⊆ Th R X) :
    ∀ {φ}, Derives R Y φ → Derives R X φ := by
  intro φ d
  induction d with
  | premise h => exact hY _ h
  | infer r hr _ ih => exact Derives.infer r hr ih

/-- Monotonicity: X ⊆ Y ⟹ Th(X) ⊆ Th(Y). Proved: a derivation from `X` is a
    derivation from any `Y` containing `X`. -/
theorem mono {X Y : Stmts S} (h : X ⊆ Y) : Th R X ⊆ Th R Y :=
  fun _ d => substitute R (sub_trans h (E29 R Y)) d

/-- E30 — Cut: Cn(Cn(X)) = Cn(X). (Tarski 1930; Gentzen; MIT 24.241)
    Proved: substituting derivations. -/
theorem E30 (X : Stmts S) : Th R (Th R X) = Th R X :=
  ext (fun _ d => substitute R (sub_refl _) d) (E29 R (Th R X))

/-- §6.1, p. 128, l. 2757: X ⊆ Th(X), Th(Th(X)) = Th(X), X ⊆ Y ⟹ Th(X) ⊆ Th(Y). -/
theorem derivability (X Y : Stmts S) :
    X ⊆ Th R X ∧ Th R (Th R X) = Th R X ∧ (X ⊆ Y → Th R X ⊆ Th R Y) :=
  ⟨E29 R X, E30 R X, mono R⟩

/-- For sets of statements T and S, T ⊢ S means S ⊆ Th(T). (§6.1) -/
def Proves (T U : Stmts S) : Prop := U ⊆ Th R T

/-- A theory is a set T with T = Th(T). (§6.1) -/
def IsTheory (T : Stmts S) : Prop := T = Th R T

/-- E ≡ U :⟺ (E ⊢ U) ∧ (U ⊢ E). (§6.4, p. 131, l. 2822) Deductive equivalence
    (G12): derivability in both directions. -/
def Reciprocal (E U : Stmts S) : Prop := Proves R E U ∧ Proves R U E

/-! ## Theorem 3.15.1 — The Law of Reciprocity -/

/-- Theorem 3.15.1 — Deductive reciprocity.
    [(∀u ∈ U) E ⊢ u] ∧ [(∀e ∈ E) U ⊢ e] ⟹ Th(E) = Th(U)   (§3.15.1) -/
theorem reciprocity {E U : Stmts S} (hEU : Proves R E U) (hUE : Proves R U E) :
    Th R E = Th R U :=
  ext (fun _ d => substitute R hUE d) (fun _ d => substitute R hEU d)

/-! ## Theorem 3.23.1 — The ordered proof ledger -/

/-- U = ⟨L₁, L₂, …⟩, E ⊆ U, Lᵢ ∈ E or Lᵢ ∈ Th({L₁, …, Lᵢ₋₁}).   (§6.1, p. 128, l. 2764)
    Its ground lines are the members of E; every other line is derived by a
    stated rule from the lines before it. -/
structure Ledger (E : Stmts S) where
  line : Nat → S
  ground_or_derived : ∀ i, E (line i) ∨ Th R (fun φ => ∃ j, j < i ∧ line j = φ) (line i)
  ground_lines : ∀ e, E e → ∃ i, line i = e

variable {R}

/-- The theory U: the lines of the ledger. -/
def Ledger.U {E : Stmts S} (L : Ledger R E) : Stmts S := fun φ => ∃ i, L.line i = φ

/-- Theorem 3.23.1 — Ordered proof-ledger theorem. Every line is derivable from
    the admitted ground. Proof: induction on the index. -/
theorem Ledger.derivable {E : Stmts S} (L : Ledger R E) : ∀ i, Th R E (L.line i) := by
  have upto : ∀ n, ∀ i, i < n → Th R E (L.line i) := by
    intro n
    induction n with
    | zero => intro i h; exact absurd h (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      cases L.ground_or_derived i with
      | inl hE => exact E29 R E _ hE
      | inr hd =>
        apply substitute R _ hd
        intro φ ⟨j, hj, hjφ⟩
        rw [← hjφ]
        exact ih j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hi))
  exact fun i => upto (i + 1) i (Nat.lt_succ_self i)

/-- §3.23.1 — The dependency graph: an edge j → i whenever line i cites line j,
    and every cited line comes earlier. -/
inductive DependsOn (cites : Nat → Nat → Prop) : Nat → Nat → Prop
  | edge {j i} : cites j i → DependsOn cites j i
  | trans {k j i} : DependsOn cites k j → DependsOn cites j i → DependsOn cites k i

theorem DependsOn.lt {cites : Nat → Nat → Prop} (earlier : ∀ j i, cites j i → j < i) :
    ∀ {j i}, DependsOn cites j i → j < i := by
  intro j i d
  induction d with
  | edge h => exact earlier _ _ h
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- Corollary 3.23.2 — A proof ledger contains no self-supporting dependency
    cycle: a cycle would need i < i. -/
theorem no_cycle {cites : Nat → Nat → Prop} (earlier : ∀ j i, cites j i → j < i) (i : Nat) :
    ¬ DependsOn cites i i :=
  fun d => Nat.lt_irrefl i (DependsOn.lt earlier d)

/-! ## Section 6 — The Reciprocal Existence Theorem -/

section Theorem
variable {E : Stmts S} (L : Ledger R E)

/-- Theorem R1 — Forward traversal: E ⊢ U.   (§6.2, p. 129, l. 2773) -/
theorem R1 : Proves R E L.U := by
  intro φ ⟨i, hi⟩
  rw [← hi]
  exact L.derivable i

/-- Theorem R2 — Reverse traversal: U ⊢ E.   (§6.3, p. 129, l. 2776)
    E ⊆ U, and E29 gives U ⊆ Th(U). Hence E ⊆ Th(U). -/
theorem R2 : Proves R L.U E :=
  sub_trans (fun e he => L.ground_lines e he) (E29 R L.U)

/-- Theorem R3 — Reciprocity: E ≡ U, and Th(E) = Th(U).   (§6.4, p. 131, ll. 2822–2837)
    E ⊢ U ∧ U ⊢ E ⟹ Th(E) = Th(U), and E ⊢ U ∧ U ⊢ E ⟹ E ≡d U. -/
theorem R3 : Reciprocal R E L.U ∧ Th R E = Th R L.U :=
  ⟨⟨R1 L, R2 L⟩, reciprocity R (R1 L) (R2 L)⟩

/-- Theorem R4 — Fixed point: Th(Th(U)) = Th(U) = Th(E).   (§6.5, p. 132, l. 2839) -/
theorem R4 : Th R (Th R L.U) = Th R L.U ∧ Th R L.U = Th R E :=
  ⟨E30 R L.U, (R3 L).2.symm⟩

/-- Exactly one `T` has property `P`. -/
def ExactlyOne (P : Stmts S → Prop) : Prop := ∃ T, P T ∧ ∀ T', P T' → T' = T

/-- The property of §6.6: T = Th(T) ∧ E ⊢ T ∧ T ⊢ E. -/
def MutuallyDerivable (E T : Stmts S) : Prop := IsTheory R T ∧ Proves R E T ∧ Proves R T E

omit L in
/-- Every theory mutually derivable with E is Th(E). (Proof of R5, uniqueness.) -/
theorem unique_reciprocal {T : Stmts S} (h : MutuallyDerivable (R := R) E T) : T = Th R E := by
  obtain ⟨hT, hET, hTE⟩ := h
  apply ext hET
  intro φ hφ
  have : Th R E ⊆ Th R T := fun _ d => substitute R hTE d
  rw [hT]
  exact this φ hφ

/-- Theorem R5 — Uniqueness. ∃!T [T = Th(T) ∧ E ⊢ T ∧ T ⊢ E], T = Th(E) = Th(U).
    (§6.6, p. 132, l. 2846) -/
theorem R5 : ExactlyOne (MutuallyDerivable (R := R) E) ∧ Th R E = Th R L.U := by
  refine ⟨⟨Th R E, ⟨(E30 R E).symm, sub_refl _, ?_⟩, fun _ h => unique_reciprocal h⟩, (R3 L).2⟩
  exact sub_trans (E29 R E) (E29 R (Th R E))

omit L in
/-- Corollary R6 — Rigidity. T′ = Th(T′) ∧ T′ ≠ Th(E) ⟹ ¬(E ⊢ T′ ∧ T′ ⊢ E).
    (§6.7, p. 132, l. 2853) -/
theorem R6 {T' : Stmts S} (hT : IsTheory R T') (hne : T' ≠ Th R E) :
    ¬ (Proves R E T' ∧ Proves R T' E) :=
  fun ⟨h₁, h₂⟩ => hne (unique_reciprocal ⟨hT, h₁, h₂⟩)

end Theorem

/-! ## §5.3 — K7: the seven channels, equal, none weighted -/

namespace K7

/-- Ξ = (ξ₁,…,ξ₇).   (§5.3, p. 126, l. 2722) Exact integers. -/
abbrev Defects := Fin 7 → Int

/-- Ξ = 0: every channel's defect is zero. -/
def Zero (Ξ : Defects) : Prop := ∀ i, Ξ i = 0

/-- The defects are non-negative. -/
def NonNeg (Ξ : Defects) : Prop := ∀ i, 0 ≤ Ξ i

/-- Fᵢ = gᵢ(ξᵢ), gᵢ(0)=0, gᵢ strictly increasing.   (§5.3, p. 126, l. 2724) -/
structure Measure where
  g : Fin 7 → Int → Int
  at_zero : ∀ i, g i 0 = 0
  strict : ∀ i a b, a < b → g i a < g i b

/-- The largest of seven values, every one counted the same. -/
def max7 (f : Fin 7 → Int) : Int :=
  max (f 0) (max (f 1) (max (f 2) (max (f 3) (max (f 4) (max (f 5) (f 6))))))

theorem max7_le {f : Fin 7 → Int} {c : Int} : max7 f ≤ c ↔ ∀ i, f i ≤ c := by
  simp only [max7, Int.max_le]
  constructor
  · intro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    match i with
    | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2 | ⟨3, _⟩ => exact h3
    | ⟨4, _⟩ => exact h4 | ⟨5, _⟩ => exact h5 | ⟨6, _⟩ => exact h6
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩

theorem le_max7 (f : Fin 7 → Int) (i : Fin 7) : f i ≤ max7 f :=
  (max7_le.mp (Int.le_refl _)) i

/-- F* = max(F₁,…,F₇).   (§5.3, p. 126, l. 2726) -/
def Fstar (m : Measure) (Ξ : Defects) : Int := max7 (fun i => m.g i (Ξ i))

theorem g_nonneg (m : Measure) {Ξ : Defects} (h : NonNeg Ξ) (i : Fin 7) : 0 ≤ m.g i (Ξ i) := by
  by_cases hz : Ξ i = 0
  · rw [hz, m.at_zero]; exact Int.le_refl 0
  · have hlt : 0 < Ξ i := by have := h i; omega
    have := m.strict i 0 (Ξ i) hlt
    rw [m.at_zero] at this
    exact Int.le_of_lt this

/-- Lemma 5 — Zero-Max Equivalence. F* = 0 ⇔ Ξ = 0.   (§5.3, p. 127, l. 2732)
    If F* = 0, then Fᵢ ≤ 0 for every i. Since Fᵢ ≥ 0, each Fᵢ = 0. Strict
    monotonicity and gᵢ(0) = 0 give ξᵢ = 0. Conversely, ξᵢ = 0 for every i gives
    Fᵢ = 0 for every i, hence F* = 0. -/
theorem lemma5 (m : Measure) {Ξ : Defects} (h : NonNeg Ξ) : Fstar m Ξ = 0 ↔ Zero Ξ := by
  constructor
  · intro hF i
    have hle : m.g i (Ξ i) ≤ 0 := hF ▸ le_max7 (fun i => m.g i (Ξ i)) i
    by_cases hz : Ξ i = 0
    · exact hz
    · have hlt : 0 < Ξ i := by have := h i; omega
      have := m.strict i 0 (Ξ i) hlt
      rw [m.at_zero] at this
      omega
  · intro hz
    apply Int.le_antisymm
    · exact max7_le.mpr fun i => by rw [hz i, m.at_zero]; exact Int.le_refl 0
    · have := le_max7 (fun i => m.g i (Ξ i)) 0
      simp only [hz 0, m.at_zero] at this
      exact this

/-- The flow of the defects: dξᵢ/dt = Gᵢ(ξ₁, …, ξ₇).   (evidence §8.3) -/
abbrev Flow := Defects → Defects

/-- ξᵢ = 0 is certifiable at Ξ: it holds, and it is invariant under the flow.
    A level set {ξᵢ = 0} is invariant under a C¹ flow only where the flow is
    tangent to it (Nagumo; Khalil §4.2): Gᵢ(Ξ) = 0.   (evidence §8.3) -/
def Certifiable (G : Flow) (i : Fin 7) (Ξ : Defects) : Prop := Ξ i = 0 ∧ G Ξ i = 0

/-- The ground state is at rest under the flow (Proposition 8.6): G(0) = 0. -/
def AtRest (G : Flow) : Prop := ∀ i, G (fun _ => 0) i = 0

/-- The lock (evidence §8.3): on the face ξᵢ = 0 with some ξⱼ > 0, Gᵢ(Ξ) ≠ 0.
    `Near Ξ` is the neighbourhood of Ξ = 0 where the lock holds. -/
def Locked (G : Flow) (Near : Defects → Prop) : Prop :=
  ∀ Ξ, Near Ξ → NonNeg Ξ → ¬ Zero Ξ → ∀ i, Ξ i = 0 → G Ξ i ≠ 0

/-- The lock from its local form (evidence §8.3): Gᵢ(Ξ) = Σ cᵢⱼξⱼ + Rᵢ(Ξ) with
    every cᵢⱼ ≥ c > 0, the defects non-negative and |Rᵢ(Ξ)| ≤ K|Ξ|². The linear
    part is at least c|Ξ|, which exceeds K|Ξ|² for 0 < |Ξ| < c/K. So Gᵢ ≠ 0.
    Here `n` is |Ξ|, `lin` the linear part and `rem` the remainder. -/
theorem lock_local (c K n lin rem : Int) (hn : 0 < n) (hlin : c * n ≤ lin)
    (hrem : -(K * n * n) ≤ rem ∧ rem ≤ K * n * n) (hsmall : K * n < c) : lin + rem ≠ 0 := by
  have : K * n * n < c * n := Int.mul_lt_mul_of_pos_right hsmall hn
  omega

/-- Theorem 8.3 (ground-state closure; mutual necessity). For each channel i,
    ξᵢ = 0 is certifiable exactly when Ξ = 0.   (evidence §8.3) -/
theorem certifiable_iff (G : Flow) (Near : Defects → Prop) (hL : Locked G Near) (hR : AtRest G)
    {Ξ : Defects} (hN : Near Ξ) (h : NonNeg Ξ) (i : Fin 7) : Certifiable G i Ξ ↔ Zero Ξ := by
  constructor
  · intro ⟨hi, hG⟩
    exact Classical.byContradiction fun hz => hL Ξ hN h hz i hi hG
  · intro hz
    have : Ξ = fun _ => 0 := funext hz
    subst this
    exact ⟨rfl, hR i⟩

/-- Solve(i): channel i is certifiably solved. Solve(all): all seven are. -/
def Solve (G : Flow) (i : Fin 7) (Ξ : Defects) : Prop := Certifiable G i Ξ
def SolveAll (G : Flow) (Ξ : Defects) : Prop := ∀ i, Certifiable G i Ξ

/-- Theorem 6 — Ground-State Mutual Necessity. Solve(i) ⇔ Solve(all) ⇔ Ξ = 0.
    (§5.3, p. 127, l. 2740) -/
theorem theorem6 (G : Flow) (Near : Defects → Prop) (hL : Locked G Near) (hR : AtRest G)
    {Ξ : Defects} (hN : Near Ξ) (h : NonNeg Ξ) (i : Fin 7) :
    (Solve G i Ξ ↔ SolveAll G Ξ) ∧ (SolveAll G Ξ ↔ Zero Ξ) := by
  have each := fun j => certifiable_iff G Near hL hR hN h j
  refine ⟨⟨fun hi j => (each j).mpr ((each i).mp hi), fun hall => hall i⟩,
          ⟨fun hall => (each 0).mp (hall 0), fun hz j => (each j).mpr hz⟩⟩

/-- One open channel leaves none of the seven certified: Ξ = (0, 1, 0, 0, 0, 0, 0).
    (evidence §8.3) -/
theorem one_open_certifies_none (G : Flow) (Near : Defects → Prop) (hL : Locked G Near)
    (hR : AtRest G) (hN : Near (fun j => if j = 1 then 1 else 0)) (i : Fin 7) :
    ¬ Certifiable G i (fun j => if j = 1 then 1 else 0) := by
  have h : NonNeg (fun j : Fin 7 => if j = 1 then (1 : Int) else 0) := by
    intro j; by_cases hj : j = 1 <;> simp [hj]
  rw [certifiable_iff G Near hL hR hN h i]
  intro hz
  have := hz 1
  simp at this

/-- VK(Ξ) = ΞᵀΞ = Σᵢ ξᵢ², every channel counted equally.   (evidence §8.6, p. 161, l. 3487) -/
def VK (Ξ : Defects) : Int :=
  Ξ 0 * Ξ 0 + Ξ 1 * Ξ 1 + Ξ 2 * Ξ 2 + Ξ 3 * Ξ 3 + Ξ 4 * Ξ 4 + Ξ 5 * Ξ 5 + Ξ 6 * Ξ 6

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases Int.le_total 0 a with
  | inl h => exact Int.mul_nonneg h h
  | inr h => have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
             rwa [Int.neg_mul_neg] at this

theorem sq_eq_zero {a : Int} (h : a * a = 0) : a = 0 := by
  cases Int.mul_eq_zero.mp h with
  | inl h => exact h
  | inr h => exact h

/-- Proposition 8.6: V = ΞᵀΞ is zero exactly at Ξ = 0.   (evidence §8.6) -/
theorem VK_zero_iff (Ξ : Defects) : VK Ξ = 0 ↔ Zero Ξ := by
  have h0 := sq_nonneg (Ξ 0); have h1 := sq_nonneg (Ξ 1); have h2 := sq_nonneg (Ξ 2)
  have h3 := sq_nonneg (Ξ 3); have h4 := sq_nonneg (Ξ 4); have h5 := sq_nonneg (Ξ 5)
  have h6 := sq_nonneg (Ξ 6)
  constructor
  · intro hV
    unfold VK at hV
    have z0 : Ξ 0 = 0 := sq_eq_zero (by omega)
    have z1 : Ξ 1 = 0 := sq_eq_zero (by omega)
    have z2 : Ξ 2 = 0 := sq_eq_zero (by omega)
    have z3 : Ξ 3 = 0 := sq_eq_zero (by omega)
    have z4 : Ξ 4 = 0 := sq_eq_zero (by omega)
    have z5 : Ξ 5 = 0 := sq_eq_zero (by omega)
    have z6 : Ξ 6 = 0 := sq_eq_zero (by omega)
    intro i
    match i with
    | ⟨0, _⟩ => exact z0 | ⟨1, _⟩ => exact z1 | ⟨2, _⟩ => exact z2 | ⟨3, _⟩ => exact z3
    | ⟨4, _⟩ => exact z4 | ⟨5, _⟩ => exact z5 | ⟨6, _⟩ => exact z6
  · intro hz
    simp [VK, hz 0, hz 1, hz 2, hz 3, hz 4, hz 5, hz 6]

/-! ### The integrated transport form (§5.3, p. 127, ll. 2742–2748) -/

/-- The product of a list of whole numbers. -/
def prod : List Nat → Nat
  | [] => 1
  | w :: ws => w * prod ws

theorem mul_eq_one {a b : Nat} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a with
  | zero => simp at h
  | succ a =>
    cases b with
    | zero => simp at h
    | succ b => simp only [Nat.succ_mul, Nat.mul_succ] at h; omega

/-- w_Δ := [Λ:Δ(Λ)] ≥ 1, a whole number. For a finite transport set ℰ:
    ∏_{Δ∈ℰ} w_Δ = 1 ⇔ ∀Δ: w_Δ = 1, that is, ∀Δ: δ_Δ = log w_Δ = 0.
    (§5.3, p. 127, l. 2748) -/
theorem prod_eq_one_iff : ∀ (ws : List Nat), prod ws = 1 ↔ ∀ w, w ∈ ws → w = 1
  | [] => by simp [prod]
  | w :: ws => by
    have ih := prod_eq_one_iff ws
    simp only [prod, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h1
      exact ⟨(mul_eq_one h1).1, ih.mp (mul_eq_one h1).2⟩
    · intro ⟨h1, h2⟩
      rw [h1, ih.mpr h2]

/-- w_{Δ₁∘Δ₂} = w_{Δ₁}w_{Δ₂}: composition multiplies indices.   (§5.3, p. 127, l. 2744)
    The product over ℰ is the index of the composed transport. -/
theorem prod_append (a b : List Nat) : prod (a ++ b) = prod a * prod b := by
  induction a with
  | nil => simp [prod]
  | cons w ws ih => simp [prod, ih, Nat.mul_assoc]

end K7

/-! ## §5.2 — The manifold and the seven fields -/

/-- φ = (P, I, Sₐ, Ψ, Q, A, Rₐ): the seven coupled fields.   (§5.2, p. 126, l. 2712) -/
inductive Field
  | P | I | S | Ψ | Q | A | R
  deriving DecidableEq, Repr

/-- Each field is one K7 channel. -/
def Field.channel : Field → Fin 7
  | .P => 0 | .I => 1 | .S => 2 | .Ψ => 3 | .Q => 4 | .A => 5 | .R => 6

def Field.ofChannel : Fin 7 → Field
  | ⟨0, _⟩ => .P | ⟨1, _⟩ => .I | ⟨2, _⟩ => .S | ⟨3, _⟩ => .Ψ
  | ⟨4, _⟩ => .Q | ⟨5, _⟩ => .A | ⟨6, _⟩ => .R

/-- The seven fields are exactly the seven channels of K7: one coupled problem. -/
theorem seven_fields_seven_channels :
    (∀ f, Field.ofChannel f.channel = f) ∧ (∀ i, (Field.ofChannel i).channel = i) := by
  refine ⟨fun f => by cases f <;> rfl, fun i => ?_⟩
  match i with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl

/-- M = U × T⁴, dim M = 8.   (§6.3.1, p. 129, l. 2786; §5.2, p. 126, l. 2710) -/
def dimU : Nat := 4
def dimT4 : Nat := 4
theorem dim_M : dimU + dimT4 = 8 := rfl

/-! ## Evidence §14.3 — Ξ̄* = φ⁻¹ = (√5 − 1)/2, exactly -/

/-- a + b√5, with whole a and b: exact, no decimal of √5 is ever taken. -/
structure Root5 where
  a : Int
  b : Int
  deriving DecidableEq

def Root5.mul (x y : Root5) : Root5 := ⟨x.a * y.a + 5 * x.b * y.b, x.a * y.b + x.b * y.a⟩
def Root5.add (x y : Root5) : Root5 := ⟨x.a + y.a, x.b + y.b⟩

/-- 2φ⁻¹ = √5 − 1 and 2φ = √5 + 1. -/
def twoInvPhi : Root5 := ⟨-1, 1⟩
def twoPhi : Root5 := ⟨1, 1⟩

/-- φ⁻¹ · φ = 1: (√5 − 1)(√5 + 1) = 4 = 2 · 2. -/
theorem invPhi_mul_phi : twoInvPhi.mul twoPhi = ⟨4, 0⟩ := by decide

/-- φ⁻¹ is the positive root of x² + x = 1: (√5 − 1)² + 2(√5 − 1) = 4.   (evidence §14.3, p. 231, l. 5080) -/
theorem invPhi_root : (twoInvPhi.mul twoInvPhi).add (Root5.mul ⟨2, 0⟩ twoInvPhi) = ⟨4, 0⟩ := by decide

/-! ## §3.19 — Translated reciprocity -/

section Translation
variable {SA SB : Type u}

/-- Theorem 3.15.2 — Reciprocal translation. τ: A → B and σ: B → A preserve and
    reflect derivability, and A ⊢ φ ↔ σ(τ(φ)), B ⊢ ψ ↔ τ(σ(ψ)). Then τ and σ are
    inverse on the theorem sets modulo provable equivalence.   (§3.15.2; §3.19, p. 52, l. 1132) -/
theorem translated_reciprocity (thmA : SA → Prop) (thmB : SB → Prop)
    (eqvA : SA → SA → Prop) (eqvB : SB → SB → Prop) (τ : SA → SB) (σ : SB → SA)
    (pres_τ : ∀ φ, thmA φ → thmB (τ φ)) (refl_τ : ∀ φ, thmB (τ φ) → thmA φ)
    (pres_σ : ∀ ψ, thmB ψ → thmA (σ ψ)) (refl_σ : ∀ ψ, thmA (σ ψ) → thmB ψ)
    (round_A : ∀ φ, eqvA φ (σ (τ φ))) (round_B : ∀ ψ, eqvB ψ (τ (σ ψ))) :
    (∀ φ, thmA φ ↔ thmB (τ φ)) ∧ (∀ ψ, thmB ψ ↔ thmA (σ ψ)) ∧
    (∀ φ, eqvA φ (σ (τ φ))) ∧ (∀ ψ, eqvB ψ (τ (σ ψ))) :=
  ⟨fun φ => ⟨pres_τ φ, refl_τ φ⟩, fun ψ => ⟨pres_σ ψ, refl_σ ψ⟩, round_A, round_B⟩

/-- Cross-domain bridge: R_total = R_n ∘ ⋯ ∘ R_2 ∘ R_1.   (§3.19, p. 52, l. 1130)
    Each bridge preserves theorems, so the composed bridge does. -/
theorem bridge_compose {SC : Type u} (thmA : SA → Prop) (thmB : SB → Prop) (thmC : SC → Prop)
    (r₁ : SA → SB) (r₂ : SB → SC)
    (h₁ : ∀ φ, thmA φ ↔ thmB (r₁ φ)) (h₂ : ∀ ψ, thmB ψ ↔ thmC (r₂ ψ)) :
    ∀ φ, thmA φ ↔ thmC (r₂ (r₁ φ)) :=
  fun φ => (h₁ φ).trans (h₂ (r₁ φ))

end Translation

/-! ## §4.6, §6.8 — The derivational spine and the complete dependency chain -/

variable {R : Rule S → Prop}

/-- E ⊢ A1 ⟹ A2 ⟹ A3 ⟹ A4.   (§4.6, p. 120, l. 2592)
    A1 is proved from E (§1.1). Each next root relation is derived from E with
    the one before it:
      A1 ↓ physical differentiation                               A2: P ─ε→ P′, P′ ≠ P
      A2 ↓ symmetry preservation + no hidden prior distinction    A3: Var(ε) > 0, ε ∉ Comp
      A3 ↓ local information continuity + Noether/action variation A4: div(S) = 0 -/
structure Spine (R : Rule S → Prop) (E : Stmts S) where
  A1 : S
  A2 : S
  A3 : S
  A4 : S
  A1_from_E : Th R E A1
  differentiation : Th R (fun φ => E φ ∨ φ = A1) A2
  symmetry : Th R (fun φ => E φ ∨ φ = A2) A3
  continuity : Th R (fun φ => E φ ∨ φ = A3) A4

/-- A statement derived from E together with something E derives is derived from E. -/
theorem from_E_with {E : Stmts S} {a b : S} (ha : Th R E a) (hb : Th R (fun φ => E φ ∨ φ = a) b) :
    Th R E b :=
  substitute R (fun φ h => h.elim (fun he => E29 R E φ he) (fun h => h ▸ ha)) hb

/-- E ⊢ A1, A2, A3, A4: every root relation is derived from E. -/
theorem Spine.from_E {E : Stmts S} (A : Spine R E) :
    Th R E A.A1 ∧ Th R E A.A2 ∧ Th R E A.A3 ∧ Th R E A.A4 :=
  have h2 := from_E_with A.A1_from_E A.differentiation
  have h3 := from_E_with h2 A.symmetry
  ⟨A.A1_from_E, h2, h3, from_E_with h3 A.continuity⟩

/-! ## §6.9 — The complete result: one equation -/

/-- The Reciprocal Existence Theorem, the complete result of §6.9 (pp. 134–135, ll. 2899–2904):

      A1 ⇒ A2 ⇒ A3 ⇒ A4
      ∏_{Δ∈ℰ} w_Δ = 1 ⇔ Ξ = 0          (here: ⇔ ∀Δ, w_Δ = 1, and Solve(i) ⇔ Solve(all) ⇔ Ξ = 0)
      E ⊢ U ∧ U ⊢ E ⇒ E ≡ U
      Th(E) = Th(U)
      Th(Th(U)) = Th(U)
      ∃!T [T = Th(T) ∧ E ⊢ T ∧ T ⊢ E]

    Accordingly, when the complete ground E coexists non-contradictorily, the UEF
    is the one theory reciprocal with it. -/
theorem the_one_equation {E : Stmts S} (A : Spine R E) (L : Ledger R E)
    (ws : List Nat) (m : K7.Measure) (G : K7.Flow) (Near : K7.Defects → Prop)
    (hL : K7.Locked G Near) (hR : K7.AtRest G)
    {Ξ : K7.Defects} (hN : Near Ξ) (h0 : K7.NonNeg Ξ) (i : Fin 7) :
    -- A1 ⇒ A2 ⇒ A3 ⇒ A4, every one from E
    (Th R E A.A1 ∧ Th R E A.A2 ∧ Th R E A.A3 ∧ Th R E A.A4) ∧
    -- K7: ∏ w_Δ = 1 ⇔ ∀Δ: w_Δ = 1;  F* = 0 ⇔ Ξ = 0;  Solve(i) ⇔ Solve(all) ⇔ Ξ = 0
    (K7.prod ws = 1 ↔ ∀ w, w ∈ ws → w = 1) ∧
    (K7.Fstar m Ξ = 0 ↔ K7.Zero Ξ) ∧
    ((K7.Solve G i Ξ ↔ K7.SolveAll G Ξ) ∧ (K7.SolveAll G Ξ ↔ K7.Zero Ξ)) ∧
    -- E ⊢ U ∧ U ⊢ E ⇒ E ≡ U
    Reciprocal R E L.U ∧
    -- Th(E) = Th(U)
    Th R E = Th R L.U ∧
    -- Th(Th(U)) = Th(U)
    Th R (Th R L.U) = Th R L.U ∧
    -- ∃!T [T = Th(T) ∧ E ⊢ T ∧ T ⊢ E]
    ExactlyOne (MutuallyDerivable (R := R) E) :=
  ⟨A.from_E, K7.prod_eq_one_iff ws, K7.lemma5 m h0, K7.theorem6 G Near hL hR hN h0 i,
   (R3 L).1, (R3 L).2, (R4 L).1, (R5 L).1⟩

end UEF
