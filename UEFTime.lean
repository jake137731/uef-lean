/-
  THE UNIFIED EXISTENCE FRAMEWORK — Time is not foundational, in Lean 4 with Mathlib

  Jake McDonough, Institute for Higher Thinking, Louisville, Kentucky, USA

  Source: UEF Release, 01_Manuscript.pdf, §4.5.2 (Time is not foundational,
  proved) and §4.5.4 (the paper Time Is Not Foundational, Definitions 1–4 and
  Theorems 1–6). The proof is one move: a relation requires its relata.
-/
import Mathlib

namespace UEF.Time

/-! ## §4.5.2 — Definitions, from set theory (E31, MIT 18.100A) -/

variable {X V : Type*}

/-- A relation is a set of ordered pairs. Its components are the relata. -/
abbrev Relation (X : Type*) := Set (X × X)

/-- The relata of a relation: every component of every pair. -/
def relata (R : Relation X) : Set X := {x | ∃ p ∈ R, p.1 = x ∨ p.2 = x}

/-- A function is a set of ordered pairs with no two sharing a first component.
    Its first components are its domain. -/
structure Function' (X V : Type*) where
  graph : Set (X × V)
  single : ∀ p q, p ∈ graph → q ∈ graph → p.1 = q.1 → p.2 = q.2

/-- The domain of a function: its first components. -/
def Function'.domain (f : Function' X V) : Set X := {x | ∃ v, (x, v) ∈ f.graph}

/-- A function is defined at x when x is in its domain. -/
def Function'.DefinedAt (f : Function' X V) (x : X) : Prop := x ∈ f.domain

/-! ## The theorems of §4.5.2 -/

/-- Theorem 1 — A relation requires its relata. A relation on a set of things is a
    set of pairs of those things: every relatum is one of them. -/
theorem relation_requires_relata (E : Set X) (R : Relation X) (hR : R ⊆ E ×ˢ E) :
    relata R ⊆ E := by
  rintro x ⟨p, hp, h | h⟩
  · exact h ▸ (hR hp).1
  · exact h ▸ (hR hp).2

/-- Without the relata there are no pairs, and without the pairs no set. -/
theorem no_relata_no_relation (R : Relation X) (hR : R ⊆ (∅ : Set X) ×ˢ (∅ : Set X)) : R = ∅ := by
  ext p; simp only [Set.mem_empty_iff_false, iff_false]
  intro hp; exact (hR hp).1

/-- Theorem 2 — A function requires its domain. An empty domain gives the empty set,
    not a function on that domain. -/
theorem function_requires_domain (f : Function' X V) (h : f.domain = ∅) : f.graph = ∅ := by
  ext ⟨x, v⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have : x ∈ f.domain := ⟨v, hp⟩
  rw [h] at this
  exact this

/-- A coordinate is a function from a set of points to a set of values.
    Theorem 3 — A coordinate requires its points (by 2): it is defined only on its points. -/
structure Coordinate (X V : Type*) (points : Set X) extends Function' X V where
  on_points : toFunction'.domain ⊆ points

theorem coordinate_requires_points {points : Set X} (c : Coordinate X V points) (x : X)
    (hx : x ∉ points) : ¬ c.DefinedAt x :=
  fun h => hx (c.on_points h)

/-! ## §4.5.4 — Definitions 1–4 and Theorems 1–6 -/

section Block
variable (happened : X → Prop)

/-- Definition 3 — Each e in E is what happens. E is the set of events: what happened.
    An event is what happens. What did not happen is not an event. -/
def Events : Set X := {e | happened e}

/-- A time coordinate is a coordinate whose points are events. C: the time coordinates. -/
abbrev TimeCoordinate := Coordinate X ℝ (Events happened)

/-- Time is the relation between events. -/
structure TimeRelation where
  T : Relation X
  between_events : T ⊆ Events happened ×ˢ Events happened

/-- Theorem 1 — If e is in E, e has happened. -/
theorem theorem1 (e : X) (he : e ∈ Events happened) : happened e := he

/-- Theorem 2 — If e has not happened, e is not in E. -/
theorem theorem2 (e : X) (he : ¬ happened e) : e ∉ Events happened := he

/-- Theorem 3 — No c in C is defined on any e not in E. -/
theorem theorem3 (c : TimeCoordinate happened) (e : X) (he : e ∉ Events happened) :
    ¬ c.DefinedAt e :=
  coordinate_requires_points c e he

/-- Definition 4 — The block universe asserts that C is defined on E, that E includes
    future events (events that have not happened), and that the manifold is prior to E.
    Theorem 4 — The block universe requires c in C for some e not in E. -/
def BlockUniverse : Prop :=
  ∃ c : TimeCoordinate happened, ∃ e : X, ¬ happened e ∧ c.DefinedAt e

/-- Theorem 5 — No such c exists. -/
theorem theorem5 : ¬ ∃ c : TimeCoordinate happened, ∃ e : X, ¬ happened e ∧ c.DefinedAt e := by
  rintro ⟨c, e, he, hdef⟩
  exact theorem3 happened c e (theorem2 happened e he) hdef

/-- Theorem 6 — The block universe cannot exist. -/
theorem theorem6 : ¬ BlockUniverse happened :=
  theorem5 happened

/-- Theorem 4 and 5 of §4.5.2 — A time coordinate requires its events, and time
    requires its events: the time relation relates only what has happened. -/
theorem time_requires_events (t : TimeRelation happened) : relata t.T ⊆ Events happened :=
  relation_requires_relata (Events happened) t.T t.between_events

end Block

end UEF.Time
