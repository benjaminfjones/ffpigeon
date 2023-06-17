import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card


inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  deriving Repr

open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
    | monday => 1
    | tuesday => 2
    | wednesday => 3
    | thursday => 4
    | friday => 5

open Function

theorem number_of_day_inj : Injective (numberOfDay : Weekday → Nat) := by
  intro x y h
  admit

-- TODO: need instance of Fintype?
-- def all_weekdays : Finset Weekday := Finset.univ _

-- RTO choice is valid if it has at least 3 weekdays
def rto_valid (c : Finset Weekday) : Prop := 3 ≤ c.card

-- Every pair of two valid RTO choices shares at least one day in common
theorem rto_collision (c₁ c₂ : Finset Weekday) (h₁ : rto_valid c₁) (h₂ : rto_valid c₂) :
  ∃ d : Weekday, d ∈ c₁ ∧ d ∈ c₂ := by
  by_contra' h
  have hd : Disjoint c₁ c₂ := Finset.disjoint_left.mpr h
  let cc : Finset Weekday := Finset.disjUnion c₁ c₂ hd
  -- claim: cc ⊆ univ, cc.card = 3 + 3 = 6, univ.card = 5, cc.card ≤ univ.card, 6 ≤ 5
  admit