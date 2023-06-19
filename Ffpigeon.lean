import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.NCard
import Mathlib.Tactic.Linarith


-- Note: DecidableEq is required in order to automatically infer `Finset` for
-- set literals.
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  deriving Repr, DecidableEq

open Weekday

example : Finset Weekday := {tuesday}
example : Finset Weekday := {monday, tuesday}  -- requires `DecidableEq` to type check

def all_weekdays : Finset Weekday := {monday, tuesday, wednesday, thursday, friday}
theorem all_weekdays_complete : ∀ x : Weekday, x ∈ all_weekdays := by
  intro x
  cases x <;> simp
theorem all_weekdays_card : all_weekdays.card = 5 := rfl

instance : Fintype Weekday where
  elems := all_weekdays
  complete := all_weekdays_complete

-- Every pair of two valid RTO choices shares at least one day in common
theorem rto_collision (c₁ c₂ : Finset Weekday) (h₁ : 3 ≤ c₁.card) (h₂ : 3 ≤ c₂.card) :
  ∃ d : Weekday, d ∈ c₁ ∧ d ∈ c₂ := by
  by_contra' h
  have hd : Disjoint c₁ c₂ := Finset.disjoint_left.mpr h
  let cc : Finset Weekday := c₁ ∪ c₂
  have hcc_card : cc.card ≥ 6 := by
    calc
      Finset.card cc = Finset.card c₁ + Finset.card c₂ := Finset.card_disjoint_union hd
      _              ≥ 6 := by linarith
  have hcu : cc ⊆ all_weekdays := by
    intro a _
    exact (Fintype.complete a)
  have _ : cc.card ≤ all_weekdays.card := Finset.card_le_of_subset hcu
  have _ : 6 ≤ 5 := by
    calc
      6 ≤ cc.card := ge_iff_le.mp hcc_card
      _ ≤ all_weekdays.card := by assumption
      _ = 5 := all_weekdays_card
  contradiction