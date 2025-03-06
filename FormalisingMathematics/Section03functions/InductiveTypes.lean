

inductive Weekday
| monday : Weekday
| tuesday : Weekday
| sunday : Weekday

example : Weekday.monday ≠ .sunday := by
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

inductive Foo
| mk1 (n : Nat)
| mk2

#check Foo.mk1 3
#check Foo.mk2

inductive Prod' (α β : Type)
| makePair (a : α) (b : β)

#check Prod'

#check Prod'.makePair (1 : Nat) (-2 : Int)

inductive Sum' (α β : Type)
| left (a : α)
| right (b : β)

#check (Sum'.left 1 : Sum' Nat Int)
#check (Sum'.right (-1) : Sum' Nat Int)

#check And

inductive And' (P Q : Prop)
| mk (p : P) (q : Q)

inductive Or' (P Q : Prop)
| left (p : P)
| right (q : Q)

def parse (val : String) : (α : Type) × α := sorry

#check (α : Type) × α

-- To be continued...
