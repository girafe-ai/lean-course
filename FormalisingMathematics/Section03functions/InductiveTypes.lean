import Mathlib.Tactic

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


mutual
  inductive Even'
  | zero
  | succ (x : Odd')

  inductive Odd'
  | succ (x : Even')
end

example (P Q : Prop) : And' P Q → Or' P Q := by
  intro h
  cases' h with hP hQ
  exact Or'.left hP

theorem foo (P Q : Prop) : Or' P Q → P ∨ Q := by
  intro h
  cases h with
  | left hP => left; exact hP
  | right hQ => right; exact hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply And.intro
  · exact hP
  · exact hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨?_, ?_⟩
  · exact hP
  · exact hQ

example (a b : ℕ) (h : a < b) : a < b + 2 := by
  omega

example (a b : ℕ) (h : a = b) (h2 : a + 1 ≤ a * 2) : b + 1 ≤ b * 2 := by
  convert h2
  · exact Eq.symm h
  · exact h.symm

def sum (n : Nat) : Nat := match n with
| Nat.zero => Nat.zero
| Nat.succ m => sum m + n -- n = m + 1

#eval sum 0
#eval sum 1
#eval sum 3

example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction n with
  | zero =>
    unfold sum
    norm_num
  | succ m ih =>
    unfold sum
    ring_nf at ih ⊢
    rw [ih]
    ring

example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n with m ih
  · unfold sum
    norm_num
  · unfold sum
    ring_nf at ih ⊢
    rw [ih]
    ring

theorem sum_eq (n : ℕ) : 2 * sum n = n * (n + 1) := by
  cases n with
  | zero =>
    unfold sum
    norm_num
  | succ m =>
    unfold sum
    ring_nf
    rw [mul_comm, sum_eq m]
    ring

example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => simp [sum]
  | succ m =>
    specialize ih m (by omega)
    simp [sum]
    ring_nf
    sorry
