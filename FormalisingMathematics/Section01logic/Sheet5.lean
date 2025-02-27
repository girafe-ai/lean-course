/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rewrite [h]
  rfl
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rewrite [h1]
  rfl
  intro h2
  rewrite [h2]
  rfl
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rewrite [h1, h2]
  rfl
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h
  cases' h with hP hQ
  constructor
  exact hQ
  exact hP
  intro h
  cases' h with hQ hP
  constructor
  exact hP
  exact hQ
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h
  cases' h with hPQ hR
  cases' hPQ with hP hQ
  constructor
  exact hP
  constructor
  exact hQ
  exact hR
  intro h
  cases' h with hP hQR
  constructor
  constructor
  exact hP
  cases' hQR with hQ hR
  exact hQ
  cases' hQR with hQ hR
  exact hR
  done

example : P ↔ P ∧ True := by
  constructor
  intro h
  constructor
  exact h
  trivial
  intro h
  cases' h with hP hTrue
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor
  intro h
  constructor
  exfalso
  exact h
  exact h
  intro h
  cases' h with hP hFalse
  exact hFalse
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw [h1, h2]
  done

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  apply h1
  by_cases hP : P
  exact hP
  apply h2
  exact hP
  by_cases hP : P
  exact hP
  apply h2
  exact hP
  done
