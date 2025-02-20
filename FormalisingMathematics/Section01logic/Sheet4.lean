/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases' h with hP hQ
  exact hP
  done

example : P ∧ Q → Q := by
  intro h
  cases' h with hP hQ
  exact hQ
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  cases' h2 with hP hQ
  apply h1
  exact hP
  exact hQ
  done

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  exact hP
  exact hQ
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases' h with hP hQ
  constructor
  exact hQ
  exact hP
  done

example : P → P ∧ True := by
  intro h1
  constructor
  exact h1
  trivial
  done

example : False → P ∧ False := by
  intro h1
  exfalso
  exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases' h1 with hP hQ
  cases' h2 with hQ' hR
  constructor
  exact hP
  exact hR
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  exact h2
  exact h3
  done
