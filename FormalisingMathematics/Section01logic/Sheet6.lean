/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  cases' h1 with h4 h5
  apply h2
  exact h4
  apply h3
  exact h5
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  sorry
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  sorry
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · change P → False
      intro hP
      change P ∨ Q → False at h
      apply h
      left
      exact hP
    · sorry
  · intro h
    cases' h with hP hQ
    change P ∨ Q → False
    intro h
    apply hP
    cases' h with h1 h2
    · exact h1
    · exfalso
      apply hQ
      exact h2
      done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
