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
  intro h
  cases' h with hP hQ
  right
  exact hP
  left
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h
  cases' h with h1 h2
  cases' h1 with h3 h4
  left
  exact h3
  right
  left
  exact h4
  right
  right
  exact h2
  intro h
  cases' h with h1 h2
  left
  left
  exact h1
  cases' h2 with h3 h4
  left
  right
  exact h3
  right
  exact h4
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases' h3 with h4 h5
  left
  apply h1
  exact h4
  right
  apply h2
  exact h5
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases' h2 with h3 h4
  left
  apply h1
  exact h3
  right
  exact h4
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  rw [h1, h2]
  intro h3
  exact h3
  rw [h1, h2]
  intro h4
  exact h4
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
    · intro hQ
      apply h
      right
      exact hQ
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
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      constructor
      exact hP
      exact hQ
    · left
      exact hP
  · intro h
    intro hPQ
    cases' h with h1 h2
    · apply h1
      cases' hPQ with hP hQ
      exact hP
    · apply h2
      cases' hPQ with hP hQ
      exact hQ
    done
