/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  -- intro h

  -- change (True → False) → False
  intro h
  change True → False at h
  apply h
  trivial
  done

example : False → ¬True := by
  intro h
  exfalso
  exact h
  done

example : ¬False → True := by
  sorry
  done

example : True → ¬False := by
  sorry
  done

example : False → ¬P := by
  sorry
  done

example : P → ¬P → False := by
  sorry
  done

example : P → ¬¬P := by
  intro hP
  -- change (¬P → False)
  intro hp'
  -- change P → False at hp'
  apply hp'
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  sorry
  done

example : ¬¬False → False := by
  sorry
  done

example : ¬¬P → P := by
  intro h
  change (P → False) → False at h
  by_cases hP : P
  exact hP
  exfalso
  apply h
  exact hP
  done

example : ¬¬P → P := by
  intro h
  by_contra h'
  apply h
  exact h'

example : (¬Q → ¬P) → P → Q := by
  sorry
  done
