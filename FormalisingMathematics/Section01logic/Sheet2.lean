/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `trivial`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  trivial
  done

example : True → True := by
  intro hP
  trivial
  done

example : False → True := by
  intro hP
  trivial
  done

example : False → False := by
  intro hP
  exact hP
  done

example : (True → False) → False := by
  intro h
  apply h
  trivial
  done

example : False → P := by
  intro h
  exfalso
  exact h
  done

example : True → False → True → False → True → False := by
  intro h1 h2 h3 h4 h5
  exact h2
  done

example : P → (P → False) → False := by
  sorry
  done

example : (P → False) → P → Q := by
  sorry
  done

example : (True → False) → P := by
  sorry
  done
