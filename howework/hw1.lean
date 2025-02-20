import Mathlib.Tactic
set_option linter.all false
/-!
# Инструкция по выполнению ДЗ №1.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
Используйте только тактики, пройденные на первой лекции, а именно:
* `intro`
* `exact`
* `apply`
* `cases'`
* `constructor`
* `left`/`right`
* `change`
* `exfalso`
* `by_cases`
* `trivial`
* `rfl`
* `rw`

Не стесняйтесь спрашивать вопросы в чате!
-/

/-- Problem 1. -/
example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 h3
  apply h2
  apply h1
  exact h3
  done

/-- Problem 2. -/
example : (P ↔ True) → (Q ↔ False) → (P ∧ ¬Q ↔ True) := by
  intro h1 h2
  constructor
  intro h3
  trivial
  intro h4
  constructor
  rw [h1]
  trivial
  rw [h2]
  trivial
  done

/-- Problem 3. -/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro h1
  by_cases h2 : P
  by_cases h3 : Q
  exfalso
  apply h1
  constructor
  exact h2
  exact h3
  right
  exact h3
  left
  exact h2
  intro h4 h5
  cases' h4 with h6 h7
  cases' h5 with h8 h9
  apply h6
  exact h8
  apply h7
  cases' h5 with h8 h9
  apply h9
  done
