import Mathlib.Tactic
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
  sorry

/-- Problem 2. -/
example : (P ↔ True) → (Q ↔ False) → (P ∧ ¬Q ↔ True) := by
  sorry

/-- Problem 3. -/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
