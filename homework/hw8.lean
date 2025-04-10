import Mathlib
/-!
# Инструкция по выполнению ДЗ №8.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

namespace Problem1

/-- Задача 1. Существует нелинейная функция `f` из ℝ в ℝ, такая что `f(x + y) = f(x) + f(y)`.

Комментарий: для ℚ это неверно и такая задача была в первой контрольной.

Указание: ℝ это векторное пространство над ℚ. Его размерность на самом деле равна континууму: см.
`Real.rank_rat_real`. Можно задать `f` равной `1` на каком-то базисном элементе `e`,
и `0` на остальных. Тогда для любого другого базисного элемента `e'` имеем
`c * e' = f e' = 0` и `с * e = f e = 1`, противоречие.
-/
example : ∃ f : ℝ → ℝ, (∀ x y, f (x + y) = f x + f y) ∧ ¬ ∃ c, ∀ x, f x = c * x := by
  -- Берем какой-то базис ℝ над ℚ.
  -- `Module.Free` это класс означающий что модуль свободен, то есть имеет базис.
  -- Все векторные пространства свободны.
  -- Простейший пример несвободного модуля это ℤₙ над ℤ.
  -- Базиса там нет, потому что `n • v = 0` для всех `v`, и это позволяет получить нулевую
  -- линейную комбинацию базисных элементов.
  obtain ⟨I, B⟩ : Nonempty ((I : Type) × Basis I ℚ ℝ) := Module.Free.exists_basis
  -- Используем континуальность `I` чтобы взять два различных элемента базиса.
  -- Класс `Nontrivial` как раз означает существование таких элементов.
  obtain ⟨⟨i1, i2, hi⟩⟩ : Nontrivial I := by
    suffices Infinite I by
      exact Infinite.instNontrivial I
    rw [← Cardinal.aleph0_le_mk_iff, B.mk_eq_rank'', Real.rank_rat_real]
    exact Cardinal.aleph0_le_continuum
  sorry

end Problem1

open Classical

/-- Задача 2. В конечной коммутативной группе без элементов четного порядка (что эквивалентно `h` ниже),
произведение всех элементов равно 1. -/
example (G : Type) [CommGroup G] [Fintype G] (h : ∀ x : G, x ≠ 1 → x^2 ≠ 1) :
    (∏ g : G, g) = 1 := by
  sorry
