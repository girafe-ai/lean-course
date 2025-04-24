import Mathlib
/-!
# Бонусное ДЗ №9 по верификации программ.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

namespace Problem1

/- Задача 1. Второй по порядку элемент в массиве.

Указание: лучше, конечно, верифицировать линейный алгоритм, но если это окажется слишком трудным,
попробуйте просто отсортировать (`List.mergeSort`) и взять второй с конца элемент.
-/

def secondMax (arr : List ℕ) : ℕ :=
  sorry

theorem secondMax_spec (arr : List ℕ) (h : 1 < arr.length) :
    -- либо существует ровно один элемент (максимум) больше `secondMax`
    (∃! v ∈ arr, secondMax arr < v) ∨
    -- либо `secondMax` совпадает с максимумом, и таких элементов в массиве хотя бы 2.
    (∀ v ∈ arr, v ≤ secondMax) ∧ (∃ (i : Fin arr.length), ∃ j ≠ i, arr[i] = secondMax arr ∧ arr[j] = secondMax arr) := by
  sorry

end Problem1

namespace Problem2

/- Задача 2. Достижима ли вершина `x` из вершины `y` в графе?

Задача стоит **2 балла**.
-/

/-- Граф задан таблицей смежности: ребро `x -> y` есть тогда и только тогда когда `g x y = true` -/
abbrev Graph (n : ℕ) : Type := Fin n → Fin n → Bool

inductive Walk {n : ℕ} (graph : Graph n) : (Fin n) → (Fin n) → Type
  /-- Пустой путь из `u` в `u` -/
  | nil {u : Fin n} : Walk graph u u
  /-- Соединение ребра `u -> v` и пути `v -> w` -/
  | cons {u v w : Fin n} (h : graph u v = true) (p : Walk graph v w) : Walk graph u w

/-- Вершины `x` и `y` соединены если между ними существует путь. -/
def AreConnected {n : ℕ} (g : Graph n) (x y : Fin n) : Prop :=
  Nonempty (Walk g x y)

/-- Наша функция для проверки достижимости. -/
def checkConnected (g : Graph n) (x y : Fin n) : Bool :=
  sorry

theorem isConnected_spec {g : Graph n} {x y : Fin n} :
    checkConnected g x y = true ↔ AreConnected g x y := by
  sorry

end Problem2
