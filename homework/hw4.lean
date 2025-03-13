import Mathlib
/-!
# Инструкция по выполнению ДЗ №4.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Могут оказаться полезными:
* Индуктивные типы, ключевое слово `match`.
* Тактика `induction`.

Не стесняйтесь задавать вопросы в чате!
-/
open Function

/-- Задача 1. `BinTree` это тип бинарных деревьев, на листьях которого написаны натуральные числа.
Ваша задача -- определить функцию `BinTree.sum` которая вычисляет этих чисел. После этого проверьте
что "тесты" ниже могут быть доказаны с помощью `by rfl`.
-/
inductive BinTree
| leaf (val : ℕ)
| node (left : BinTree) (right : BinTree)

def BinTree.sum (tree : BinTree) : ℕ := sorry

-- Тесты
example (v : ℕ) : BinTree.sum (BinTree.leaf v) = v := by sorry --rfl
example : BinTree.sum (BinTree.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = 10 := by sorry --rfl

/-- Задача 2. Определите предикат `BinTree.AllEven` означающий что все написанные на листьях числа четны.
Проверьте что "тесты" нижы могут быть доказаны через `by reduce; norm_num`. Затем докажите теорему ниже.

Примечание: чтобы это сработало выражайте факт "`n` - четное" как `n % 2 = 0`.

Примечание №2: `reduce` это тактика которая приводит все термы в цели к нормальной форме. В частности она
раскрывает определения и определяет по какой ветви `match` пойти.
-/
def BinTree.AllEven (tree : BinTree) : Prop := sorry

-- Тесты
example : BinTree.AllEven (.leaf 3) = False := by sorry --reduce; norm_num
example : BinTree.AllEven (.leaf 2048) = True := by sorry --reduce; norm_num
example : BinTree.AllEven (.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = False := by sorry --reduce; norm_num
example : BinTree.AllEven (.node (.leaf 8) (.node (.node (.leaf 8) (.leaf 0)) (.leaf 4))) = True := by sorry --reduce; norm_num

-- Теорема
example (tree : BinTree) (h_even : tree.AllEven) : tree.sum % 2 = 0 := by
  sorry

/-- Задача 3: Существует счетная цепочка типов `Fₙ` такая что `Fₙ` можно инъективно и строго вложить
в `Fₙ₊₁`, и при этом `Fₙ₊₁ ≠ Fₙ`. -/
example : ∃ F : ℕ → Type, ∀ n, ∃ ι : F n → F (n + 1), Injective ι ∧ ι '' Set.univ ≠ Set.univ := by
  sorry
