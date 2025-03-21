import Mathlib
/-!
# Инструкция по выполнению ДЗ №5.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
На полный балл достаточно сделать **2 задачи**.

Не стесняйтесь задавать вопросы в чате!
-/

/-- Задача 1: Любая группа в которой верно `x^2=1` для всех `x`, абелева. -/
example {G : Type} [Group G] (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  sorry

/- Задача 2:
Покажите, что множество кватернионных единиц `Q₈ = {±1, ±i, ±j, ±k}`, которые перемножаются так,
что «минус на минус даёт плюс», `i² = j² = k² = -1` и
`ij = -ji = k`, `jk = -kj = i`, `ki = -ik = j`.
образуют группу. -/
namespace Problem2

inductive Q8_Generator where
| e
| i
| j
| k

-- Второй множитель отвечает за знак. `true` значит "минус".
def Q8 : Type := Q8_Generator × Bool

-- Указание: в определении `mul` нужно сделать `match (x, b1), (y, b2) with ...` и разобрать 16 случаев.
-- Булы можно складывать, сложение определено как xor.
-- После этого требуемые свойства должны доказываться разбором всех случаев
-- как-то так: `cases x <;> cases b1 <;> cases y <;> cases b2 <;> rfl`
instance : Group Q8 where
  one := sorry
  mul := sorry
  inv := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry

end Problem2

open Problem2 in
/-- Задача 3 (сложная): Q₈ не изоморфна D₄.

Указание: в группе Q8 есть два некоммутирующих элемента порядка 4: `i` и `j`, а в D4 нет.
Там всего два элемента порядка 4: `r 1` и `r 3` и те коммутируют.
Про диэдральную группу Dₙ можно почитать в Википедии.
https://ru.wikipedia.org/wiki/%D0%94%D0%B8%D1%8D%D0%B4%D1%80%D0%B0%D0%BB%D1%8C%D0%BD%D0%B0%D1%8F_%D0%B3%D1%80%D1%83%D0%BF%D0%BF%D0%B0
-/
example (φ : Q8 →* DihedralGroup 4) (ψ : DihedralGroup 4 →* Q8) (h1 : φ ∘ ψ = id) (h2 : ψ ∘ φ = id) :
    False := by
  sorry

/- Задача 4 (сложная): существует неабелева группа `G` в которой верно `x^3=1` для всех `x`.

Указание: нужная группа гуглится, но формализовать ее остается непросто. -/
namespace Problem4

def G : Type := sorry

instance : Group G where
  one := sorry
  mul := sorry
  inv := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry

example : (∀ g : G, g*g*g = 1) ∧ ∃ g h : G, g * h ≠ h * g := by
  sorry

end Problem4
