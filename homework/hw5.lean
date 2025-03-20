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

-- `neg = true` означает что к образующей добавляется минус
inductive Q8 where
| e (neg : Bool)
| i (neg : Bool)
| j (neg : Bool)
| k (neg : Bool)

-- Указание: в определении `mul` нужно сделать `match x, y with ...` и разобрать ≤ 16 случаев.
-- Булы можно складывать, сложение определено как xor.
-- После этого требуемые свойства должны доказываться разбором всех случаев
-- как-то так: `cases x <;> cases y <;> rfl`
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
/-- Задача 3: Q8 не изоморфна D4.

Указание: в группе Q8 есть 6 различных элементов порядка 4, а в D4 всего 1. -/
example (φ : Q8 →* DihedralGroup 4) (ψ : DihedralGroup 4 →* Q8) (h1 : φ ∘ ψ = id) (h2 : ψ ∘ φ = id) :
    False := by
  sorry

/- Задача 4 (сложная): существует неабелева группа `G` в которой верно `x^3=1` для всех `x`.

Указание: нужная группа гуглится, но формализовать ее остается непросто. -/
namespace Problem3

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

end Problem3
