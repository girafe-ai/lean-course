import Mathlib

/-!
# Вторая контрольная работа.
Вам предлагается заменить `sorry` на определения и валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

namespace Problem1

/- ## Задача 1. Бесконечная диэдральная группа инъективно вкладывается в группу 2x2 матриц.

Про саму группу можно прочитать в Википедии: https://en.wikipedia.org/wiki/Infinite_dihedral_group.

Указания:
* Тип `GL n ℚ` -- это subtype типа `Martix n n ℚ` с доп. условием на обратимость матрицы.
* Для задания матриц в GL удобно пользоваться функцией `Matrix.GeneralLinearGroup.mkOfDetNeZero`.
* Когда нужно доказать равенство двух матриц из `GL n ℚ` удобно подняться из suptype обратно в исходный тип
  `Matrix n n ℚ` и, к примеру, воспользоваться `ext`. Для этого можно использовать `rw [← Units.eq_iff]`
  (`Units α` это тип обратимых элементов типа `α`)
* Если в контексте есть переменная `x : Fin n` то тактика `fin_cases x` сделает из текущей цели n целей
  для каджого значения `x`.
-/

universe u v in
/-- `simp`-лемма которая должна быть в Mathlib, но ее там пока нет. -/
@[simp]
lemma Matrix.GeneralLinearGroup.mkOfDetNeZero_coe {n : Type u} [DecidableEq n] [Fintype n] {K : Type v} [Field K]
    (A : Matrix n n K) (h : A.det ≠ 0) : (Matrix.GeneralLinearGroup.mkOfDetNeZero A h : Matrix n n K) = A :=
  rfl

/-- Гомоморфизм из бесконечной диеэдральной группы в GL₂(ℚ). -/
def φ : DihedralGroup 0 →* (GL (Fin 2) ℚ) where
  toFun x := sorry
  map_one' := by
    sorry
  map_mul' := by
    sorry

/-- Он инъективен. -/
example : Function.Injective φ := by
  sorry

end Problem1

namespace Problem2

/- ## Задача 2. Оператор проекции вдоль вектора.
Для каждого вектора `v` есть оператор `A`, оставляющий `v` на месте и проецирующий все пространство на
прямую порожденную вектором `v`.

Указание на всякий случай: в евклидовом пространстве такой оператор естественно строится при помощи
скалярного произведения, но здесь его нет. Нужно пользоваться базисом.
-/

variable (k : Type) {V I : Type} [Field k] [AddCommGroup V] [Module k V] {e : Basis I k V}

example (v : V) : ∃ A : V →ₗ[k] V, A v = v ∧ ∀ u : V, ∃ c : k, A u = c • v := by
  sorry

end Problem2

namespace Problem3

/- ## Задача 3. Сумма нечетных биномиальных коэффициентов.
Нужно доказать что сумма биномиальных коэффициентов (в Mathlib это `Nat.choose`) с нечетными
нижними индексами и верхним `2n` равна `2^(2n - 1)`.

Указания:
* Запрос "Finset.sum, Nat.choose" в loogle покажет какие суммы содержащие биномиальные коэффиценты
  уже есть в библиотеке. Немного их покрутив можно доказать утверждение.
-/

example (n : ℕ) (hn : 0 < n) : ∑ m ∈ Finset.range n, Nat.choose (2 * n) (2 * m + 1) = 2^(2*n - 1) := by
  sorry

end Problem3

namespace Problem4

/- ## Задача 4. В группе кватернионов Q₈ существует наименьшая нетривиальная подгруппа.

Указание: для работы с `ZMod` пригодится тактика `reduce_mod_char`.
-/

/-- Кажется никакие умные тактики не умеют доказывать это, поэтому приведу доказательство здесь.
Может оказаться полезным. -/
example : (2 : ZMod 4) ≠ 0 := by
  intro h
  simp [← ZMod.val_eq_zero, ZMod.val_two_eq_two_mod] at h

example : ∃ H : Subgroup (QuaternionGroup 2),
    H ≠ ⊥ ∧ ∀ H' : Subgroup (QuaternionGroup 2), H' ≠ ⊥ → H ≤ H' := by
  sorry

end Problem4
