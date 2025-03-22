import Mathlib

/-!
# Инструкция по выполнению первой контрольной работы.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

/-- Задача 1. Пропозициональная логика.

Тактика `tauto` запрещена.
-/
theorem problem1 (P Q R S : Prop) (h1 : P ∨ Q ↔ R ∨ S) (h2 : ¬ (P ∧ R)) (h3 : ¬ (Q ∧ S)) :
    (P ↔ S) ∧ (Q ↔ R) := by
  sorry

/-- Задача 2. Кванторы.

Комментарии:
* Это известный математический факт. Если не встречались до этого, можете загуглить доказательство.
* В Lean есть понятие coercion. Суть в том что если некоторые типы "вкладываются" в другие (например
  ℕ в ℤ, а ℤ в ℚ), то объекты можно тоже "протаскивать" в больший тип. Например, пусть есть `n : ℕ` и
  `q : ℚ`. Если мы напишем выражение `n * q` то Lean в нем протащит `n` в тип `ℚ` (умножение определяется
  только для аргументов одного типа). Под капотом он применит функцию `coe : ℕ → ℚ`, то есть `n * q` по
  будет интерпретировано как `(coe n) * q`, еще это обозначается стрелкой вверх: `↑n * q`. Обычно стрелки
  опускают потому что Lean автоматически понимает что и куда кастовать. Если нет, то проще написать type
  annotation, то есть как-то так: `(n : ℚ) * q`. Примеры лемм с коерциями, которые могут помочь в решении:
  `Int.eq_nat_or_neg`, `Rat.num_div_den`.
* Может пригодиться тактика `field_simp`.
-/
theorem problem2 (f : ℚ → ℚ) (hf : ∀ x y, f (x + y) = f x + f y) : ∃ c, ∀ x, f x = c * x := by
  sorry

open Function in
/-- Задача 3. Свойства функций и множества.

Комментарии:
* Нотация `f^[i]` означает `i` раз итерированную функцию `f`:
`f^[0] x = x`, `f^[1] x = f x`, `f^[2] x = f (f x)` и так далее.
Определяется это через функцию `Nat.iterate` (пригодиться для поиска лемм):
`f^[i] = Nat.iterate f i`.
* `Bijective f := Injective f ∧ Surjective f`
* Есть и другие связанные свойства функций и операции над ними, например `HasRightInverse`, `invFun`.
  Загляните в модули `Mathlib.Function.Defs`, `Mathlib.Function.Basic`, ``Mathlib.Function.Iterate`
  в документации.
* Эквивалентность типов (в смысле существования биекции) `A` и `B`, обычно выражают через предикат
`Equiv`. Для `Equiv A B` есть нотация `A ≃ B`. Посмотрите в документации как он устроен. Если
переформулировать задачу через `Equiv`, доказывать может стать гораздо проще потому что
для `Equiv` разработано больше "API" в библиотеке.
* Если не получается придумать нужную функцию `f` -- пишите мне в телеграм (@versham), подскажу!
-/
theorem problem3 : ∃ f : ℕ → ℕ, Bijective f ∧ ∀ n, n ∉ {f^[i] n | i ≥ 1} := by
  sorry

/- # Задача 4. Типы и индукция.

В этой задаче предлагается формализовать известный факт о том, что любую логическую формулу
можно переписать, пользуясь только одной бинарной операцией NAND: `x NAND y = NOT (x AND y)`.

Мы определяем типы `LogicalFormula` и `NAndFormula` логических формул составленных из
переменных, имеющих тип `Var`, констант `t` (истина) и `f` (ложь), и логических связок.
Функции `LogicalFormula.eval` и `NAndFormula.eval` "вычисляют" формулу подставляя вместо
каждой переменной `p` предикат `val p` и возвращают `Prop`. См. секцию `Example` ниже.

Вам нужно определить `NAndFormula.eval` и доказать теорему о том, что любое утверждение,
кодирумое какой-то формулой `φ : LogicalFormula`, можно закодировать при помощи
некоторой `ψ : NAndFormula`.
-/

inductive LogicalFormula (Var : Type)
  | var (p : Var)
  | t
  | f
  | not (x : LogicalFormula Var)
  | and (x y : LogicalFormula Var)
  | or (x y : LogicalFormula Var)

def LogicalFormula.eval {Var : Type} (φ : LogicalFormula Var) (val : Var → Prop) : Prop :=
  match φ with
  | var p => val p
  | t => True
  | f => False
  | not x => ¬ x.eval val
  | and x y => x.eval val ∧ y.eval val
  | or x y => x.eval val ∨ y.eval val

section Example
-- В этой секции мы приведем пример "использования" определений выше.
-- Это должно дать больше понимания

namespace hidden -- обернем все в namespace чтобы не выносить определения отсюда

/-- Пусть у нас будет всего две переменные: `p` и `q` -/
inductive TwoVars
| p
| q

/-- Формула `p` -/
def formulaP : LogicalFormula TwoVars :=
  .var TwoVars.p

/-- Формула `q` -/
def formulaQ : LogicalFormula TwoVars :=
  .var TwoVars.q

/-- Формула `¬ q` -/
def formulaNotQ : LogicalFormula TwoVars :=
  .not formulaQ

/-- Формула `p ∨ ¬ q` -/
def formulaPOrNotQ : LogicalFormula TwoVars :=
  .or formulaP formulaNotQ

/- Чтобы придать формулам логический смысл, нужно подставить вместо переменных какие-то утверждения. -/
def P : Prop := ∃ n : ℕ, n + 1 = 0
def Q : Prop := ∃ n : ℕ, n - 1 = 0

/-- Вместо `p` подставим утверждение `P`, вместо `q` -- `Q`. -/
def val (var : TwoVars) : Prop := match var with
  | .p => P
  | .q => Q

/-- Тогда результат подстановки будет эквивалентен `P ∨ ¬ Q`, как и ожидалось. -/
example : formulaPOrNotQ.eval val ↔ P ∨ ¬Q := by
  -- распаковываем все определения при помощи `simp`
  simp [LogicalFormula.eval, formulaPOrNotQ, formulaP, formulaQ, formulaNotQ, val]

end hidden

end Example

inductive NAndFormula (Var : Type)
  | var (p : Var)
  | t
  | f
  | nand (x y : NAndFormula Var)

def NAndFormula.eval {Var : Type} (φ : NAndFormula Var) (val : Var → Prop) : Prop :=
  sorry

theorem problem4 {Var : Type} (φ : LogicalFormula Var) : ∃ ψ : NAndFormula Var, ∀ val : Var → Prop, φ.eval val ↔ ψ.eval val := by
  sorry
