import Mathlib
/-!
# Инструкция по выполнению ДЗ №6.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

/-- Задача 1. Один из законов дистрибутивности влечет другой. -/
example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

/-- Задача 2. Если две нормальные группы пересекаются по единице, то их элементы коммутируют между собой. -/
example (G : Type) [Group G] (N₁ N₂ : Subgroup G) [h1_normal : N₁.Normal] [h2_normal : N₂.Normal]
    (h : N₁ ⊓ N₂ = ⊥) : ∀ g₁ ∈ N₁, ∀ g₂ ∈ N₂, g₁ * g₂ = g₂ * g₁ := by
  sorry

open Equiv in
/-- Задача 3. Фактор группы перестановок по группе четных перестановок изоморфен {+1, -1}.

Указания:
* Посмотрите как определена `alternatingGroup`.
* Вообще в этой задаче старайтесь по максимуму использовать леммы из библиотеки,
  иначе рискуете надолго увязнуть. Хорошо повод понять как пользоваться loogle.
* `Fintype` и `DecidableEq` нужны чтобы использовать `alternatingGroup`,
  а вот `Nontrivial` здесь по существу, его придется использовать явно.

Комментарий: слово `noncomputable` здесь значит что определяемый объект не обязан быть
вычислимым и для не нужно генерировать код (на языке C). Для теорем (то есть определений чей тип имеет тип `Prop`)
код не генерируется никогда -- его и запускать смысла нет -- нам без разницы какой терм типа `P` она
вернет, главное что он доказывает `P`. Однако `Equiv α β` это `Type` а не `Prop`: он содержит функции
`α → β` и `β → α`, и Lean по умолчанию хочет сгенерировать для них код. Это не всегда возможно: например
если используется аксиома выбора. Поэтому мы помечаем определение `noncomputable` позволяя себе право
использовать при доказательстве все возможности невычислимой математики. -/
noncomputable example (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] : (Perm α) ⧸ (alternatingGroup α) ≃* ℤˣ := by
  sorry
