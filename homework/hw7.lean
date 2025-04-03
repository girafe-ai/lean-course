import Mathlib
/-!
# Инструкция по выполнению ДЗ №7.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Не стесняйтесь задавать вопросы в чате!
-/

namespace Problem1

/- Задача 1. Построить пример непрерывной биекции, обратная к которой не непрерывна. -/

def X : Type := sorry

instance : TopologicalSpace X := sorry

def Y : Type := sorry

instance : TopologicalSpace Y := sorry

noncomputable def f : X ≃ Y := sorry

example : Continuous f ∧ ¬ Continuous f.symm := by
  sorry

end Problem1

section Problem2

/- Задача 2. Пусть `φ` -- такой оператор `V → V`, что `φ² = φ`. Тогда `V = ker φ ⊕ im φ`. -/

variable (𝕜 : Type) [Field 𝕜] (V : Type) [AddCommGroup V] [Module 𝕜 V]

example (φ : V →ₗ[𝕜] V) (h : φ.comp φ = φ) :
    (LinearMap.ker φ) ⊓ (LinearMap.range φ) = ⊥ ∧ (LinearMap.ker φ) ⊔ (LinearMap.range φ) = ⊤ := by
  sorry

end Problem2
