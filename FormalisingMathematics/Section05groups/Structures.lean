import Mathlib

structure Point where
  x : ℕ
  y : ℕ

-- Эквивалентно
inductive Point' where
| mk (x : ℕ) (y : ℕ)


-- section Foo
local instance : Add Point where
  add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩


#check Inhabited

instance inst : Inhabited ℕ := by infer_instance

instance instInhabitedProd' (A B : Type) [hA : Inhabited A]
    [Inhabited B] : Inhabited (A × B) where
  default := (@Inhabited.default A hA, default)

example : Inhabited (ℕ × ℤ) := by infer_instance

#eval (⟨1, 2⟩ : Point) + (⟨3, 4⟩ : Point)
