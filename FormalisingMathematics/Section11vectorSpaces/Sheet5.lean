import Mathlib

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
variable (I : Type) (e : Basis I k V)

example (A : V →ₗ[k] V) (h : ∀ B : V →ₗ[k] V, A ∘ₗ B = B ∘ₗ A) : ∃ c : k, A = c • .id := by
  -- `E i j` переводит базисный вектор `e i` в `e j`, а остальные в 0.
  let E (i j : I) : V →ₗ[k] V :=
    e.constr k (Finsupp.single i (e j))
  -- Подставим эти операторы в условие
  have h1 (i j : I) : A (e i) = (E j i) (A (e j)) := by
    calc
      _ = A ((E j i) (e j)) := by
        simp [E]
      _ = (E j i) (A (e j)) := by
        change (A ∘ₗ (E j i)) (e j) = ((E j i) ∘ₗ A) (e j)
        rw [h]
  by_cases h_nonempty : Nonempty I
  swap -- разберемся со случаем когда `I` пустой сначала
  · simp at h_nonempty
    use 0
    apply e.ext
    simp
  -- Если `I` не пустой, тогда возьмем некоторый базисный `i0` и покажем что нужный `c`
  -- это `i0`-координата `(A (e i0))`, т.е. значение в клетке `A[i0][i0]` если думать о `A` как о матрице
  obtain ⟨i0⟩ := h_nonempty
  let c := e.coord i0 (A (e i0))
  use c
  -- Покажем что для `e i0` соотношение работает
  have h2 : A (e i0) = c • (e i0) := by
    rw [h1 i0 i0]
    -- векторы равны если всех их координаты совпадают
    apply (LinearEquiv.injective e.repr)
    ext j
    simp
    -- нам понадобится иное представление `E i0 i0`, с которым цель становится очевидна
    -- может, можно и без него, не знаю
    let E' : V →ₗ[k] V := {
      toFun (v : V) := e.coord i0 v • e i0
      map_add' := by
        simp [add_smul]
      map_smul' := by
        simp [mul_smul]
    }
    have : (E i0 i0) = E' := by
      apply Basis.constr_eq
      intro i
      by_cases h : i = i0
      · simp [h, E']
      · rw [Finsupp.single_eq_of_ne (by symm; exact h)]
        simp [E']
        rw [Finsupp.single_eq_of_ne h]
        simp
    -- переписываем используя новое представление
    rw [this]
    simp [E', c]
  -- Для других базисных векторов `e i` соотношение следует из `h1` и `h2`.
  have h3 (i : I) : A (e i) = c • e i := by
    rw [h1 i i0, h2]
    simp [E]
  -- Раз соотношение верно на всех базисных векторах, значит оно верно и на всех векторах вообще
  apply e.ext
  simp
  exact h3
