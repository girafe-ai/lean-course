import Mathlib

/- Обращение по модулю -/

-- def invModuloAux (a m : Nat) (j : Nat) : Option Nat :=
--   if j == 0 then
--     none
--   else
--     if (a * j) % m == 1 then
--       some j
--     else
--       invModuloAux a m (j - 1)
-- termination_by j
-- decreasing_by
--   rename_i h1 _
--   simp at h1
--   omega

def invModuloAux (a m : Nat) (j : Nat) : Option Nat :=
  match j with
  | 0 => none
  | k + 1 =>
    if (a * (k + 1)) % m == 1 then
      some (k + 1)
    else
      invModuloAux a m k

def invModulo (a m : Nat) : Option Nat :=
  invModuloAux a m m

theorem invModulo_correct1 (a m x : Nat) (h : invModulo a m = some x) : (a * x) % m = 1 := by
  simp [invModulo] at h
  suffices ∀ j, invModuloAux a m j = some x → (a * x) % m = 1 by
    apply this _ h
  intro j h
  induction j with
  | zero =>
    simp [invModuloAux] at h
  | succ k ih =>
    simp [invModuloAux] at h
    split_ifs at h with h_if
    · simp at h
      rw [← h]
      exact h_if
    · exact ih h

theorem invModulo_correct2 (a m : Nat) (hm : 0 < m) (h : invModulo a m = none) : ¬ ∃ x, (a * x) % m = 1 := by
  simp [invModulo] at h
  have h_lemma : ∀ j, invModuloAux a m j = none → ∀ x ≤ j, (a * x) % m ≠ 1 := by
    intro j h x hx
    induction j with
    | zero =>
      simp at hx
      simp [hx]
    | succ k ih =>
      simp [invModuloAux] at h
      split_ifs at h with h_if
      by_cases hx' : x = k + 1
      · simp [hx', h_if]
      exact ih h (by omega)
  specialize h_lemma _ h
  by_contra! h_exists
  obtain ⟨x, hx⟩ := h_exists
  specialize h_lemma (x % m) (by apply le_of_lt; exact Nat.mod_lt x hm)
  rw [← Nat.mul_mod_mod] at hx
  contradiction

theorem invModulo_correct3 (a m : Nat) (hm : 1 < m) (h : a.Coprime m) : ∃ x, invModulo a m = some x := by
  have := Nat.exists_mul_emod_eq_one_of_coprime h hm
  by_contra! h
  cases h' : invModulo a m with
  | some y =>
    specialize h y
    contradiction
  | none =>
    have := invModulo_correct2 a m (by omega) h'
    contradiction
