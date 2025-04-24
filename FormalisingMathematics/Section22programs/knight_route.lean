import Mathlib

/- Можно ли шахматным конем обойти всю доску начиная в углу? -/

-- SAT-solving: выполнима ли логическая формула?

abbrev Square := Fin 8 × Fin 8

abbrev Route := List Square

abbrev isKnightMove (x y : Square) : Prop :=
  |(x.1 : ℤ) - (y.1 : ℤ)| > 0 ∧
  |(x.2 : ℤ) - (y.2 : ℤ)| > 0 ∧
  |(x.1 : ℤ) - (y.1 : ℤ)| + |(x.2 : ℤ) - (y.2 : ℤ)| = 3

example : isKnightMove (0, 0) (1, 2) := by decide

structure IsValid (route : Route) : Prop where
  nonempty : route ≠ []
  start : route.getLast nonempty = (0, 0)
  knight : ∀ i : Fin 64, (h : i.val + 1 < route.length) → isKnightMove route[i] route[i + 1]
  surj : ∀ s : Square, s ∈ route

def intToFin (i : ℤ) (hi : 0 ≤ i ∧ i < 8) : Fin 8 :=
  ⟨i.toNat, by rw [Int.toNat_lt hi.left]; simp [hi.right]⟩

def getMoves (curRoute : Route) : List Square :=
  let (x, y) := curRoute.head!
  let possibleMoves : List Square := [
    ((x : ℤ) + 1, (y : ℤ) + 2),
    ((x : ℤ) + 2, (y : ℤ) + 1),
    ((x : ℤ) + 2, (y : ℤ) - 1),
    ((x : ℤ) + 1, (y : ℤ) - 2),
    ((x : ℤ) - 1, (y : ℤ) - 2),
    ((x : ℤ) - 2, (y : ℤ) - 1),
    ((x : ℤ) - 2, (y : ℤ) + 1),
    ((x : ℤ) - 1, (y : ℤ) + 2)
  ].filterMap fun (i, j) =>
    if h1 : (0 ≤ i ∧ i < 8) ∧ (0 ≤ j ∧ j < 8) then
      some (intToFin i h1.1, intToFin j h1.2)
    else
      none

  possibleMoves.filter fun s => s ∉ curRoute

mutual

  partial def findRouteAux (cur : Route) (moves : List Square) : Option Route :=
    if cur.length = 64 then
      some cur
    else
      let movesWithNextMoves := moves.zip (moves.map (fun move => getMoves (move :: cur)))
      let movesWithNextMoves := movesWithNextMoves.mergeSort (le := fun x y => x.2.length ≤ y.2.length)
      go cur movesWithNextMoves

  partial def go (cur : Route) (cands : List (Square × List Square)) : Option Route :=
    match cands with
    | [] => none
    | (move, nextMoves) :: candsTail =>
    match findRouteAux (move :: cur) nextMoves with
    | some route => some route
    | none =>
      go cur candsTail

end

def findRoute : Route :=
  (findRouteAux [(0, 0)] (getMoves [(0, 0)])).getD []

set_option pp.deepTerms true in
#eval! findRoute

lemma findRoute_eq : findRoute = [(6, 5), (7, 7), (5, 6), (4, 4), (2, 3), (3, 5), (1, 4), (0, 2), (2, 1), (4, 2), (5, 4), (3, 3), (5, 2), (7, 3), (6, 1),
    (4, 0), (3, 2), (5, 3), (3, 4), (4, 6), (2, 7), (0, 6), (2, 5), (0, 4), (1, 6), (3, 7), (4, 5), (2, 4), (4, 3),
    (2, 2), (1, 0), (3, 1), (5, 0), (7, 1), (6, 3), (7, 5), (6, 7), (5, 5), (7, 4), (6, 6), (4, 7), (2, 6), (0, 7),
    (1, 5), (0, 3), (1, 1), (3, 0), (5, 1), (7, 0), (6, 2), (4, 1), (6, 0), (7, 2), (6, 4), (7, 6), (5, 7), (3, 6),
    (1, 7), (0, 5), (1, 3), (0, 1), (2, 0), (1, 2), (0, 0)] := by
  native_decide

lemma ex2 : IsValid findRoute := by
  rw [findRoute_eq] -- unsafe
  constructor
  rotate_left
  all_goals decide

#print axioms ex2

lemma ex : IsValid [(6, 5), (7, 7), (5, 6), (4, 4), (2, 3), (3, 5), (1, 4), (0, 2), (2, 1), (4, 2), (5, 4), (3, 3), (5, 2), (7, 3), (6, 1),
    (4, 0), (3, 2), (5, 3), (3, 4), (4, 6), (2, 7), (0, 6), (2, 5), (0, 4), (1, 6), (3, 7), (4, 5), (2, 4), (4, 3),
    (2, 2), (1, 0), (3, 1), (5, 0), (7, 1), (6, 3), (7, 5), (6, 7), (5, 5), (7, 4), (6, 6), (4, 7), (2, 6), (0, 7),
    (1, 5), (0, 3), (1, 1), (3, 0), (5, 1), (7, 0), (6, 2), (4, 1), (6, 0), (7, 2), (6, 4), (7, 6), (5, 7), (3, 6),
    (1, 7), (0, 5), (1, 3), (0, 1), (2, 0), (1, 2), (0, 0)] := by
  constructor
  rotate_left
  all_goals decide

#print axioms ex
