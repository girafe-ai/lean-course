import Mathlib

/- Сортировка пузырьком -/

def checkSortedAux (arr : Array Int) (i : Nat) : Bool :=
  if h : i + 1 >= arr.size then
    true
  else
    if arr[i] > arr[i + 1] then
      false
    else
      checkSortedAux arr (i + 1)
termination_by arr.size - i

def checkSorted (arr : Array Int) : Bool :=
  checkSortedAux arr 0

lemma checkSortedAux_spec (arr : Array Int) (i : Nat) :
    checkSortedAux arr i = true ↔
    ∀ j ≥ i, (h : j + 1 < arr.size) → arr[j] ≤ arr[j + 1] := by
  sorry

lemma checkSortedAux_spec' (arr : Array Int) (i : Nat) :
    checkSortedAux arr i = true ↔
    ∀ j ≥ i, ∀ k, (hjk : k > j) → (h : k < arr.size) → arr[j] ≤ arr[k] := by
  sorry

theorem checkSorted_spec (arr : Array Int) : checkSorted arr = true ↔ arr.Pairwise (· ≤ ·) := by
  simp [checkSorted]
  rw [checkSortedAux_spec', Array.pairwise_iff_get]
  constructor
  · intro h
    by_contra! h
    obtain ⟨i, j, hij, h'⟩ := h
    simp at h
    specialize h i j (by omega) (by simp)
    simp at h'
    omega
  · simp
    intro h j k hjk hk
    specialize h ⟨j, by omega⟩ ⟨k, by omega⟩ (by simpa)
    simp at h
    exact h

def swapIfGt (arr : Array Int) (i : Nat) (h : i + 1 < arr.size) : Array Int :=
  if arr[i] > arr[i + 1] then
    arr.swap i (i + 1)
  else
    arr

lemma swapIfGt_size (arr : Array Int) (i : Nat) (h : i + 1 < arr.size) :
    (swapIfGt arr i h).size = arr.size := by
  simp [swapIfGt]
  split_ifs
  · simp
  · rfl

lemma swapIfGt_stable_of_gt (arr : Array Int) (i : Nat) (h : i + 1 < arr.size) (k : Nat)
    (hk1 : i + 1 < k) (hk2 : k < arr.size) :
    (swapIfGt arr i h)[k]'(by rw [swapIfGt_size]; assumption) = arr[k] := by
  simp [swapIfGt]
  split_ifs
  · apply Array.getElem_swap_of_ne <;> omega
  · rfl

def bubbleSortPassAux (arr : Array Int) (i : Nat) : Array Int :=
  if h : i + 1 ≥ arr.size then
    arr
  else
    let arr' := swapIfGt arr i (by omega)
    bubbleSortPassAux arr' (i + 1)
termination_by arr.size - i
decreasing_by
  rw [swapIfGt_size]
  omega

def bubbleSortPass (arr : Array Int) : Array Int :=
  bubbleSortPassAux arr 0

#eval bubbleSortPass #[3, 2, 4, 1]

noncomputable def inversionsNumber (arr : Array Int) : Nat :=
  Finset.card {(i, j) : Fin arr.size × Fin arr.size | (i < j) ∧ (arr[i] > arr[j])}

theorem swapIfGt_inversionsNumber_le (arr : Array Int) (i : Nat) (h : i + 1 < arr.size) :
    inversionsNumber (swapIfGt arr i h) ≤ inversionsNumber arr := by
  simp [swapIfGt]
  split_ifs with h_if
  swap
  · rfl
  sorry

theorem swapIfGt_inversionsNumber_lt (arr : Array Int) (i : Nat) (h : i + 1 < arr.size)
    (h_gt : arr[i + 1] < arr[i]) :
    inversionsNumber (swapIfGt arr i h) < inversionsNumber arr := by
  sorry

lemma bubbleSortPassAux_inversionsNumber_le (arr : Array Int) (j : Nat) :
    inversionsNumber (bubbleSortPassAux arr j) ≤ inversionsNumber arr := by
  sorry

lemma bubbleSortPass_inversionsNumber_lt (arr : Array Int) (h : ¬ arr.Pairwise (· ≤ ·)) :
    inversionsNumber (bubbleSortPass arr) < inversionsNumber arr := by
  contrapose! h
  rw [Array.pairwise_iff_get]
  simp
  simp [bubbleSortPass] at h
  suffices ∀ i, (h : i + 1 < arr.size) → arr[i] ≤ arr[i + 1] by
    sorry
  intro i hi
  suffices arr[i] ≤ arr[i + 1] ∧ inversionsNumber arr ≤ inversionsNumber (bubbleSortPassAux arr i) by tauto
  induction i with
  | zero =>
    simp [h]
    unfold bubbleSortPassAux at h
    simp [show ¬ (0 + 1 ≥ arr.size) by omega] at h
    by_contra! h'
    have := swapIfGt_inversionsNumber_lt _ _ _ h'
    have := bubbleSortPassAux_inversionsNumber_le (swapIfGt arr 0 (by omega)) 1
    omega
  | succ i ih =>
    have h : inversionsNumber arr ≤ inversionsNumber (bubbleSortPassAux arr (i + 1)) := by
      specialize ih (by omega)
      obtain ⟨h1, h2⟩ := ih
      unfold bubbleSortPassAux at h2
      simp [show ¬ (arr.size ≤ i + 1) by omega] at h2
      simp [swapIfGt, show ¬ (arr[i + 1] < arr[i]) by omega] at h2
      exact h2
    refine ⟨?_, h⟩
    -- copy-paste from above
    unfold bubbleSortPassAux at h
    simp [show ¬ (arr.size ≤ i + 1 + 1) by omega] at h
    by_contra! h'
    have := swapIfGt_inversionsNumber_lt _ _ _ h'
    have := bubbleSortPassAux_inversionsNumber_le (swapIfGt arr (i + 1) (by omega)) (i + 1 + 1)
    omega

def bubbleSort (arr : Array Int) : Array Int :=
  if checkSorted arr then
    arr
  else
    let arr' := bubbleSortPass arr
    bubbleSort arr'
termination_by inversionsNumber arr
decreasing_by
  apply bubbleSortPass_inversionsNumber_lt
  rw [← checkSorted_spec]
  assumption

#eval bubbleSort #[3, 2, 4, 1]
#eval! bubbleSort #[3, 2, 4, 1]

theorem bubbleSort_sorted (arr : Array Int) : (bubbleSort arr).Pairwise (· ≤ ·) := by
  generalize h_invs : inversionsNumber arr = invs
  induction' invs using Nat.strong_induction_on with k ih generalizing arr
  subst h_invs
  unfold bubbleSort
  split_ifs with h
  · rw [checkSorted_spec] at h
    exact h
  · simp
    apply ih (inversionsNumber (bubbleSortPass arr))
    · apply bubbleSortPass_inversionsNumber_lt
      rw [← checkSorted_spec]
      assumption
    · rfl

theorem bubbleSort_is_permutation (arr : Array Int) :
    ∃ σ : Equiv (Fin arr.size) (Fin (bubbleSort arr).size), ∀ i, (bubbleSort arr)[σ i] = arr[i] := by
  sorry

/- Real-world monadic bubble sort -/

def bubbleSortM (arr : Array Int) : Array Int := Id.run do
  let mut arr := arr
  let mut sortedFlag := false
  while !sortedFlag do
    sortedFlag := true
    for i in [:arr.size - 1] do
      if arr[i]! > arr[i + 1]! then
        sortedFlag := false
        arr := arr.swapIfInBounds i (i + 1)
  return arr

#eval bubbleSortM #[4, 1, 3, 2]

set_option profiler true

#eval bubbleSortM ((Array.range 4000).map (fun (x : ℕ) ↦ (x : ℤ))).reverse

#eval! bubbleSort ((Array.range 4000).map (fun (x : ℕ) ↦ (x : ℤ))).reverse
