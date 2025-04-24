import Mathlib

/- Задача о рюкзаке -/

/- 1. Problem statement -/

structure KnapsackProblem (n : ℕ) where
  values : Vector ℕ n
  weights : Vector ℕ n
  maxWeight : ℕ

structure KnapsackProblemSolution {n : ℕ} (problem : KnapsackProblem n) where
  isPicked : Vector Bool n
  cond : (∑ i : Fin n, if isPicked[i] then problem.weights[i] else 0) ≤ problem.maxWeight

def KnapsackProblemSolution.score {n : ℕ} {problem : KnapsackProblem n} (solution : KnapsackProblemSolution problem) : ℕ :=
  ∑ i : Fin n, if solution.isPicked[i] then problem.values[i] else 0

/- Empty solution -/

def emptySolution {n : ℕ} (problem : KnapsackProblem n) : KnapsackProblemSolution problem where
  isPicked := .replicate _ false
  cond := by simp

theorem emptySolution_score {n : ℕ} {problem : KnapsackProblem n} : (emptySolution problem).score = 0 := by
  simp [KnapsackProblemSolution.score, emptySolution]

/- Greedy solution -/

def greedySolution {n : ℕ} (problem : KnapsackProblem n) : KnapsackProblemSolution problem :=
  sorry

theorem greedySolution_score_ge {n : ℕ} {problem : KnapsackProblem n} :
    ∀ solution : KnapsackProblemSolution problem, solution.score ≤ 2 * (greedySolution problem).score := by
  sorry
