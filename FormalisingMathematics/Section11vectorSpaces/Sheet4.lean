/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-!

# Bases and matrices

Here is some API for bases of a vector space, and its relation to matrices.

-/

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]

/-

What *is* a basis for a vector space `V`? Mathematicians use the term to mean two
different things! Sometimes it's a subset of `V` (this is particularly common
if `V` is infinite-dimensional) and sometimes it's a *list* `[e₁, e₂, ..., eₙ]`.
The issue is whether the basis is *indexed* or not. In `mathlib`, bases are
indexed, so we have an index type (e.g. `{1,2,3,...,n}`) and a basis
is a function from this type to `V` satisfying the axioms for a basis.

-/
-- Let `B` be a `k`-basis for `V` indexed by `I`.
variable (I : Type) (B : Basis I k V)

-- Lean is allowing for the possibility that `I` is infinite, which makes
-- the theory noncomputable, so let's switch on non-computable mathematics
noncomputable section

-- (I always do this when Lean complains something is not computable; this doesn't
-- mean that you can't do maths with it, it means that we're asking Lean to do things
-- for which there is no algorithm (e.g. picking a basis, especially in the infinite-dimensional
-- case)
-- If `(i : I)` then the basis element of `V` corresponding to `i` (i.e. the element eᵢ if
-- you're imagining i={1,2,3,...,n}) is `B i`
variable (i : I)

example : V :=
  B i

-- A general element of V is uniquely a `k`-linear combination of elements of the basis.
-- In the finite-dimensional case we just write `v = ∑ᵢ cᵢeᵢ`. In the infinite-dimensional
-- case a basis will be infinite, but you can't take infinite sums so from `v` we should
-- expect to get a finitely-supported function on `I`, i.e., an element of `I →₀ k`
-- which sends `i` to `cᵢ`. Conversely given a finitely supported function `f : I →₀ k`
-- we can make the element ∑ᵢf(i)eᵢ, this is a finite sum so makes sense, and
-- every element of `V` is uniquely of this form (because the `eᵢ` are a basis.

-- Given a basis `B` with index set `I`, the function `Basis.repr B`, or `B.repr`,
-- is the `k`-linear isomorphism from `V` to these finitely-supported functions.
example : V ≃ₗ[k] (I →₀ k) :=
  B.repr

-- If `I` is finite, then you can use the space of all functions `I → k` (because they're
-- all finitely-supported) but because `I →₀ k` isn't *equal* to `I → k` (they're just
-- in bijection when `I` is finite) we need a different function to do this.
example [Fintype I] : V ≃ₗ[k] I → k :=
  B.equivFun

-- If you want to see the coefficient of `B i` in the expansion of `v` in terms
-- of the basis `B`, you can write
example (v : V) : k :=
  B.repr v i

-- Again if `I` is finite, you can reconstruct `v` as `∑ B.repr v i • B i`, a sum over all `i`.
-- allow notation for sums
open BigOperators

example [Fintype I] (v : V) : ∑ i, B.repr v i • B i = v :=
  B.sum_repr v

-- You can also use `B.coord i`, which is the linear map from `V` to `k` sending a vector `V`
-- to the coefficient of `B i`
example : V →ₗ[k] k :=
  B.coord i

-- Now let `W` be another `k`-vector space
variable (W : Type) [AddCommGroup W] [Module k W]

-- Let's prove that any map `f` from `I` to `W` extends uniquely to a linear map `φ` from `V` to `W`
-- such that forall `i : I`, `f i = φ (B i)`.
-- The three pieces of API you'll need:
-- the extension of `f : I → W` to a `k`-linear map `V →ᵢ[k] W` is `Basis.constr B k f`
example (f : I → W) : V →ₗ[k] W :=
  B.constr k f -- dot notation

-- The theorem that `B.constr k f` agrees with `f` (in the sense that `B.constr k f (B i) = f i`
-- is `Basis.constr_basis B k f i`
example (f : I → W) (i : I) : B.constr k f (B i) = f i :=
  B.constr_basis k f i

-- Finally, `Basis.ext` is the theorem that two linear maps are equal if they agree
-- on a basis of the source
lemma aux (φ ψ : V →ₗ[k] W) (h : ∀ i : I, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h

-- That should be all you need to do this!
example (f : I → W) : ∃! φ : V →ₗ[k] W, ∀ i, φ (B i) = f i := by
  use B.constr k f
  constructor
  · dsimp
    intro i
    exact B.constr_basis k f i
  · intro ψ hψ
    apply aux (B := B)
    simp
    assumption

-- Now say `C` is a basis of `W`, indexed by a type `J`
variable (J : Type) (C : Basis J k W)

-- If everything is finite-dimensional
variable [Fintype I] [Fintype J]

-- then linear maps from `V` to `W` are the same as matrices with rows
-- indexed by `I` and columns indexed by `J`
open Classical

-- apparently something isn't constructive here?
example : (V →ₗ[k] W) ≃ₗ[k] Matrix J I k :=
  LinearMap.toMatrix B C

-- check that this bijection does give what we expect.
-- Right-click on `LinearMap.toMatrix` and then "go to definition" to find
-- the API for `LinearMap.toMatrix`.
example (φ : V →ₗ[k] W) (i : I) (j : J) : ((LinearMap.toMatrix B C) φ) j i = C.repr (φ (B i)) j := by
  exact LinearMap.toMatrix_apply B C φ j i

example (A : V →ₗ[k] V) (h : ∀ B : V →ₗ[k] V, A.comp B = B.comp A) : ∃ c : k, A = c • .id := by
  -- для базисного B i берем оператор F i который все остальные базисные векторы обнуляет, а B i сохраняет
  let F (i : I) : V →ₗ[k] V :=
    let f : I →₀ V := Finsupp.single i (B i)
    B.constr k f
  -- Fi A (B i) = A Fi (B i) = A (B i)
  have h1 : ∀ i, A.comp (F i) = (F i).comp A := by
    solve_by_elim
  have h2 : ∀ i, (F i) (A (B i)) = A (B i) := by
    intro i
    specialize h1 i
    conv =>
      lhs
      change (F i ∘ₗ A) (B i)
    rw [← h1]
    simp [F]
  have h3 : ∀ i : I, ∃ c : k, A (B i) = c • (B i) := by
    intro i
    specialize h2 i
    have h4 : ∀ j, j ≠ i → B.repr (A (B i)) j = 0 := by
      intro j hji
      rw [← h2]
      generalize A (B i) = u
      simp [F]
      rw [Fintype.sum_eq_add_sum_compl i]
      have h5 : (Finsupp.single i 1) j = (0 : k) := by
        exact Finsupp.single_eq_of_ne (id (Ne.symm hji))
      simp [h5]
      apply Finset.sum_eq_zero
      intro x hx
      simp at hx
      suffices (B.repr ((Finsupp.single i (B i)) x)) j = 0 by
        simp [this]
      have h6 : (Finsupp.single i (B i)) x = 0 := by
        exact Finsupp.single_eq_of_ne fun a ↦ hx (id (Eq.symm a))
      rw [h6]
      simp
    sorry
  -- Нужно взять G i j который переставляет местами B i и B j
  sorry
