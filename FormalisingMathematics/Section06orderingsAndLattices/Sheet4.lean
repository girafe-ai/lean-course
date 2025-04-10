/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Complete lattices

A lattice has sups and infs for all subsets with 2 elements. A *complete lattice* has sups
and infs for *every* subset (including infinite ones). An example would be the set of all
subsets of a fixed base set (or, in Lean speak, the type `Set X` of all subsets of a type `X`).
Other examples: all subgroups of a group, all subspaces of a vector space (and all subrings of a
ring, all subfields of a field...). A non-example would be the real numbers: we do say that the
reals are "complete" but we're talking about a different kind of completeness here
(an order-theoretic concept, not a metric space concept), and indeed unbounded subsets of ℝ like
the natural numbers do *not* have a sup. However the closed interval `[0,1]` would be an example
of a complete lattice in this sense.

If `L` is a complete lattice, and `S : Set L` is a subset of `L`, then its sup is `sSup S`
(the little `s` stands for "set") and its inf is `sInf S`. Here's the basic API for `sSup`:

`le_sSup : a ∈ S → a ≤ Sup S`
`sSup_le : (∀ (b : L), b ∈ S → b ≤ a) → sSup S ≤ a`

and you can probably guess the analogous names for `sInf` :-)

A special case: the empty set has a `sSup` and and an `sInf`, and if you think carefully
about this then you'll discover that this means that the lattice has a least element and a
greatest element. These elements are called `⊥` and `⊤` respectively, pronounced `bot`
and `top`.

`sSup_empty : Sup ∅ = ⊥`

See if you can prove basic things about `⊥` and `sSup` just using the API for `sSup`.
All these results are in the library, but it's a good exercise to prove them from
the axioms directly.

-/

-- Let `L` be a complete lattice and say `a` is a general element of `L`
variable (L : Type) [CompleteLattice L] (a : L)

-- this is called `bot_le`
example : ⊥ ≤ a := by
  exact bot_le

-- this is called `le_bot_iff`
example : a ≤ ⊥ ↔ a = ⊥ := by
  exact le_bot_iff



-- `sSup` is monotone.
-- this is called sSup_le_sSup
example {α : Type} (S T : Set (Set α)) : S ⊆ T → sSup S ≤ sSup T := by
  exact sSup_le_sSup
