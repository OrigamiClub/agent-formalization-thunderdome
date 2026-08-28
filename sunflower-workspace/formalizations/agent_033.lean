/-
  Agent 033 — Formalization of the *statement* of the improved sunflower lemma.

  Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao 2020 and
  by Bell–Chueluecha–Warnke 2021):

    There is an absolute constant `C` such that for all integers `k ≥ 2` and `r ≥ 1`,
    every finite family `W` of `k`-element sets with `|W| > (C · r · log k)^k`
    contains a sunflower with `r` petals.

  Statement only: the theorem ends in `:= by sorry`.
-/
import Mathlib

open scoped BigOperators

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/--
A family `W` of finite sets **contains a sunflower with `r` petals** when there is a
subfamily `P ⊆ W` of exactly `r` (necessarily distinct) sets and a common *core*
`Y` such that every two distinct members of `P` intersect in exactly `Y`.

This "all pairwise intersections coincide" formulation is equivalent to the usual
one (common core `Y ⊆ s` for each petal `s`, with the petals `s \ Y` pairwise
disjoint): if `s ∩ t = Y` for all distinct `s, t ∈ P` then `Y ⊆ s` for every
`s ∈ P` with `|P| ≥ 2`, and any `x ∈ (s \ Y) ∩ (t \ Y)` would lie in `s ∩ t = Y`,
a contradiction — so the petals are automatically pairwise disjoint. When the
members of `P` all have the same positive cardinality and `r ≥ 2`, the petals are
moreover nonempty, so no separate nonemptiness hypothesis is needed.
-/
def ContainsSunflower (r : ℕ) (W : Finset (Finset α)) : Prop :=
  ∃ (P : Finset (Finset α)) (Y : Finset α),
    P ⊆ W ∧ P.card = r ∧
      ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → s ∩ t = Y

/--
**Improved sunflower lemma (statement).**

There is an absolute constant `C > 0` such that: for every type `α` with decidable
equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family
`W : Finset (Finset α)` in which every set has cardinality exactly `k`, if
`(C · r · log k)^k < |W|` then `W` contains a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an arbitrary ambient type `α`; the family is
  `W : Finset (Finset α)`. Cardinalities are `Finset.card`.
* `C` is existentially quantified as a single real constant, independent of `α`,
  `k`, `r`, and `W`.
* The logarithm is `Real.log` (natural log). The base is immaterial: changing it
  rescales `C` by a constant factor, and `C` is existentially quantified.
* The bound `(C * r * Real.log k) ^ k` is compared against `(W.card : ℝ)` after
  casting.
* We require `2 ≤ k`. For `k = 1` we have `Real.log 1 = 0`, making the right-hand
  side `0`, and the conclusion (`r` distinct singletons forming a sunflower) would
  need `|W| ≥ r`, which `|W| > 0` does not give; for `k = 0` the "`k`-element set"
  hypothesis forces `W ⊆ {∅}`. The bound is the standard one precisely in the
  regime `k ≥ 2`.
* Distinctness of the `r` petals is automatic: they are the elements of a `Finset`
  `P` with `P.card = r`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflower r W := by
  sorry

/--
Equivalent "sunflower function" phrasing: writing `f (k, r)` for the least `N` such
that every family of `k`-element sets with more than `N` members contains a
sunflower with `r` petals, the improved bound reads `f (k, r) ≤ (C · r · log k)^k`.
Here it is stated directly as an upper bound on any family size that still avoids a
sunflower.
-/
theorem improved_sunflower_lemma_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          ¬ ContainsSunflower r W →
          (W.card : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
