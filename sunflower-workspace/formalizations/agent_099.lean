import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for all positive integers `k` and `r`,
every finite family `W` of `k`-element sets with `|W| > (C · r · log k)^k` contains
a sunflower with `r` petals.

This file contains the statement only; the proof is `sorry`.
-/

open scoped BigOperators

namespace ImprovedSunflower

/-- A subfamily `petals` of sets is a **sunflower with `r` petals and core `core`**
if it consists of exactly `r` (distinct) sets whose pairwise intersections all equal
`core`.

Encoding notes:
* The members are collected in a `Finset (Finset α)`, so distinctness of the `r`
  sets is automatic and is pinned down by `petals.card = r`.
* From `A ∩ B = core` for all `A ≠ B` one recovers the usual description: every
  element lying in at least two members lies in `core` (hence in all members that
  contain it), and the petals `A \ core` are pairwise disjoint. We do not demand
  the petals `A \ core` to be nonempty (the classical "family of `r` distinct
  sets" definition); at most one member can coincide with `core`. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (core : Finset α)
    (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
    ∀ ⦃A⦄, A ∈ petals → ∀ ⦃B⦄, B ∈ petals → A ≠ B → A ∩ B = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every type `α` with decidable
equality, all positive integers `k` and `r`, and every finite family `W` of subsets
of `α` each of cardinality exactly `k`, if
`(C · r · log k) ^ k < |W|`
then `W` contains a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` for an ambient type `α`; the family `W` is a `Finset (Finset α)`
  and `|W|` is `W.card`.
* `log` is the natural logarithm `Real.log`. The right-hand side is a real number and
  is compared with the natural number `W.card` via a coercion. For `k = 1` we have
  `Real.log 1 = 0`, so the hypothesis degenerates to `0 < |W|`; the constant `C`
  and the (uninteresting) small-`k` cases are absorbed into the existential over `C`.
* `C` is existentially quantified inside the statement, expressing "there is an
  absolute constant".
* The sunflower is exhibited as a subfamily `𝒮 ⊆ W` together with its core. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
        0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ core : Finset α, ∃ 𝒮 : Finset (Finset α),
            𝒮 ⊆ W ∧ IsSunflower r core 𝒮 := by
  sorry

end ImprovedSunflower
