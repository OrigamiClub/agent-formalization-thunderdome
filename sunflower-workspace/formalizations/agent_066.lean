import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for all `k ≥ 2` and `r ≥ 1`,
every finite family `W` of `k`-element sets with `|W| > (C · r · log k)^k`
contains a sunflower with `r` petals.

This file contains only the statement; the proof is `sorry`.
-/

open scoped BigOperators

/-- `IsSunflower r Y petals` says that `petals` is a family of exactly `r`
sets which form a sunflower with core `Y`:

* there are exactly `r` sets (so, in particular, they are pairwise distinct),
* the core `Y` is contained in every set of the family,
* any two distinct sets of the family intersect in exactly `Y`.

Consequently every element lying in `≥ 2` of the sets lies in `Y` and hence in
all of them, and the petals `S \ Y` for `S ∈ petals` are pairwise disjoint.

(Mathlib may in the meantime have gained its own sunflower predicate, e.g. a
`Finset.IsSunflower` / `Sunflower` in `Mathlib.Combinatorics.SetFamily`; the
present self-contained definition is used to keep the statement unambiguous.) -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
  (∀ S ∈ petals, Y ⊆ S) ∧
  (∀ S ∈ petals, ∀ T ∈ petals, S ≠ T → S ∩ T = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that: for every type `α` with
decidable equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family
`W` of subsets of `α` each of cardinality exactly `k`, if
`(C · r · log k)^k < |W|` then `W` contains a subfamily that is a sunflower
with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`
for `k ≥ 2`.

Encoding notes:
* Sets are `Finset α`; a family is a `Finset (Finset α)`; cardinalities are
  `Finset.card`.
* `log` is the natural logarithm `Real.log`; the base only affects `C`.
* `k ≥ 2` is imposed so that `Real.log k > 0` and the bound is meaningful:
  for `k ≤ 1` one has `log k ≤ 0`, the displayed bound degenerates, and the
  statement as written would be false (`k = 1`: a family of one singleton with
  `r ≥ 2`); the `k = 1` case is elementary and handled separately.
* `C` is existentially quantified *inside* the theorem and *outside* the
  quantifier over `α`, so it is genuinely absolute.
* Distinctness of the `r` chosen sets is encoded by `petals.card = r` together
  with `petals ⊆ W`. Petals `S \ Y` are automatically nonempty (since
  `|S| = k ≥ 2` and `S ∩ T ⊊ S` for distinct equal-cardinality `S, T`), so
  nonemptiness is not stated. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ Y : Finset α, ∃ petals ⊆ W, IsSunflower r Y petals := by
  sorry
