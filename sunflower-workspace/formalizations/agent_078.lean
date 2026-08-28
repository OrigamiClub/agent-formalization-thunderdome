/-
Agent 078 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke):

  There is an absolute constant `C` such that for all positive integers `k` and
  `r`, every finite family `W` of sets, each of cardinality exactly `k`, with
  `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/
import Mathlib

namespace Agent078

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith r core P` says that the finite family of finsets `P` is a
sunflower with `r` petals and core `core`:

* `P` has exactly `r` members (which, being elements of a `Finset`, are pairwise
  distinct — this encodes the "`r` distinct sets `S₁, …, S_r`" requirement);
* any two distinct members of `P` intersect in exactly `core`.

The second clause is equivalent to the usual description "every element contained
in at least two of the sets is contained in all of them", and it makes the petals
`S \ core` for `S ∈ P` pairwise disjoint.  Petals are **not** required to be
nonempty. -/
def IsSunflowerWith (r : ℕ) (core : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃s : Finset α⦄, s ∈ P → ∀ ⦃t : Finset α⦄, t ∈ P → s ≠ t → s ∩ t = core

/-- **Improved sunflower lemma** (statement only).

There is an absolute constant `C > 0` such that for every ambient type `α` with
decidable equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family
`W : Finset (Finset α)` whose members all have exactly `k` elements, if
`|W| > (C · r · log k)^k` then `W` contains a sunflower with `r` petals: there is
a subfamily `P ⊆ W` and a core `core` with `IsSunflowerWith r core P`.

Encoding notes:
* Sets are `Finset`s over an arbitrary decidable-equality type `α`; the family is
  a `Finset (Finset α)`.  Cardinalities are `Finset.card`.
* `C` is existentially quantified inside the statement, so the theorem is
  self-contained.
* The logarithm is the natural logarithm `Real.log`.  The bound is compared in
  `ℝ` after coercing `W.card`.
* `k ≥ 2` is assumed so that `Real.log k > 0` and the bound is meaningful; for
  `k ≤ 1` the quantity `Real.log k` is `≤ 0` and the "`(C r log k)^k`" form of the
  bound degenerates (the `k = 1` case is handled separately in the literature).
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          ((C * (r : ℝ) * Real.log (k : ℝ)) ^ k) < (W.card : ℝ) →
          ∃ (P : Finset (Finset α)) (core : Finset α),
            P ⊆ W ∧ IsSunflowerWith r core P := by
  sorry

/-- Equivalent "sunflower function" phrasing.  If `f : ℕ → ℕ → ℕ` is a sunflower
function, i.e. every family of `k`-sets of size `> f k r` contains an `r`-petal
sunflower, then `f k r` is bounded by `(C · r · log k)^k` for an absolute
constant `C`. -/
theorem improved_sunflower_bound
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
      ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) → f k r < W.card →
        ∃ (P : Finset (Finset α)) (core : Finset α),
          P ⊆ W ∧ IsSunflowerWith r core P)
    (hmin : ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
      ∀ N : ℕ, (∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
        (∀ s ∈ W, s.card = k) → N < W.card →
          ∃ (P : Finset (Finset α)) (core : Finset α),
            P ⊆ W ∧ IsSunflowerWith r core P) → f k r ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end Agent078
