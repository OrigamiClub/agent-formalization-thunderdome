import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*. The theorem is closed with `sorry`.
-/

/-- A finite family `petals` of finite subsets of `α` is a **sunflower with `r` petals and
core `core`** when it consists of exactly `r` distinct sets whose pairwise intersections all
coincide with `core`.

Membership in `Finset (Finset α)` makes the `r` members automatically distinct, and
`petals.card = r` pins down their number.

For `r ≥ 2` this condition is equivalent to the usual one: it implies `core ⊆ s` for every
`s ∈ petals` (any element of two distinct members lies in their intersection, hence in `core`)
and that the petals `s \ core` are pairwise disjoint (a shared element of `s \ core` and
`t \ core` would lie in `s ∩ t = core`). For `r ≤ 1` the intersection condition is vacuous,
which keeps the main theorem consistent in the degenerate `r = 1` case. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (core : Finset α)
    (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
    ∀ ⦃s⦄, s ∈ petals → ∀ ⦃t⦄, t ∈ petals → s ≠ t → s ∩ t = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for all positive integers `k` and `r`, every
finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* `W` is a `Finset (Finset α)` over an arbitrary ambient type `α`; finiteness and
  distinctness of members are then automatic, and `|W|` is `Finset.card`.
* `C` is existentially quantified *outside* the quantifier over `α`, `k`, `r`, so it is a
  genuine absolute constant.
* `log` is the natural logarithm `Real.log`. To keep the right-hand side well defined and
  non-degenerate at `k = 1` (where `log 1 = 0`), it is applied to `k + 1`; for `k ≥ 2` this
  only changes the value of the absolute constant `C`.
* The cardinality inequality is stated in `ℝ` after coercion. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 1 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (W.card : ℝ) > (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k →
          ∃ (core : Finset α) (petals : Finset (Finset α)),
            petals ⊆ W ∧ IsSunflower r core petals := by
  sorry
