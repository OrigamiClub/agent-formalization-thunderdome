import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement* only. The single theorem ends in `:= by sorry`;
nothing is proved.
-/

namespace ImprovedSunflower

/-- A **sunflower with `r` petals** and core `core`, realised as a subfamily `P`.

`P` is a finite family of exactly `r` sets — its members are automatically pairwise
distinct because `P : Finset (Finset α)` — such that `s ∩ t = core` for any two
distinct members `s t ∈ P`.

Consequently the petals `s \ core` (`s ∈ P`) are pairwise disjoint, and every element
lying in at least two members of `P` lies in all of them.  Empty petals are allowed. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (core : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every ambient type `α`, every set
size `k ≥ 2`, every petal count `r ≥ 1`, and every finite family `W` of `k`-element
subsets of `α`, if
`|W| > (C * r * Real.log k) ^ k`
then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * Real.log k) ^ k`.

Encoding notes (see the accompanying `.md`):
* Sets are `Finset α`; the family is `W : Finset (Finset α)`; "cardinality exactly `k`"
  is `∀ s ∈ W, s.card = k`.
* `Real.log` is the natural logarithm; `Real.log (k : ℝ)` is `0` at `k = 1` and `k = 0`.
* The hypothesis `2 ≤ k` rules out the degenerate `k = 1` case, where the literal bound
  collapses to `0` and the statement would be false for `r ≥ 2`.  With `2 ≤ k` this is
  the standard form of the bound.  (A variant valid for all positive `k` replaces
  `Real.log k` by `max 1 (Real.log k)`.)
* `C` is existentially quantified *outside* the quantifier over `α, k, r, W`, so it is a
  genuine absolute constant.
* Distinctness of the `r` petals is encoded by `P.card = r` together with `P` being a
  `Finset`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ (core : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r core P := by
  sorry

end ImprovedSunflower
