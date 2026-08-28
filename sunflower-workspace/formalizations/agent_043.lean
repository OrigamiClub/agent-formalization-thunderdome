import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace ImprovedSunflower

/-- A **sunflower with `r` petals and core `Y`** is a finite family `P` of `r`
(necessarily distinct) sets all of whose pairwise intersections are equal to the
fixed set `Y`.

Equivalent informal description: every element that lies in at least two members
of `P` lies in all of them, and the *petals* `S \ Y` (`S ∈ P`) are pairwise
disjoint.  When `r ≥ 2` this condition pins `Y` down as the common pairwise
intersection and forces `Y ⊆ S` for every `S ∈ P`.

Mathlib (as of this writing) has no sunflower predicate, so we define our own. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃S : Finset α⦄, S ∈ P → ∀ ⦃T : Finset α⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for every `k ≥ 2`, every `r ≥ 1`, and
every finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then some subfamily of `W` is a sunflower with `r`
petals.

Notes on the encoding.
* Sets are `Finset α` for an arbitrary ambient type `α` with decidable equality;
  the family `W` is a `Finset (Finset α)`, so distinctness of its members is
  automatic, as is distinctness of the `r` petals.
* `log` is the natural logarithm `Real.log`; changing the base only rescales the
  absolute constant `C`, so the choice is immaterial.
* The hypothesis `2 ≤ k` sidesteps the degenerate cases `k = 0, 1`, where
  `Real.log k = 0` makes the right-hand side vanish and the bound false
  (`f(1, r) = r`).  These small cases are handled separately in the literature
  and are not part of the interesting content.
* `C` is existentially quantified: "there is an absolute constant".
* The conclusion exhibits the core `Y` and the petal family `P ⊆ W`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end ImprovedSunflower
