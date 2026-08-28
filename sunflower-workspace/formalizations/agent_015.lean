/-
Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke).

Statement only.  Every theorem ends in `:= by sorry`; nothing is proved.
-/
import Mathlib

namespace ImprovedSunflower

/-- A finite family `P` of sets is a **sunflower with core `Y`** when any two
*distinct* members of `P` intersect in exactly `Y`.

Consequences of this definition (not part of it):
* every element that lies in at least two members of `P` lies in `Y`, hence in
  every member of `P`;
* the *petals* `S \ Y` for `S ∈ P` are pairwise disjoint.

The **number of petals** of such a sunflower is `P.card` (the members of a
`Finset` are automatically distinct, so no separate distinctness hypothesis is
needed). -/
def IsSunflower {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S : Finset α⦄, S ∈ P → ∀ ⦃T : Finset α⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for every integer `k ≥ 2`, every
integer `r ≥ 1`, and every finite family `W` of sets each of cardinality exactly
`k`, if
`|W| > (C · r · log k) ^ k`
then `W` contains a sunflower with `r` petals: there is an `r`-element subfamily
`P ⊆ W` and a core `Y` such that any two distinct members of `P` meet exactly
in `Y`.

Encoding notes:
* Sets are `Finset`s over an arbitrary ambient type `α`; the family is
  `W : Finset (Finset α)`.  The constant `C` is quantified *outside* the
  quantifier over `α`, so it is genuinely absolute (independent of the ambient
  type).
* `log` is the natural logarithm `Real.log`; the choice of base only rescales
  `C`.  The count `|W|` is compared to a real number via the coercion `ℕ → ℝ`.
* The hypothesis `2 ≤ k` avoids the degenerate regime `k ≤ 1`, where
  `Real.log k ≤ 0` makes the right-hand side vanish or misbehave.  (For `k = 1`
  one has the trivial exact value `f(1, r) = r`.)
* `1 ≤ r` matches "for all positive integers `r`".  For `r ≤ 2` the conclusion
  is trivial; the content is at `r ≥ 3`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ P ⊆ W, ∃ Y : Finset α, P.card = r ∧ IsSunflower P Y := by
  sorry

/-- Equivalent "sunflower function" phrasing.  With
`f k r := ` the least `N` such that every family of `N` distinct `k`-sets
contains an `r`-petal sunflower, the improved bound reads
`f k r ≤ (C · r · log k) ^ k`.  Here it is stated contrapositively as: any
family with more than `(C · r · log k) ^ k` members of size `k` already contains
the sunflower (same content as `improved_sunflower_lemma`, isolated as a named
bound for convenience). -/
theorem sunflower_function_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          ¬ (∃ P ⊆ W, ∃ Y : Finset α, P.card = r ∧ IsSunflower P Y) →
          (W.card : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
