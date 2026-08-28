/-
Improved sunflower lemma -- STATEMENT ONLY.

Alweiss-Lovett-Wu-Zhang (2019), with the bound refined by Rao and by
Bell-Chueluecha-Warnke:

  There is an absolute constant `C` such that for all positive integers `k`, `r`,
  every finite family `W` of `k`-element sets with `|W| > (C * r * log k) ^ k`
  contains a sunflower with `r` petals.  Equivalently the sunflower function
  satisfies  `f(k, r) <= (C * r * log k) ^ k`.

This file states the theorem and closes it with `sorry`.  Nothing is proved.
-/

import Mathlib

namespace ImprovedSunflower

/-- A finite family `T` of finsets is a **sunflower with core `Y`** when the
intersection of any two *distinct* members of `T` equals `Y`.

Consequences of this condition (for `T` with at least two members):
* `Y ⊆ s` for every `s ∈ T`;
* the "petals" `s \ Y` (`s ∈ T`) are pairwise disjoint;
* every element that lies in at least two members of `T` lies in all of them.

This mirrors `Finset.IsSunflower` in Mathlib
(`Mathlib/Combinatorics/SetFamily/Sunflower.lean`), which is likewise phrased as a
`Set.Pairwise` condition on the coerced family. -/
def IsSunflower {α : Type*} [DecidableEq α] (T : Finset (Finset α)) (Y : Finset α) :
    Prop :=
  (T : Set (Finset α)).Pairwise fun s₁ s₂ => s₁ ∩ s₂ = Y

/-- **Improved sunflower lemma**
(Alweiss-Lovett-Wu-Zhang 2019; bound refined by Rao and by Bell-Chueluecha-Warnke).

There is an absolute constant `C > 0` such that for every ambient type `α`, all
integers `k ≥ 2` and `r ≥ 1`, and every finite family `W : Finset (Finset α)` whose
members all have cardinality exactly `k`, if
`(C * r * Real.log k) ^ k < |W|` then `W` contains a **sunflower with `r` petals**:
a subfamily `T ⊆ W` with `|T| = r` (hence `r` distinct sets) together with a core
`Y` such that any two distinct members of `T` meet in exactly `Y`.

Encoding notes:
* `Real.log` is the natural logarithm; changing the base only rescales `C`.
* The hypothesis `2 ≤ k` excludes the degenerate case `k = 1`, where `Real.log k = 0`
  makes the right-hand side `0` and the bound would be false (`f(1, r) = r`).  The
  case `k = 0` is vacuous (only `∅` has cardinality `0`).
* The constant `C` is quantified first, so it is genuinely independent of `α`,
  `k` and `r`.
* Membership of a `Finset` already encodes distinctness, so `T.card = r` records
  that there are `r` distinct sets. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ T ⊆ W, T.card = r ∧ ∃ Y : Finset α, IsSunflower T Y := by
  sorry

end ImprovedSunflower
