/-
  Improved Sunflower Lemma  --  statement only.

  Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke:
  there is an absolute constant `C` such that for all positive integers `k` and
  `r`, every finite family `W` of sets, each of cardinality exactly `k`, with
  `|W| > (C * r * log k) ^ k` contains a sunflower with `r` petals.

  This file states the theorem and closes it with `sorry`; nothing is proved.

  `import Mathlib` is used for convenience; the statement only needs
  `Finset` cardinality API and `Real.log`
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`).
-/
import Mathlib

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `S` of sets is a **sunflower with core `Y`** when every two
distinct members of `S` meet in exactly `Y`.

Consequences (not part of the definition): the "petals" `s \ Y`, `s ∈ S`, are
pairwise disjoint, and every point lying in two members of `S` lies in all of
them.  The number of petals is `S.card`. -/
def IsSunflower [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s : Finset α⦄, s ∈ S → ∀ ⦃t : Finset α⦄, t ∈ S → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every type `α` with
decidable equality, all `k ≥ 2` and `r ≥ 1`, and every finite family
`W : Finset (Finset α)` whose every member has exactly `k` elements, if
`(C * r * Real.log k) ^ k < W.card` then some subfamily `S ⊆ W` consisting of
exactly `r` sets is a sunflower with some core `Y` (equivalently
`f (k, r) ≤ (C * r * log k) ^ k` for the sunflower function `f`).

Encoding notes:
* `Real.log` is the natural logarithm; the choice of base is immaterial since it
  is absorbed into `C`.
* The hypothesis `2 ≤ k` sidesteps the degenerate case `Real.log 1 = 0`: when
  `k = 1` every family of distinct singletons is already a sunflower, so no
  bound of the shape `(… · log k) ^ k` can hold.
* Distinctness of the `r` chosen sets is automatic from `S : Finset _` together
  with `S.card = r`.
* Petals are not required to be nonempty, which only weakens the conclusion. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ) →
        ∃ S ⊆ W, ∃ Y : Finset α, S.card = r ∧ IsSunflower S Y := by
  sorry

end ImprovedSunflower
