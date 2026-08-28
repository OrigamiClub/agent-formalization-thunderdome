import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*; the theorem is closed with `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `S` of finite sets is a *sunflower with core `Y`* when every two
distinct members of `S` meet exactly in `Y`.

Consequences of this single condition (not needed for the statement, recorded for the
reader): the "petals" `s \ Y`, for `s ∈ S`, are pairwise disjoint; every element that
lies in at least two members lies in `Y`; and once `S` has at least two members we get
`Y ⊆ s` for every `s ∈ S`, so `Y` is contained in all of them.

The number of petals is `S.card`. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s₁ : Finset α⦄, s₁ ∈ S → ∀ ⦃s₂ : Finset α⦄, s₂ ∈ S → s₁ ≠ s₂ → s₁ ∩ s₂ = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`,
every finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C · r · log k) ^ k`, contains a sunflower with `r` petals: a subfamily
`S ⊆ W` with `|S| = r` together with a core `Y` such that any two distinct members of
`S` intersect exactly in `Y`.

Encoding notes:
* Sets are `Finset α` over an ambient `DecidableEq` type; the family is
  `W : Finset (Finset α)`.
* `log` is the natural logarithm `Real.log`; the size comparison is done in `ℝ`.
* `k ≥ 2` is assumed so that `Real.log k > 0` and the bound is non-degenerate
  (for `k = 1`, `log k = 0` and the inequality would read `|W| > 0`, which is false
  in general).
* `C` is existentially quantified outside the family/type quantifiers, capturing
  "there is an absolute constant".
* The members of `S` are automatically pairwise distinct because
  `S : Finset (Finset α)`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ S : Finset (Finset α), S ⊆ W ∧ S.card = r ∧ ∃ Y : Finset α, IsSunflower S Y := by
  sorry

end ImprovedSunflower
