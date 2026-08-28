import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*.  The single theorem ends in
`:= by sorry`; nothing is proved.
-/

namespace ImprovedSunflower

/-- A **sunflower with core `Y`**: a family `S` of finite sets all of whose
pairwise intersections equal `Y`.

Equivalently, the "petals" `A \ Y` for `A ∈ S` are pairwise disjoint, and
every element that lies in at least two members of `S` lies in *all* of
them.  Following the usual convention (and Mathlib's `Finset.IsSunflower`,
if that is indeed its name), no petal is required to be nonempty, so that
every subfamily of a sunflower is again a sunflower. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃A : Finset α⦄, A ∈ S → ∀ ⦃B : Finset α⦄, B ∈ S → A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for all positive integers `k`
and `r`, every finite family `W` of sets each of cardinality exactly `k`
with
  `|W| > (C · r · (log k + 1)) ^ k`
contains a sunflower with `r` petals: an `r`-element subfamily `S ⊆ W`
that is a sunflower for some core `Y`.

Encoding decisions (see the accompanying `.md` note for rationale):

* Sets are `Finset α` over an arbitrary ambient type `α` with decidable
  equality; the family is `W : Finset (Finset α)`, so its members — and
  hence the `r` sets of the returned subfamily `S` — are automatically
  distinct.  `S.card = r` records that there are exactly `r` petals.
* `Real.log` is the natural logarithm.  The bound uses `log k + 1` rather
  than `log k`; the `+ 1` makes the statement meaningful also for `k = 1`
  (where `log 1 = 0`) and is absorbed into `C`.  Changing the logarithm's
  base only rescales `C`.
* `C` is existentially quantified *before* the quantifier over the ambient
  type `α`, so it is a single absolute constant, independent of `α`, `k`,
  `r`, and `W`.
* Cardinalities are `Finset.card`.  Distinctness of the members of `S`
  needs no separate hypothesis (it is built into `Finset (Finset α)`).
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        0 < k → 0 < r →
        (∀ A ∈ W, A.card = k) →
        (C * (r : ℝ) * (Real.log (k : ℝ) + 1)) ^ k < (W.card : ℝ) →
        ∃ (S : Finset (Finset α)) (Y : Finset α),
          S ⊆ W ∧ S.card = r ∧ IsSunflower S Y := by
  sorry

end ImprovedSunflower
