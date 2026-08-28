import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement* only.  The single theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `T` of finite sets is a **sunflower** (with `T.card` petals) if
there is a common **core** `Y` such that the intersection of any two distinct
members of `T` equals `Y`.

Equivalently: every element that lies in at least two members of `T` lies in all
of them, and the **petals** `s \ Y` (`s ∈ T`) are pairwise disjoint.  (When
`2 ≤ T.card` the core automatically satisfies `Y ⊆ s` for every `s ∈ T`, so the
two formulations agree.)

The members of a `Finset` are pairwise distinct, so no separate distinctness
hypothesis is needed. -/
def IsSunflower {α : Type*} [DecidableEq α] (T : Finset (Finset α)) : Prop :=
  ∃ Y : Finset α,
    ∀ ⦃s : Finset α⦄, s ∈ T → ∀ ⦃t : Finset α⦄, t ∈ T → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of finite sets, each of cardinality exactly `k`,
with
`|W| > (C * r * log k) ^ k`
contains a sunflower with `r` petals: a subfamily `T ⊆ W` with `T.card = r` that
is a sunflower in the sense of `IsSunflower`.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family `W` is a
  `Finset (Finset α)`.  `α` is quantified *inside* the statement so that `C` is
  genuinely absolute (independent of the ambient type).
* The logarithm is `Real.log`.  The hypothesis `2 ≤ k` avoids the degenerate
  regime `k ≤ 1` where `Real.log k ≤ 0` makes the threshold vacuous or wrong;
  this matches the way the bound is used in the literature.
* `T.card = r` encodes `r` distinct sets (elements of a `Finset` are distinct).
* Petals need not be required nonempty: since every member of `W` has the same
  cardinality `k`, for `r ≥ 2` no member is contained in another, so each petal
  `s \ Y` is automatically nonempty.
* The equivalent statement `f(k, r) ≤ (C r log k)^k` for the sunflower function
  `f` is exactly the contrapositive/threshold reading of this theorem. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ T ⊆ W, T.card = r ∧ IsSunflower T := by
  sorry

end ImprovedSunflower
