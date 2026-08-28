import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The single theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `P` of finsets is a **sunflower with core `Y`** when
* `Y` is contained in every member of `P`, and
* any two distinct members of `P` intersect in exactly `Y`.

Equivalently: every point lying in at least two members of `P` lies in all of them, and the
"petals" `s \ Y` (for `s ∈ P`) are pairwise disjoint.  The first conjunct is redundant as soon
as `P` has at least two elements, but it makes the degenerate cases `P.card ≤ 1` behave sensibly. -/
def IsSunflower [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ s ∈ P, Y ⊆ s) ∧
    ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → s ∩ t = Y

/-- `W` **contains a sunflower with `r` petals** if some `r`-element subfamily `P ⊆ W` is a
sunflower for some core `Y`.

Since `P : Finset (Finset α)`, the condition `P.card = r` already encodes that the `r` petals
are pairwise distinct sets, so no separate distinctness hypothesis is needed. -/
def ContainsSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ P.card = r ∧ IsSunflower P Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for every `k ≥ 2` and every `r ≥ 1`, every finite
family `W` of sets, each of cardinality exactly `k`, with

`(C * r * Real.log k) ^ k  <  W.card`

contains a sunflower with `r` petals.  (Writing `f k r` for the sunflower function, this says
`f k r ≤ (C * r * Real.log k) ^ k`.)

Encoding decisions:
* Sets are modelled as `Finset α` over an arbitrary ambient type `α`; the family is
  `W : Finset (Finset α)`, and "finite family" is automatic.
* `Real.log` is the natural logarithm; changing the logarithm base only rescales `C`.
* Cardinalities are `Finset.card`, compared in `ℝ` via the obvious coercions.
* The hypothesis `2 ≤ k` is essential: for `k ≤ 1` one has `Real.log k ≤ 0`, so the right-hand
  side is `≤ 0` and no choice of constant can make the statement true (already `k = 1` needs
  `W.card ≥ r`).
* `C` is quantified *outside* the quantifiers over `k`, `r`, `α`, `W`, i.e. it is one absolute
  constant, exactly as in "there is an absolute constant `C` such that ...". -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ContainsSunflower W r := by
  sorry

end ImprovedSunflower
