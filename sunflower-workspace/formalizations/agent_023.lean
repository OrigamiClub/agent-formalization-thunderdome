import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The single theorem is closed with
`:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `T` of finite sets is a *sunflower with core `Y`* when any two
distinct members of `T` meet in exactly `Y`.

Equivalently, every element lying in at least two members of `T` lies in all of
them, and the "petals" `A \ Y` for `A ∈ T` are pairwise disjoint.  We use
`Set.Pairwise`, which quantifies only over *distinct* pairs, so the definition
imposes no constraint relating a set to itself. -/
def IsSunflower {α : Type*} [DecidableEq α] (T : Finset (Finset α)) (Y : Finset α) :
    Prop :=
  (T : Set (Finset α)).Pairwise fun A B => A ∩ B = Y

/-- `W` *contains a sunflower with `r` petals* when some subfamily `T ⊆ W`
consisting of exactly `r` members is a sunflower for some core `Y`.

Recording `T` as a `Finset` of cardinality `r` simultaneously encodes that the `r`
petals are pairwise distinct. -/
def ContainsSunflower {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) :
    Prop :=
  ∃ T : Finset (Finset α), T ⊆ W ∧ T.card = r ∧ ∃ Y : Finset α, IsSunflower T Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k` and
`r`, every finite family `W` of sets each of cardinality exactly `k` with

`(C * r * Real.log k) ^ k  <  |W|`

contains a sunflower with `r` petals.  Equivalently, the sunflower function
satisfies `f(k, r) ≤ (C * r * log k) ^ k`.

The constant `C` is quantified outermost so that it is genuinely independent of the
ambient type `α`, of `k`, of `r`, and of `W`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflower W r := by
  sorry

end ImprovedSunflower
