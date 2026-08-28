import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the refined `(C r log k)^k` bound due to
Rao and to Bell–Chueluecha–Warnke.

This file contains only the *statement*; every theorem ends in `:= by sorry`.
-/

open scoped BigOperators

/-- A finite family `𝒮` of finite sets is a **sunflower with core `Y`** when every
two distinct members meet in exactly `Y`.

The *petals* are the sets `S \ Y` for `S ∈ 𝒮`.  The defining condition is
equivalent to: every element that lies in at least two members of `𝒮` lies in
`Y` (hence in all members), so the petals are pairwise disjoint.

A "sunflower with `r` petals" is then a subfamily `𝒮` with `𝒮.card = r`
admitting some core `Y` with `IsSunflower 𝒮 Y`.  Distinctness of the `r`
members is automatic, since `𝒮 : Finset (Finset α)`. -/
def IsSunflower {α : Type*} [DecidableEq α] (𝒮 : Finset (Finset α))
    (Y : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family is `W : Finset (Finset α)`.
* `C` is genuinely absolute: it is bound by the outermost `∃`, before `α`, `k`,
  `r`, and `W`.
* `log` is the natural logarithm `Real.log`.  The hypothesis `2 ≤ k` keeps
  `Real.log k > 0` and sidesteps the degenerate regime `k ∈ {0, 1}` where
  `log k ≤ 0`.  (For `k = 1` the lemma is the trivial statement that any `r`
  distinct singletons form a sunflower with empty core.)
* The conclusion produces a subfamily of *exactly* `r` members together with an
  explicit core `Y`.  Petals are not required to be nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧
            ∃ Y : Finset α, IsSunflower 𝒮 Y := by
  sorry

/-- Reformulation via the sunflower function `f k r`, defined as the least `N`
such that every family of `N` distinct `k`-sets contains a sunflower with `r`
petals.  Here it is packaged as: any bound `N` on family size that *forces* an
`r`-petal sunflower is at least the threshold, so the improved lemma says the
least such `N` is `≤ (C r log k)^k`.  We phrase it directly: if
`(C r log k)^k < N` then the forcing property holds at `N`. -/
theorem improved_sunflower_lemma_threshold :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r N : ℕ), 2 ≤ k → 1 ≤ r →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (N : ℝ) →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) → N ≤ W.card →
          ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧
            ∃ Y : Finset α, IsSunflower 𝒮 Y := by
  sorry
