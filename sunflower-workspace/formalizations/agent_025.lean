import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  Every theorem ends in `:= by sorry`.
-/

open Real

/-- A *sunflower with `r` petals and core `Y`* is a family `P` of exactly `r` sets such that
any two distinct members of `P` intersect in exactly `Y`.

From this condition it follows automatically that the "petals" `s \ Y` (for `s ∈ P`) are
pairwise disjoint, and that every element contained in two members of `P` is contained in
all of them.  Petals are allowed to be empty. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃s : Finset α⦄, s ∈ P → ∀ ⦃t : Finset α⦄, t ∈ P → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every integer `k ≥ 2`, every integer
`r ≥ 1`, and every finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then some subfamily `P ⊆ W` is a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family `W` is a `Finset (Finset α)`.
* `Real.log` is the natural logarithm.  We restrict to `k ≥ 2` so that `log k > 0`
  (the cases `k = 0, 1` are degenerate / handled separately in the literature).
* `C` is existentially quantified so the statement asserts the existence of an absolute
  constant.
* Distinctness of the `r` members of the sunflower is encoded by `P.card = r` inside
  `IsSunflower` (a `Finset` has no repeats).
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

/-- Equivalent "sunflower function" phrasing.  Let `sunflowerFree k r` say that a family of
`k`-sets has no `r`-petal sunflower.  Then the size of any such family is bounded by
`(C · r · log k) ^ k`, i.e. `f(k, r) ≤ (C r log k) ^ k`. -/
theorem improved_sunflower_lemma_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (¬ ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P) →
          (W.card : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry
