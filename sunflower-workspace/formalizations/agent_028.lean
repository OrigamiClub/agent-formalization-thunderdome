/-
Agent 028 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
positive integers `k`, `r`, every finite family `W` of exactly-`k`-element sets
with `|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/

import Mathlib

namespace Agent028

variable {α : Type*} [DecidableEq α]

/-- A **sunflower with `r` petals** and **core** `Y` is a family `P` of exactly `r`
sets whose pairwise intersections all equal `Y`.

* `P : Finset (Finset α)`, so the `r` members are automatically distinct.
* The condition is equivalent to
  `(P : Set (Finset α)).Pairwise (fun S₁ S₂ => S₁ ∩ S₂ = Y)`.
* Every element lying in `≥ 2` members then lies in `Y` (hence in all members),
  and the petals `S \ Y` for `S ∈ P` are pairwise disjoint.  We do not require the
  petals to be nonempty (the standard convention). -/
def IsSunflower (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧ ∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- A family `W` **contains a sunflower with `r` petals** if some sub-family
`P ⊆ W` is a sunflower with `r` petals, for some core `Y`. -/
def ContainsSunflower (r : ℕ) (W : Finset (Finset α)) : Prop :=
  ∃ P ⊆ W, ∃ Y : Finset α, IsSunflower r Y P

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every `k ≥ 2` and every
`r ≥ 1`, any finite family `W` of `k`-element sets (over an arbitrary ambient
type `α`) with
`(C · r · log k) ^ k < |W|`
contains a sunflower with `r` petals.

Encoding notes:
* `C` is existentially quantified *outside* the quantifier over `α, k, r, W`, so it
  is genuinely absolute.
* Sets are `Finset α`; the family is `W : Finset (Finset α)`; cardinalities are
  `Finset.card`.  The hypothesis `∀ S ∈ W, S.card = k` fixes the uniform size.
* `Real.log` is the natural logarithm.  The base is irrelevant (a change of base
  is absorbed into `C`).  For `k ≥ 2` we have `Real.log k ≥ Real.log 2 > 0`, so
  the base of the power is positive.
* `k = 1` is excluded: `Real.log 1 = 0` collapses the displayed bound to `0`,
  which is too weak to force `|W| ≥ r`.  `k = 0` has no `k`-element sets of
  interest.  Standard statements of the improved bound likewise assume `k ≥ 2`.
* Equivalent "sunflower function" phrasing: `f(k, r) ≤ (C · r · log k) ^ k`, where
  `f(k, r)` is the least `N` such that every family of `N` distinct `k`-sets has a
  sunflower with `r` petals. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 0 < r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ContainsSunflower r W := by
  sorry

end Agent028
