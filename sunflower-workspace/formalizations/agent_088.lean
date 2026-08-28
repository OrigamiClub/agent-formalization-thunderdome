import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith r petals core` says that `petals` is a *sunflower with `r` petals* and
core `core`: it consists of exactly `r` (hence pairwise distinct) sets, and any two distinct
members intersect exactly in `core`.

Consequences (not part of the definition): every element lying in at least two members lies
in all of them, and the "petals" `S \ core` for `S ∈ petals` are pairwise disjoint. When
`2 ≤ r` the definition already forces `core ⊊ S` for each member `S`, so the set-theoretic
petals are nonempty automatically; we therefore do not add that as a hypothesis. -/
def IsSunflowerWith (r : ℕ) (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  petals.card = r ∧
    ∀ ⦃A⦄, A ∈ petals → ∀ ⦃B⦄, B ∈ petals → A ≠ B → A ∩ B = core

end ImprovedSunflower

open ImprovedSunflower in
/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`, every
finite family `W` of `k`-element sets with `|W| > (C · r · log k) ^ k` contains a sunflower
with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset`s over an arbitrary ambient type `α`; the family `W` is a
  `Finset (Finset α)`, so its members are automatically pairwise distinct, and so are the
  members of any `T ⊆ W`.
* `Real.log` is the natural logarithm; the base is irrelevant, since a change of base only
  rescales the absolute constant `C`.
* We require `2 ≤ k`: for `k ≤ 1` the stated bound is simply false, e.g.
  `f (1, r) = r > 0 = (C · r · log 1) ^ 1`.
* `C` is existentially quantified inside the statement (an absolute constant, independent of
  `α`, `k`, `r`, and `W`).
* Cardinality is `Finset.card`; the strict inequality `|W| > (C r log k)^k` is written with
  the real-number cast of `W.card`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ A ∈ W, A.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ T ⊆ W, ∃ Y : Finset α, IsSunflowerWith r T Y := by
  sorry
