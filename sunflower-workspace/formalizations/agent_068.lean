/-
Improved sunflower lemma (statement only).

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke: the sunflower function satisfies
`f(k, r) ≤ (C · r · log k)^k` for an absolute constant `C`.

This file states the theorem only; the proof is `sorry`.
-/
import Mathlib

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith P r Y` says that the finite family `P` of finite sets is a
*sunflower with `r` petals and core `Y`*: `P` has exactly `r` (necessarily distinct)
members, and any two distinct members intersect exactly in `Y`.

Consequences of this definition (not needed for the statement): the petals
`S \ Y` for `S ∈ P` are pairwise disjoint, and every element that lies in at
least two members of `P` lies in every member of `P`. Petals are allowed to be
empty (some member may equal `Y`). -/
def IsSunflowerWith (P : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop :=
  P.card = r ∧ ∀ ⦃S⦄, S ∈ P → ∀ ⦃T⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- `P` is a *sunflower with `r` petals* if it has some core `Y`. -/
def IsSunflower (P : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ Y : Finset α, IsSunflowerWith P r Y

/-- **Improved sunflower lemma.**
(Alweiss–Lovett–Wu–Zhang 2019; refinements by Rao and by Bell–Chueluecha–Warnke.)

There is an absolute constant `C > 0` such that for every integer `k ≥ 2`, every
integer `r ≥ 1`, every ambient type `α`, and every finite family `W` of
`k`-element subsets of `α`, if
`(C · r · log k)^k < |W|`
then some subfamily `P ⊆ W` is a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset`s over an arbitrary ambient type `α` with `DecidableEq`;
  the family is a `Finset (Finset α)`.
* `Real.log` is the natural logarithm. The statement is restricted to `k ≥ 2`
  so that `Real.log k > 0`; for `k = 1` the family of singletons needs the
  separate trivial bound `|W| ≥ r`.
* `C` is existentially quantified at the outermost level, so it cannot depend on
  `α`, `k`, `r`, or `W` — it is genuinely absolute.
* Cardinalities are `Finset.card`. Distinctness of the `r` petals is encoded by
  `P.card = r` (a `Finset` has distinct elements). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ P ⊆ W, IsSunflower P r := by
  sorry

end ImprovedSunflower
