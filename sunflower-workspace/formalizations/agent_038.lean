import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement* only. The single theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A *sunflower with `r` petals* and *core* `Y` is a finite family `S` of finsets such that

* `S` has exactly `r` members (in particular they are pairwise distinct);
* every member of `S` contains the core `Y`;
* any two distinct members of `S` intersect in exactly `Y`.

The petals are the sets `s \ Y` for `s ∈ S`. The conditions say precisely that the petals are
pairwise disjoint and disjoint from the core, i.e. every element lying in `≥ 2` members lies in
all of them. This is the notion appearing in the Erdős–Rado sunflower lemma and its quantitative
refinements. (Mathlib also carries a sunflower development in
`Mathlib/Combinatorics/SetFamily/Sunflower.lean`; we define the predicate locally to keep the
statement self-contained and independent of the exact Mathlib spelling.) -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (S : Finset (Finset α)) : Prop :=
  S.card = r ∧
  (∀ s ∈ S, Y ⊆ s) ∧
  (S : Set (Finset α)).Pairwise (fun A B => A ∩ B = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that, for every ambient type `α`, all integers `k ≥ 2`
and `r ≥ 1`, and every finite family `W` of `k`-element finsets over `α`, if

  `|W| > (C · r · log k) ^ k`

then `W` contains a sunflower with `r` petals. Equivalently the sunflower function satisfies
`f(k, r) ≤ (C · r · log k) ^ k`.

Encoding decisions:
* `log` is the natural logarithm `Real.log`; the choice of base is absorbed into `C`.
* We require `2 ≤ k`, so that `Real.log k > 0` and the displayed bound is meaningful. The cases
  `k = 0, 1` are degenerate (`log k ≤ 0`) and are governed by a separate elementary convention.
* `C` is existentially quantified at the front, encoding "there is an absolute constant `C`".
* Sets are `Finset α` over an arbitrary type `α`; cardinalities use `Finset.card`. The membership
  family `W : Finset (Finset α)` automatically records distinctness of its members.
* The hypothesis comparison is stated in `ℝ` (`W.card` cast to `ℝ`) since the right-hand side is
  real-valued. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * r * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (S : Finset (Finset α)), S ⊆ W ∧ IsSunflower r Y S := by
  sorry

end ImprovedSunflower
