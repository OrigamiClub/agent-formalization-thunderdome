import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*. The single theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A *sunflower with `r` petals and core `Y`*: a family `S` of exactly `r` finite sets such
that every two distinct members intersect in exactly `Y`.

Members of a `Finset (Finset α)` are automatically distinct, so distinctness of the petals is
built in. For `r ≥ 2` the pairwise condition forces `Y ⊆ A` for every `A ∈ S` (since
`Y = A ∩ B ⊆ A`), the petals `{A \ Y | A ∈ S}` are pairwise disjoint, and any element lying in
two members lies in all of them. Petals are not required to be nonempty; at most one member can
equal `Y`. -/
def IsSunflowerWith {α : Type*} (r : ℕ) (Y : Finset α) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ (S : Set (Finset α)).Pairwise fun A B => A ∩ B = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang, 2019; refined by Rao and by
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`, and every
finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C * r * log k) ^ k`
then `W` contains a sunflower with `r` petals: there exist a core `Y` and a subfamily `S ⊆ W`
with `IsSunflowerWith r Y S`.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * log k) ^ k`.

Encoding notes:
* `Real.log` is the natural logarithm; only the value of `C` depends on the choice of base.
* The constant `C` is existentially quantified at the front, expressing "there is an absolute
  constant": it is independent of `α`, `k`, `r`, and `W`.
* The degenerate range `k ≤ 1` is excluded: there `Real.log k ≤ 0`, and the content is trivial
  (`k = 1` just asks for `r` distinct singletons, which form a sunflower with core `∅`). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (S : Finset (Finset α)), S ⊆ W ∧ IsSunflowerWith r Y S := by
  sorry

end ImprovedSunflower
