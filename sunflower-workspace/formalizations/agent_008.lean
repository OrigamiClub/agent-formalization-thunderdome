/-
  Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
  Bell–Chueluecha–Warnke).

  Statement only.  Every theorem ends in `:= by sorry`; nothing is proved.

  Informal statement being formalized:

    A *sunflower with `r` petals* is a family of `r` distinct sets `S₁, …, S_r`
    for which there is a *core* `Y` with `Sᵢ ∩ Sⱼ = Y` for all `i ≠ j`.

    There is an absolute constant `C` such that for all positive integers `k` and
    `r`, every finite family `W` of sets each of cardinality exactly `k` with
    `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.
-/

import Mathlib

open scoped BigOperators

namespace ImprovedSunflower

/--
`IsSunflower S Y` : the finite family of sets `S` is a sunflower with core `Y`.

Two conditions:
* the core is contained in every member of the family;
* any two distinct members of the family meet exactly in the core.

Consequences (not part of the definition): every point lying in `≥ 2` members
lies in all of them, and the petals `s \ Y` for `s ∈ S` are pairwise disjoint.

The number of *petals* is `S.card`; distinctness of the petals is automatic
because `S : Finset (Finset α)`.

Mathlib may already provide such a predicate (see the accompanying note); this
self-contained definition is used to keep the file independent of the exact
Mathlib spelling.
-/
def IsSunflower {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ s ∈ S, Y ⊆ s) ∧
  (∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y)

/--
**Improved sunflower lemma.**

There is an absolute constant `C > 0` (independent of the ambient type and of
`k`, `r`) such that:

for every type `α` with decidable equality, all naturals `k ≥ 2` and `r ≥ 1`,
and every finite family `W : Finset (Finset α)` in which every member has
cardinality exactly `k`, if

    (C · r · Real.log k) ^ k  <  |W|

then `W` contains a sunflower with `r` petals, i.e. there is a subfamily
`S ⊆ W` with `|S| = r` and a core `Y` making `S` a sunflower.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* `Real.log` is the natural logarithm.  The hypothesis `2 ≤ k` guarantees
  `Real.log k > 0`, keeping the bound meaningful; the cases `k = 0, 1`
  (where `log k` is `0` or undefined) are handled trivially by hand and are
  excluded here.
* `C` is existentially quantified inside the statement, capturing "there is an
  absolute constant".
* Cardinalities use `Finset.card`; the reals comparison casts `W.card` to `ℝ`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ S : Finset (Finset α), S ⊆ W ∧ S.card = r ∧
            ∃ Y : Finset α, IsSunflower S Y := by
  sorry

end ImprovedSunflower
