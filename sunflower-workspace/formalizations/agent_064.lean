/-
Agent 064 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
positive integers `k` and `r`, every finite family `W` of sets each of size
exactly `k` with `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/
import Mathlib

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite subfamily `P` of sets is a **sunflower with `r` petals** when it has
exactly `r` members (automatically distinct, being elements of a `Finset`) and there
is a single *core* set `Y` with `S ∩ T = Y` for every pair of distinct members
`S, T ∈ P`.

Consequences (not part of the definition): each `Y ⊆ S` for `S ∈ P`, every element
lying in at least two members of `P` lies in all of them, and the *petals* `S \ Y`
(`S ∈ P`) are pairwise disjoint. -/
def IsSunflower [DecidableEq α] (r : ℕ) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∃ Y : Finset α, ∀ ⦃S⦄, S ∈ P → ∀ ⦃T⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refinements by Rao and
by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every pair of positive integers
`k`, `r`, every type `α`, and every finite family `W : Finset (Finset α)` of sets each
of cardinality exactly `k`, if

  `(C * r * max (Real.log k) 1) ^ k < |W|`

then some subfamily `P ⊆ W` is a sunflower with `r` petals.

Encoding notes:
* `log` is the natural logarithm `Real.log`. The literal informal bound `(C r log k)^k`
  degenerates at `k = 1` (`log 1 = 0`); replacing the factor by `max (Real.log k) 1`
  makes the statement correct for every positive `k` while agreeing with `Real.log k`
  for all `k ≥ 3`, the remaining two values being absorbed into `C`.
* `C` is existentially quantified at the front, and the type `α` is quantified *after*
  `C`, so `C` is genuinely absolute (independent of `α`, `k`, `r`, `W`).
* Cardinalities are `Finset.card`; distinctness of the `k`-sets in `W` and of the
  `r` petals is automatic from the `Finset` encoding. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)),
          (∀ S ∈ W, S.card = k) →
          (C * r * max (Real.log k) 1) ^ k < (W.card : ℝ) →
          ∃ P ⊆ W, IsSunflower r P := by
  sorry

end ImprovedSunflower
