import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*; the theorem is closed with `sorry`.
-/

namespace Agent041

/-- A finite family `P` of finite sets is a **sunflower with `r` petals** when it
has exactly `r` (necessarily distinct) members and there is a common **core**
`Y : Finset α` such that any two *distinct* members of `P` meet exactly in `Y`.

Equivalently: all pairwise intersections of members of `P` coincide (their common
value being the core `Y`, which for `r ≥ 2` is also `⋂ s ∈ P, s`).  The **petals**
are the sets `s \ Y` for `s ∈ P`; they are pairwise disjoint, and every element
belonging to at least two members belongs to all of them.  Petals are allowed to
be empty (at most one of them can be, by distinctness).  This is exactly
Definition 1.1 of Alweiss–Lovett–Wu–Zhang. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧ ∃ Y : Finset α, ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, and every finite family `W` of finite sets each of cardinality exactly
`k`, if
`|W| > (C · r · log k) ^ k`
then `W` contains a sunflower with `r` petals (a subfamily `P ⊆ W` that
`IsSunflower r`).

Encoding decisions:
* **Sets** are `Finset α` over an arbitrary ambient type `α`; the **family** is a
  `Finset (Finset α)`.  Requiring `P.card = r` for the returned subfamily records
  that the `r` petals are genuinely distinct sets.
* **`log`** is `Real.log` (natural logarithm).  The base is immaterial: changing
  it rescales `C`.
* **Small `k`.**  `k = 1` is excluded because `Real.log 1 = 0` would make the
  bound `0`, which is false (any `r` distinct singletons form a sunflower).
  `k = 0` is excluded a fortiori.  Hence the hypothesis `2 ≤ k`.
* **The constant `C`** is existentially quantified *outside* all other
  quantifiers, so it cannot depend on `α`, `k`, `r`, or `W`.
* The cardinality bound is stated as an inequality of reals, coercing `W.card`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ P : Finset (Finset α), P ⊆ W ∧ IsSunflower r P := by
  sorry

end Agent041
