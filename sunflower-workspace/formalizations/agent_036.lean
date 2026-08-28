import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), "Improved bounds for the sunflower lemma",
with the bound subsequently refined by Rao and by Bell–Chueluecha–Warnke to

  `f(k, r) ≤ (C · r · log k) ^ k`

where `f(k, r)` is the least `N` such that every family of `N` distinct `k`-element
sets contains a sunflower with `r` petals.

This file contains the *statement only*: the theorem is closed with `sorry` and
nothing is proved.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- A finite family `petals` of finite sets is a **sunflower with core `core`**
when any two *distinct* members of the family meet in exactly `core`:

  `∀ A B ∈ petals, A ≠ B → A ∩ B = core`.

Consequences of this definition (for `petals.card ≥ 2`): every element lying in at
least two petals lies in all of them, `core ⊆ A` for each `A ∈ petals`, and the
"true petals" `A \ core` are pairwise disjoint.

The number of petals is `petals.card`.  Since the elements of a `Finset` are
automatically distinct, no separate distinctness hypothesis on the petals is
needed.  Nonemptiness of the petals is not imposed here (in the theorem below it
follows from every member having cardinality `k ≥ 2`). -/
def IsSunflower (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  (petals : Set (Finset α)).Pairwise fun A B => A ∩ B = core

end ImprovedSunflower

open ImprovedSunflower in
/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that, for every type `α` with decidable
equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family `W` of
`k`-element subsets of `α` with

  `(C · r · log k) ^ k < |W|`,

the family `W` contains a subfamily `T ⊆ W` of exactly `r` sets that form a
sunflower (with some core `Y`).

* `Real.log` is the natural logarithm.  The hypothesis `2 ≤ k` guarantees
  `Real.log k > 0`, so the right-hand side is a genuine positive bound; for
  `k = 1` it would collapse to `0` and the inequality would no longer be the
  intended statement, so that degenerate case is excluded.
* The constant `C` is genuinely absolute: it is existentially quantified
  *outside* the type `α`, the exponent `k`, the petal count `r`, and the family
  `W`.
* Distinctness of the `r` chosen sets is automatic from `T` being a `Finset` with
  `T.card = r`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ A ∈ W, A.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ T ⊆ W, T.card = r ∧ ∃ Y : Finset α, IsSunflower T Y := by
  sorry
