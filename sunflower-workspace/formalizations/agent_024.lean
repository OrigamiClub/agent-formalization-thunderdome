import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with subsequent refinements by Rao and by
Bell–Chueluecha–Warnke.

This file states the theorem only.  Every declaration ends in `sorry`; nothing is proved.
-/

namespace ImprovedSunflower

/-- A finite family `petals` of finsets is a *sunflower with core `core`* when any two
distinct members meet in exactly `core`.

Consequences (not needed for the statement): the "petals" `S \ core` for `S ∈ petals` are
pairwise disjoint, and every element that lies in two members lies in all of them. -/
def IsSunflowerWith {α : Type*} [DecidableEq α]
    (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ ⦃S : Finset α⦄, S ∈ petals → ∀ ⦃T : Finset α⦄, T ∈ petals → S ≠ T → S ∩ T = core

/-- `HasSunflower W r` : the family `W` contains `r` distinct sets that form a sunflower
(with some core `core ⊆` each of them). -/
def HasSunflower {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ (petals : Finset (Finset α)) (core : Finset α),
    petals ⊆ W ∧ petals.card = r ∧ IsSunflowerWith petals core

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that, over any ambient type, for all positive
integers `k` and `r` and every finite family `W` of sets each of cardinality exactly `k`,
if
`|W| > (C · r · log (k + 1)) ^ k`
then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log (k + 1)) ^ k`.

Encoding notes:
* `log` is the natural logarithm `Real.log`.
* The argument `k + 1` (instead of `k`) only changes the value of the absolute constant,
  and it keeps the bound meaningful and true at `k = 1` (where `log 1 = 0`) and vacuously
  true at `k = 0`.
* `C` is existentially quantified *outside* the quantifier over the ambient type, so a
  single constant works uniformly for all set systems. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
        0 < k → 0 < r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
        HasSunflower W r := by
  sorry

end ImprovedSunflower
