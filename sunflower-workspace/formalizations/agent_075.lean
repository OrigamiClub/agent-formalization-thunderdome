/-
Agent 075 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
positive integers `k` and `r`, every finite family of `k`-element sets of
cardinality more than `(C · r · log k)^k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/
import Mathlib

open scoped BigOperators

namespace Agent075

/-- A family `S` of finsets is a **sunflower with core `Y`** when any two *distinct*
members meet in exactly `Y`.  Equivalently every element lying in `≥ 2` members lies
in all of them, and the *petals* `{A \ Y | A ∈ S}` are pairwise disjoint.

Distinctness of the members is automatic because `S : Finset (Finset α)`.
Petals are allowed to be empty (no nonemptiness is imposed). -/
def IsSunflowerWithCore {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ S → ∀ ⦃B⦄, B ∈ S → A ≠ B → A ∩ B = Y

/-- `S` is a **sunflower with `r` petals** if it is a sunflower for some core and has
exactly `r` members. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (r : ℕ) : Prop :=
  S.card = r ∧ ∃ Y : Finset α, IsSunflowerWithCore S Y

/--
**Improved sunflower lemma (statement).**

There is an absolute constant `C > 0` such that: for all positive integers `k` and
`r`, for every finite family `W` of finsets over an ambient type, if every member of
`W` has cardinality exactly `k` and

  `(C · r · max 1 (log k)) ^ k  <  |W|`,

then `W` contains a subfamily `S ⊆ W` that is a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient type `α` with `DecidableEq`; the family is
  `W : Finset (Finset α)`.
* `C` is existentially quantified and required positive.
* The logarithm is `Real.log`.  Since `Real.log k = 0` for `k ≤ 1` (and the informal
  statement quantifies over *all* positive `k`), the bound uses `max 1 (Real.log k)`
  so the `k = 1` instance stays meaningful; for large `k` this equals `Real.log k`.
* The size hypothesis is a strict inequality of reals, with `|W|` cast from `ℕ`.
* "Sunflower with `r` petals" is `IsSunflower S r` above: `|S| = r` together with an
  explicit core `Y` with all pairwise intersections equal to `Y`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ A ∈ W, A.card = k) →
          (C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k < (W.card : ℝ) →
          ∃ S : Finset (Finset α), S ⊆ W ∧ IsSunflower S r := by
  sorry

/--
Equivalent "sunflower function" phrasing.  Let `f k r` be the least `N` such that
*every* family of `k`-element finsets with more than `N` members contains a sunflower
with `r` petals (assuming such an `N` exists / packaged as an upper-bound statement).
The improved lemma gives `f k r ≤ (C r log k)^k`.

Here we state it directly: with the same constant `C`, the threshold
`⌈(C · r · max 1 (log k)) ^ k⌉` is an admissible value of the sunflower function,
i.e. exceeding it forces an `r`-petal sunflower.
-/
theorem improved_sunflower_lemma_threshold :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ A ∈ W, A.card = k) →
          ⌈(C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k⌉₊ < W.card →
          ∃ S : Finset (Finset α), S ⊆ W ∧ IsSunflower S r := by
  sorry

end Agent075
