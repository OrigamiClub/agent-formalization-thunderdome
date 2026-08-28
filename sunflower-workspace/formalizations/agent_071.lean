import Mathlib

/-!
# Improved sunflower lemma — statement only

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke: the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`
for an absolute constant `C`.

This file contains the *statement* only; the theorem ends in `:= by sorry`.
-/

namespace Agent071

open scoped Real

/-- A finite family `T` of finsets is a **sunflower with core `Y`** if any two
*distinct* members of `T` intersect in exactly `Y`.

Consequences of this predicate (not part of the definition): every element lying in
at least two members of `T` lies in all of them, and the "petals" `s \ Y` for `s ∈ T`
are pairwise disjoint.

This mirrors what a `Finset.IsSunflower` predicate in Mathlib would express (see the
accompanying note about the exact Mathlib identifier). -/
def IsSunflower {α : Type*} [DecidableEq α] (T : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s : Finset α⦄, s ∈ T → ∀ ⦃t : Finset α⦄, t ∈ T → s ≠ t → s ∩ t = Y

/-- `W` **contains a sunflower with `r` petals** if some `r`-element subfamily `T ⊆ W`
is a sunflower for some core `Y`.

The `r` petals are automatically pairwise distinct because `T : Finset (Finset α)`, and
`T.card = r` pins down their number exactly. Petals are *not* required to be nonempty. -/
def HasSunflower {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ T : Finset (Finset α), T ⊆ W ∧ T.card = r ∧ ∃ Y : Finset α, IsSunflower T Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang 2019; refinements by Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`,
every finite family `W` of finsets, each of cardinality exactly `k`, with
`(C · r · log k)^k < |W|` contains a sunflower with `r` petals.

Equivalently: the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`.

Encoding notes:
* `log` is the natural logarithm `Real.log`; the choice of base is irrelevant, being
  absorbed into `C`.
* `C` is existentially quantified ("there is an absolute constant"), with `0 < C`.
* `C` is chosen once, *before* the ambient type `α`, so the constant is genuinely
  independent of `α`, `k`, `r`, and `W`.
* The hypothesis `2 ≤ k` sidesteps the degenerate range `k ∈ {0, 1}`, where
  `Real.log k = 0` makes the right-hand side collapse. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

end Agent071
