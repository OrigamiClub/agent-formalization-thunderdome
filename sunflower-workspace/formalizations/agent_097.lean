import Mathlib

open Finset

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the refinements of Rao and of
Bell–Chueluecha–Warnke.

This file contains only the *statement*.  Every theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- `IsSunflower P Y` says that the finite family of sets `P` is a *sunflower*
with *core* `Y`: any two distinct members of `P` intersect exactly in `Y`.

The petals are the sets `S \ Y` for `S ∈ P`.  From this condition the petals are
pairwise disjoint, and every element lying in at least two members of `P` lies in
`Y` (hence in every member of `P`). -/
def IsSunflower [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  (P : Set (Finset α)).Pairwise fun S T => S ∩ T = Y

/-- `HasSunflower W r` says that the family `W` contains a sunflower with exactly
`r` petals: an `r`-element subfamily of `W` that is a sunflower for some core.
Distinctness of the `r` petals is automatic, since `P` is a `Finset` with
`P.card = r`. -/
def HasSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao;
Bell–Chueluecha–Warnke).

There is an absolute constant `C` such that for every ambient type `α` with
decidable equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family
`W` of `k`-element subsets of `α` with more than `(C · r · log k) ^ k` members,
`W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Conventions:
* `Real.log` is the natural logarithm.  The hypothesis `2 ≤ k` keeps `log k`
  strictly positive; the excluded cases are trivial (`f (1, r) = r`,
  `f (0, r) ≤ 1`), and the base of the logarithm only affects the constant `C`.
* The cardinality bound is stated as a strict inequality of reals, with the
  natural-number `W.card` coerced into `ℝ`.
* `C` is existentially quantified *outside* the type `α` and the parameters
  `k`, `r`, expressing that it is genuinely absolute. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

end ImprovedSunflower
